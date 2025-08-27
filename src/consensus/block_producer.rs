// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Block production, leader-side of the consensus protocol.

use std::sync::Arc;
use std::time::{Duration, Instant};

use color_eyre::Result;
use either::Either;
use fastrace::Span;
use log::{debug, info, warn};
use static_assertions::const_assert;
use tokio::pin;
use tokio::sync::{RwLock, oneshot};
use tokio::time::sleep;
use tokio_util::sync::CancellationToken;

use crate::consensus::{Blockstore, EpochInfo, Pool};
use crate::crypto::{Hash, signature};
use crate::network::{Network, NetworkMessage};
use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
use crate::types::{Slice, SliceHeader, SliceIndex, SlicePayload, Slot};
use crate::{
    BlockId, Disseminator, MAX_TRANSACTION_SIZE, MAX_TRANSACTIONS_PER_SLICE, highest_non_zero_byte,
};

/// Produces blocks from transactions and dissminates them.
///
/// This is the leader's side of the consensus protocol.
/// Produces blocks in accordance with the consensus protocol's timeouts.
/// Receives transactions from clients via a [`Network`] instance and packs them into blocks.
/// Finished blocks are shredded and disseminated via a [`Disseminator`] instance.
pub(super) struct BlockProducer<D: Disseminator, T: Network> {
    /// Own validator's secret key (used e.g. for block production).
    /// This is not the same as the voting secret key, which is held by [`Votor`].
    secret_key: signature::SecretKey,
    /// Other validators' info.
    epoch_info: Arc<EpochInfo>,

    /// Blockstore for storing raw block data.
    blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
    /// Pool of votes and certificates.
    pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,

    /// Block dissemination network protocol for shreds.
    disseminator: Arc<D>,
    /// Network connection to receive transactions from clients.
    txs_receiver: T,

    /// Indicates whether the node is shutting down.
    cancel_token: CancellationToken,

    /// Should be set to `DELTA_BLOCK` in production.
    /// Stored as a field to aid in testing.
    delta_block: Duration,
    /// Should be set to `DELTA_FIRST_SLICE` in production.
    /// Stored as a field to aid in testing.
    delta_first_slice: Duration,
}

impl<D, T> BlockProducer<D, T>
where
    D: Disseminator + Sync + Send + 'static,
    T: Network + Sync + Send + 'static,
{
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        secret_key: signature::SecretKey,
        epoch_info: Arc<EpochInfo>,
        disseminator: Arc<D>,
        txs_receiver: T,
        blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
        pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,
        cancel_token: CancellationToken,
        delta_block: Duration,
        delta_first_slice: Duration,
    ) -> Self {
        assert!(delta_block >= delta_first_slice);
        Self {
            secret_key,
            epoch_info,
            blockstore,
            pool,
            disseminator,
            txs_receiver,
            cancel_token,
            delta_block,
            delta_first_slice,
        }
    }

    /// Handles the leader side of the consensus protocol.
    ///
    /// Once all previous blocks have been notarized or skipped and the next
    /// slot belongs to our leader window, we will produce a block.
    pub(super) async fn block_production_loop(&self) -> Result<()> {
        for first_slot_in_window in Slot::windows() {
            if self.cancel_token.is_cancelled() {
                break;
            }

            let last_slot_in_window = first_slot_in_window.last_slot_in_window();

            // don't do anything if we are not the leader
            let leader = self.epoch_info.leader(first_slot_in_window);
            if leader.id != self.epoch_info.own_id {
                debug!(
                    "[val {}] not producing in window {first_slot_in_window}..{last_slot_in_window}, not leader",
                    self.epoch_info.own_id
                );
                continue;
            }

            // wait for (a) ParentReady, OR (b) block in previous slot
            let slot_ready = wait_for_first_slot(
                self.pool.clone(),
                self.blockstore.clone(),
                first_slot_in_window,
            )
            .await;

            // produce first block
            let start = Instant::now();
            let mut block_id = match slot_ready {
                SlotReady::Skip => {
                    warn!(
                        "not producing in window {first_slot_in_window}..{last_slot_in_window}, saw later finalization"
                    );
                    continue;
                }
                SlotReady::Ready(parent) => {
                    if first_slot_in_window.is_genesis() {
                        // skip genesis
                        (first_slot_in_window, Hash::default())
                    } else {
                        self.produce_block_parent_ready(first_slot_in_window, parent)
                            .await?
                    }
                }
                SlotReady::ParentReadyNotSeen(parent, channel) => {
                    self.produce_block_parent_not_ready(first_slot_in_window, parent, channel)
                        .await?
                }
            };
            debug!(
                "produced block {} in {} ms",
                first_slot_in_window,
                start.elapsed().as_millis()
            );

            // produce remaining blocks
            for slot in first_slot_in_window.slots_in_window().skip(1) {
                let start = Instant::now();
                block_id = self.produce_block_parent_ready(slot, block_id).await?;
                debug!(
                    "produced block {} in {} ms",
                    slot,
                    start.elapsed().as_millis()
                );
            }
        }

        Ok(())
    }

    /// Produces a block in the situation where we have not yet seen the `ParentReady` event.
    ///
    /// The `parent_block_id` refers to the block of the previous slot which may end up not being the actualy parent of the block.
    pub(super) async fn produce_block_parent_not_ready(
        &self,
        slot: Slot,
        parent_block_id: BlockId,
        mut parent_ready_receiver: oneshot::Receiver<BlockId>,
    ) -> Result<BlockId> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = parent_block_id;
        assert_eq!(parent_slot, slot.prev());
        assert!(slot.is_start_of_window());
        info!(
            "optimistically producing block in slot {} with parent {} in slot {}",
            slot,
            &hex::encode(parent_hash)[..8],
            parent_slot,
        );

        // only start the DELTA_BLOCK timer later, when ParentReady event is seen
        let mut duration_left = Duration::MAX;
        for slice_index in SliceIndex::all() {
            let slice_parent = slice_index.is_first().then_some(parent_block_id);
            let time_for_slice = if slice_index.is_first() {
                // make sure first slice is produced quickly enough so that other nodes do not generate the `TimeoutCrashedLeader` event
                // TODO: this can be made more accurate, only needed if production of first slice
                // still takes more than delta_first_slice after we saw ParentReady, not if:
                // 1. first slice is produced before ParentReady is seen, OR
                // 2. first slice finishes at most delta_first_slice after ParentReady is seen
                self.delta_first_slice
            } else {
                // cap timeout for each slice to `DELTA_BLOCK`
                // makes sure optimistic block production yields before timeout would expire
                duration_left.min(self.delta_block)
            };
            let produce_slice_future =
                produce_slice_payload(&self.txs_receiver, slice_parent, time_for_slice);

            // If we have not yet received the ParentReady event, wait for it concurrently while producing the next slice.
            let (payload, new_duration_left) = if parent_ready_receiver.is_terminated() {
                let (payload, time_elapsed) = produce_slice_future.await;
                (payload, duration_left - time_elapsed)
            } else {
                pin!(produce_slice_future);
                tokio::select! {
                    res = &mut produce_slice_future => {
                        let (payload, _time_elapsed) = res;
                        // ParentReady event still not seen, do not start DELTA_BLOCK timer yet
                        (payload, Duration::MAX)
                    }
                    res = &mut parent_ready_receiver => {
                        // Got ParentReady event while producing slice.
                        // It's a NOP if we have been using the same parent as before.

                        let start = Instant::now();
                        let (new_slot, new_hash) = res.expect("sender dropped");
                        let (mut payload, _time_elapsed) = produce_slice_future.await;
                        if new_hash != parent_hash {
                            assert_ne!(new_slot, parent_slot);
                            debug!(
                                "changed parent from {} in slot {} to {} in slot {}",
                                &hex::encode(parent_hash)[..8],
                                parent_slot,
                                &hex::encode(new_hash)[..8],
                                new_slot
                            );
                            payload.parent = Some((new_slot, new_hash));
                        } else {
                            debug!("parent is ready, continuing with same parent");
                        }
                        // ParentReady was seen, start the DELTA_BLOCK timer
                        // account for the time it took to finish producing current slice
                        debug!("starting blocktime timer");
                        let time_left = self.delta_block.saturating_sub(start.elapsed());
                        (payload, time_left)
                    }
                }
            };

            let is_last = slice_index.is_max() || new_duration_left.is_zero();
            if is_last {
                assert!(parent_ready_receiver.is_terminated());
            }
            let header = SliceHeader::new(slot, slice_index, is_last);

            match self.shred_and_disseminate(header, payload).await? {
                Some(block_hash) => return Ok((slot, block_hash)),
                None => {
                    assert!(!new_duration_left.is_zero());
                    duration_left = new_duration_left;
                }
            }
        }
        unreachable!()
    }

    /// Produces a block in the situation where we have already seen the `ParentReady` event.
    ///
    /// The `parent_block_id` refers to the block that is the ready parent.
    pub(crate) async fn produce_block_parent_ready(
        &self,
        slot: Slot,
        parent_block_id: BlockId,
    ) -> Result<BlockId> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = parent_block_id;
        info!(
            "producing block in slot {} with ready parent {} in slot {}",
            slot,
            &hex::encode(parent_hash)[..8],
            parent_slot,
        );

        let mut duration_left = self.delta_block;
        for slice_index in SliceIndex::all() {
            let parent = slice_index.is_first().then_some(parent_block_id);
            let time_for_slice = if slice_index.is_first() {
                // make sure first slice is produced quickly enough so that other nodes do not generate the `TimeoutCrashedLeader` event
                self.delta_first_slice
            } else {
                duration_left
            };
            let (payload, time_elapsed) =
                produce_slice_payload(&self.txs_receiver, parent, time_for_slice).await;
            let new_duration_left = duration_left - time_elapsed;
            let is_last = slice_index.is_max() || new_duration_left.is_zero();
            let header = SliceHeader::new(slot, slice_index, is_last);

            // TODO: not accounting for this potentially expensive operation in duration_left calculation above.
            match self.shred_and_disseminate(header, payload).await? {
                Some(block_hash) => return Ok((slot, block_hash)),
                None => {
                    assert!(!new_duration_left.is_zero());
                    duration_left = new_duration_left;
                }
            }
        }
        unreachable!()
    }

    /// Shreds and disseminates the slice payload.
    ///
    /// Returns `Ok(Some(block_hash))` if this is the last slice, `Ok(None)` otherwise.
    ///
    /// # Errors
    ///
    /// Returns an error if sending via the [`Disseminator`] fails.
    async fn shred_and_disseminate(
        &self,
        header: SliceHeader,
        payload: SlicePayload,
    ) -> Result<Option<Hash>> {
        let slice = Slice::from_parts(header, payload, None);
        let slot = slice.slot;
        let is_last = slice.is_last;
        let shreds = RegularShredder::shred(slice, &self.secret_key)
            .expect("shredding of valid slice should never fail");
        let mut maybe_block_hash = None;
        for s in shreds {
            self.disseminator.send(&s).await?;
            // PERF: move expensive add_shred() call out of block production
            let block = self
                .blockstore
                .write()
                .await
                .add_shred_from_disseminator(s)
                .await;
            if let Ok(Some((block_slot, block_info))) = block {
                assert_eq!(block_slot, slot);
                assert!(maybe_block_hash.is_none());
                maybe_block_hash = Some(block_info.hash);
                let block_id = (block_slot, block_info.hash);
                self.pool
                    .write()
                    .await
                    .add_block(block_id, block_info.parent)
                    .await;
            }
        }
        assert_eq!(maybe_block_hash.is_some(), is_last);
        Ok(maybe_block_hash)
    }
}

/// Produces a slice (payload only).
///
/// Packs transactions received from the network into the slice until either:
/// - The slice is full (accounting for encoding of parent), OR
/// - `duration_left` time has elapsed.
///
/// Returns the slice payload and the amount of time left afterwards.
async fn produce_slice_payload<T>(
    txs_receiver: &T,
    parent: Option<BlockId>,
    duration_left: Duration,
) -> (SlicePayload, Duration)
where
    T: Network + Sync + Send + 'static,
{
    let start_time = Instant::now();
    const_assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE);

    let parent_encoded_len = bincode::serde::encode_to_vec(parent, bincode::config::standard())
        .unwrap()
        .len();

    // HACK: As long as the size of the txs vec fits in a single byte,
    // bincode encoding seems to take a single byte so account for that here.
    assert_eq!(highest_non_zero_byte(MAX_TRANSACTIONS_PER_SLICE), 1);
    let mut slice_capacity_left = MAX_DATA_PER_SLICE
        .checked_sub(parent_encoded_len)
        .unwrap()
        .checked_sub(1)
        .unwrap();
    let mut txs = Vec::new();

    let ret = loop {
        let sleep_duration = duration_left.saturating_sub(Instant::now() - start_time);
        let res = tokio::select! {
            () = tokio::time::sleep(sleep_duration) => {
                break duration_left;
            }
            res = txs_receiver.receive() => {
                res
            }
        };
        match res.expect("unexpected error") {
            NetworkMessage::Transaction(tx) => {
                let tx = bincode::serde::encode_to_vec(&tx, bincode::config::standard())
                    .expect("serialization should not panic");
                slice_capacity_left = slice_capacity_left.checked_sub(tx.len()).unwrap();
                txs.push(tx);
            }
            msg => {
                panic!("unexpected msg: {msg:?}");
            }
        }
        if slice_capacity_left < MAX_TRANSACTION_SIZE {
            break Duration::ZERO;
        }
    };

    // TODO: not accounting for this potentially expensive operation in duration_left calculation above.
    let txs = bincode::serde::encode_to_vec(&txs, bincode::config::standard())
        .expect("serialization should not panic");
    let payload = SlicePayload::new(parent, txs);
    let time_elapsed = start_time.elapsed().max(ret);
    (payload, time_elapsed.min(duration_left))
}

/// Enum to capture the different scenarios that can be returned from [`wait_for_first_slot`].
#[derive(Debug)]
enum SlotReady {
    /// Window was already skipped.
    Skip,
    /// Slot is ready and the Pool emitted a `ParentReady` for given `BlockId`.
    Ready(BlockId),
    /// Slot is ready as a block for the previous slot was seen but the Pool has not emitted `ParentReady` yet.
    ParentReadyNotSeen(BlockId, oneshot::Receiver<BlockId>),
}

/// Waits for first slot in the given window to become ready for block production.
///
/// Ready here can mean:
/// - Pool emitted the `ParentReady` event for it, OR
/// - the blockstore has stored a block for the previous slot.
///
/// See [`SlotReady`] for what is returned.
async fn wait_for_first_slot(
    pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,
    blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
    first_slot_in_window: Slot,
) -> SlotReady {
    assert!(first_slot_in_window.is_start_of_window());
    if first_slot_in_window.is_genesis_window() {
        return SlotReady::Ready((Slot::genesis(), Hash::default()));
    }

    // if already have parent ready, return it, otherwise get a channel to await on
    let mut rx = {
        let mut guard = pool.write().await;
        match guard.wait_for_parent_ready(first_slot_in_window) {
            Either::Left(parent) => {
                return SlotReady::Ready(parent);
            }
            Either::Right(rx) => rx,
        }
    };

    // Concurrently wait for:
    // - `ParentReady` event,
    // - block reconstruction in blockstore, OR
    // - notification that a later slot was finalized.
    tokio::select! {
        res = &mut rx => {
            let parent = res.expect("sender dropped channel");
            SlotReady::Ready(parent)
        }

        res = async {
            let handle = tokio::spawn(async move {
                // PERF: These are burning a CPU. Can we use async here?
                loop {
                    let last_slot_in_prev_window = first_slot_in_window.prev();
                    if let Some(hash) = blockstore.read().await
                        .canonical_block_hash(last_slot_in_prev_window)
                    {
                        return Some((last_slot_in_prev_window, hash));
                    }
                    if pool.read().await.finalized_slot() >= first_slot_in_window {
                        return None;
                    }
                    sleep(Duration::from_millis(1)).await;
                }
            });
            handle.await.expect("error in task")
        } => {
            match res {
                None => SlotReady::Skip,
                Some((slot, hash)) => SlotReady::ParentReadyNotSeen((slot, hash), rx),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use mockall::{Sequence, predicate};

    use super::*;
    use crate::Transaction;
    use crate::consensus::BlockInfo;
    use crate::consensus::blockstore::MockBlockstore;
    use crate::consensus::pool::MockPool;
    use crate::crypto::Hash;
    use crate::disseminator::MockDisseminator;
    use crate::network::UdpNetwork;
    use crate::shredder::TOTAL_SHREDS;
    use crate::test_utils::generate_validators;

    #[tokio::test]
    async fn produce_slice_empty_slices() {
        let txs_receiver = UdpNetwork::new_with_any_port();
        let duration_left = Duration::from_micros(0);

        let parent = None;
        let (payload, time_elapsed) =
            produce_slice_payload(&txs_receiver, parent, duration_left).await;
        assert_eq!(time_elapsed, duration_left);
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 1 byte
        assert_eq!(payload.data.len(), 1);

        let parent = Some((Slot::genesis(), Hash::default()));
        let (payload, time_elapsed) =
            produce_slice_payload(&txs_receiver, parent, duration_left).await;
        assert_eq!(time_elapsed, duration_left);
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 1 byte
        assert_eq!(payload.data.len(), 1);
    }

    #[tokio::test]
    async fn produce_slice_full_slices() {
        let txs_receiver = UdpNetwork::new_with_any_port();
        let addr = format!("127.0.0.1:{}", txs_receiver.port());
        let txs_sender = UdpNetwork::new_with_any_port();
        // long enough duration so hopefully doesn't fire while collecting txs
        let duration_left = Duration::from_secs(100);

        tokio::spawn(async move {
            for i in 0..255 {
                let data = vec![i; MAX_TRANSACTION_SIZE];
                let msg = NetworkMessage::Transaction(Transaction(data));
                txs_sender.send(&msg, addr.clone()).await.unwrap();
            }
        });

        let parent = None;
        let (payload, time_elapsed) =
            produce_slice_payload(&txs_receiver, parent, duration_left).await;
        assert!(time_elapsed < duration_left);
        assert_eq!(payload.parent, parent);
        assert!(payload.data.len() <= MAX_DATA_PER_SLICE);
        assert!(payload.data.len() > MAX_DATA_PER_SLICE - MAX_TRANSACTION_SIZE);
    }

    #[tokio::test]
    async fn wait_for_first_slot_genesis() {
        let pool: Box<dyn Pool + Send + Sync> = Box::new(MockPool::new());
        let pool = Arc::new(RwLock::new(pool));
        let blockstore: Box<dyn Blockstore + Send + Sync> = Box::new(MockBlockstore::new());
        let blockstore = Arc::new(RwLock::new(blockstore));

        let status = wait_for_first_slot(pool, blockstore, Slot::genesis()).await;
        assert!(matches!(status, SlotReady::Ready(_)));
    }

    #[tokio::test]
    async fn wait_for_first_slot_parent_already_ready() {
        let blockstore: Box<dyn Blockstore + Send + Sync> = Box::new(MockBlockstore::new());
        let blockstore = Arc::new(RwLock::new(blockstore));

        let slot = Slot::windows().nth(10).unwrap();
        let parent = (slot.prev(), Hash::default());

        let mut pool = MockPool::new();
        pool.expect_wait_for_parent_ready()
            .with(predicate::eq(slot))
            .return_once(move |_slot| Either::Left(parent));
        let pool: Box<dyn Pool + Send + Sync> = Box::new(pool);
        let pool = Arc::new(RwLock::new(pool));

        let status = wait_for_first_slot(pool, blockstore, slot).await;
        match status {
            SlotReady::Ready(p) => assert_eq!(p, parent),
            other => panic!("unexpected {other:?}"),
        }
    }

    #[tokio::test]
    async fn wait_for_first_slot_parent_ready_later() {
        let blockstore: Box<dyn Blockstore + Send + Sync> = Box::new(MockBlockstore::new());
        let blockstore = Arc::new(RwLock::new(blockstore));

        let slot = Slot::windows().nth(10).unwrap();
        let parent = (slot.prev(), Hash::default());
        let (tx, rx) = oneshot::channel();
        tx.send(parent).unwrap();

        let mut pool = MockPool::new();
        pool.expect_wait_for_parent_ready()
            .with(predicate::eq(slot))
            .return_once(move |_slot| Either::Right(rx));
        let pool: Box<dyn Pool + Send + Sync> = Box::new(pool);
        let pool = Arc::new(RwLock::new(pool));

        let status = wait_for_first_slot(pool, blockstore, slot).await;
        match status {
            SlotReady::Ready(p) => assert_eq!(p, parent),
            other => panic!("unexpected {other:?}"),
        }
    }

    /// A bunch of boilerplate to initialize and return a [`BlockProducer`].
    fn setup(
        blockstore: MockBlockstore,
        pool: MockPool,
        disseminator: MockDisseminator,
        delta_block: Duration,
        delta_first_slice: Duration,
    ) -> BlockProducer<MockDisseminator, UdpNetwork> {
        let secret_key = signature::SecretKey::new(&mut rand::rng());
        let (_, epoch_info) = generate_validators(11);
        let blockstore: Box<dyn Blockstore + Send + Sync> = Box::new(blockstore);
        let blockstore = Arc::new(RwLock::new(blockstore));
        let pool: Box<dyn Pool + Send + Sync> = Box::new(pool);
        let pool = Arc::new(RwLock::new(pool));
        let disseminator = Arc::new(disseminator);
        let txs_receiver = UdpNetwork::new_with_any_port();
        let cancel_token = CancellationToken::new();

        BlockProducer::new(
            secret_key,
            epoch_info,
            disseminator,
            txs_receiver,
            blockstore,
            pool,
            cancel_token,
            delta_block,
            delta_first_slice,
        )
    }

    #[tokio::test]
    async fn verify_produce_block_parent_ready() {
        let slot = Slot::windows().nth(10).unwrap();
        let block_info = BlockInfo {
            hash: [1; 32],
            parent: (slot.prev(), [2; 32]),
        };

        // Handles TOTAL_SHRED number of calls.
        // The first TOTAL_SHRED - 1 calls return None.
        // The last call returns Some.
        let mut seq = Sequence::new();
        let mut blockstore = MockBlockstore::new();
        blockstore
            .expect_add_shred_from_disseminator()
            .times(TOTAL_SHREDS - 1)
            .in_sequence(&mut seq)
            .returning(move |_| Box::pin(async move { Ok(None) }));
        blockstore
            .expect_add_shred_from_disseminator()
            .times(1)
            .in_sequence(&mut seq)
            .returning(move |_| Box::pin(async move { Ok(Some((slot, block_info))) }));

        let mut pool = MockPool::new();
        pool.expect_add_block()
            .returning(move |ret_block_id, ret_parent_block_id| {
                assert_eq!(ret_block_id, (slot, block_info.hash));
                assert_eq!(block_info.parent, ret_parent_block_id);
                Box::pin(async {})
            });

        let mut disseminator = MockDisseminator::new();
        disseminator
            .expect_send()
            .returning(|_| Box::pin(async { Ok(()) }));
        let block_producer = setup(
            blockstore,
            pool,
            disseminator,
            Duration::from_micros(0),
            Duration::from_micros(0),
        );

        let ret = block_producer
            .produce_block_parent_ready(slot, block_info.parent)
            .await
            .unwrap();
        assert_eq!(slot, ret.0);
        assert_eq!(block_info.hash, ret.1);
    }

    #[tokio::test]
    async fn verify_produce_block_parent_not_ready() {
        let slot = Slot::windows().nth(10).unwrap();
        let slot_hash = [1; 32];
        let old_parent = (slot.prev(), [2; 32]);
        let new_parent = (slot.prev().prev(), [3; 32]);
        let old_block_info = BlockInfo {
            hash: slot_hash,
            parent: old_parent,
        };
        let new_block_info = BlockInfo {
            hash: slot_hash,
            parent: new_parent,
        };

        let (first_slice_finished_tx, first_slice_finished_rx) = oneshot::channel();
        let (start_second_slice_tx, start_second_slice_rx) = oneshot::channel();

        let mut seq = Sequence::new();
        let mut blockstore = MockBlockstore::new();

        // handle first slice
        blockstore
            .expect_add_shred_from_disseminator()
            .times(TOTAL_SHREDS - 1)
            .in_sequence(&mut seq)
            .returning(move |_| Box::pin(async move { Ok(None) }));
        blockstore
            .expect_add_shred_from_disseminator()
            .times(1)
            .in_sequence(&mut seq)
            .return_once(move |_| {
                Box::pin(async move {
                    // last shred; wait for the parent ready event to be sent before continuing
                    first_slice_finished_tx.send(()).unwrap();
                    let () = start_second_slice_rx.await.unwrap();
                    Ok(None)
                })
            });

        // handle second slice
        blockstore
            .expect_add_shred_from_disseminator()
            .times(TOTAL_SHREDS - 1)
            .in_sequence(&mut seq)
            .returning(move |_| Box::pin(async move { Ok(None) }));
        blockstore
            .expect_add_shred_from_disseminator()
            .times(1)
            .in_sequence(&mut seq)
            .returning(move |_| {
                Box::pin(async move {
                    // final shred of second slice
                    // block is constructed with the new parent
                    Ok(Some((slot, new_block_info)))
                })
            });

        let mut pool = MockPool::new();
        pool.expect_add_block()
            .returning(move |ret_block_id, ret_parent_block_id| {
                assert_eq!(ret_block_id, (slot, new_block_info.hash));
                assert_eq!(new_block_info.parent, ret_parent_block_id);
                Box::pin(async {})
            });

        let mut disseminator = MockDisseminator::new();
        disseminator
            .expect_send()
            .returning(|_| Box::pin(async { Ok(()) }));
        let block_producer = setup(
            blockstore,
            pool,
            disseminator,
            Duration::from_micros(0),
            Duration::from_millis(0),
        );

        let (parent_ready_tx, parent_ready_rx) = oneshot::channel();

        tokio::spawn(async move {
            let () = first_slice_finished_rx.await.unwrap();
            parent_ready_tx.send(new_parent).unwrap();
            start_second_slice_tx.send(()).unwrap();
        });

        let ret = block_producer
            .produce_block_parent_not_ready(slot, old_block_info.parent, parent_ready_rx)
            .await
            .unwrap();

        assert_eq!(slot, ret.0);
        assert_eq!(new_block_info.hash, ret.1);
        assert_eq!(new_block_info.parent, new_parent);
    }
}
