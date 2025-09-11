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
use crate::types::slice_index::MAX_SLICES_PER_BLOCK;
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
    D: Disseminator,
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
            let (mut block_id, num_txs) = match slot_ready {
                SlotReady::Skip => {
                    warn!(
                        "not producing in window {first_slot_in_window}..{last_slot_in_window}, saw later finalization"
                    );
                    continue;
                }
                SlotReady::Ready(parent) => {
                    if first_slot_in_window.is_genesis() {
                        // skip genesis
                        ((first_slot_in_window, Hash::default()), 0)
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
            info!(
                "produced first block in window {} ({} txs) in {} ms",
                first_slot_in_window,
                num_txs,
                start.elapsed().as_millis()
            );

            // produce remaining blocks
            for slot in first_slot_in_window.slots_in_window().skip(1) {
                let start = Instant::now();
                let (new_block_id, num_txs) =
                    self.produce_block_parent_ready(slot, block_id).await?;
                block_id = new_block_id;
                info!(
                    "produced block {} ({} txs) in {} ms",
                    slot,
                    num_txs,
                    start.elapsed().as_millis()
                );
            }
        }

        Ok(())
    }

    /// Produces a block in the situation where we have not yet seen the `ParentReady` event.
    ///
    /// The `parent` refers to the block of the previous slot which may end up not being the actualy parent of the block.
    ///
    /// Returns the block ID of the produced block and the number of transactions in the block.
    pub(super) async fn produce_block_parent_not_ready(
        &self,
        slot: Slot,
        parent: BlockId,
        mut parent_ready_receiver: oneshot::Receiver<BlockId>,
    ) -> Result<(BlockId, usize)> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = parent;
        assert_eq!(parent_slot, slot.prev());
        assert!(slot.is_start_of_window());
        info!(
            "optimistically producing block in slot {} with parent {} in slot {}",
            slot,
            &hex::encode(parent_hash)[..8],
            parent_slot,
        );

        let (block_hash, num_txs) = self
            .produce_slices(slot, parent, Some(&mut parent_ready_receiver))
            .await?;
        Ok(((slot, block_hash), num_txs))
    }

    /// Produces a block in the situation where we have already seen the `ParentReady` event.
    ///
    /// The `parent` refers to the block that is the ready parent.
    ///
    /// Returns the block ID of the produced block and the number of transactions in the block.
    pub(crate) async fn produce_block_parent_ready(
        &self,
        slot: Slot,
        parent: BlockId,
    ) -> Result<(BlockId, usize)> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = parent;
        info!(
            "producing block in slot {} with ready parent {} in slot {}",
            slot,
            &hex::encode(parent_hash)[..8],
            parent_slot,
        );

        let (block_hash, num_txs) = self.produce_slices(slot, parent, None).await?;
        Ok(((slot, block_hash), num_txs))
    }

    async fn produce_slices(
        &self,
        slot: Slot,
        parent: BlockId,
        mut parent_ready_receiver: Option<&mut oneshot::Receiver<BlockId>>,
    ) -> Result<(Hash, usize)> {
        // only start the DELTA_BLOCK timer when ParentReady event is seen
        let mut duration_left = match parent_ready_receiver {
            None => self.delta_block,
            Some(_) => Duration::MAX,
        };
        let mut txs_in_block = 0;

        for slice_index in SliceIndex::all() {
            let slice_parent = slice_index.is_first().then_some(parent);
            // HACK: use of `MAX_SLICES_PER_BLOCK / 2`, maybe introduce `MAX_SLICES_FIRST_SLOT`
            // HACK: use of `SliceIndex::inner()`, maybe introduce `is_last_before_parent_ready()`
            let min_time_for_slice = if parent_ready_receiver.is_some()
                && slice_index.inner() == MAX_SLICES_PER_BLOCK / 2
            {
                Duration::MAX
            } else {
                Duration::ZERO
            };
            let (preempt_sender, preempt_receiver) = oneshot::channel();
            let produce_slice_future = produce_slice_payload(
                &self.txs_receiver,
                slice_parent,
                min_time_for_slice,
                preempt_receiver,
            );
            pin!(produce_slice_future);

            let (payload, new_duration_left, txs_in_slice) =
                if let Some(ref mut parent_rcv) = parent_ready_receiver {
                    // if we have not yet received the ParentReady event,
                    // wait for it concurrently while producing the next slice
                    tokio::select! {
                        res = &mut produce_slice_future => {
                            let (payload, _time_elapsed, txs_in_slice) = res;
                            // ParentReady event still not seen, do not start DELTA_BLOCK timer yet
                            (payload, Duration::MAX, txs_in_slice)
                        }
                        res = parent_rcv => {
                            parent_ready_receiver = None;
                            // Got ParentReady event while producing slice.
                            // It's a NOP if we have been using the same parent as before.
                            let start = Instant::now();
                            let (new_slot, new_hash) = res.expect("sender dropped");
                            let (payload, _time_elapsed, txs_in_slice) = tokio::select! {
                                () = tokio::time::sleep(self.delta_first_slice) => {
                                    preempt_sender.send(()).unwrap();
                                    produce_slice_future.await
                                }
                                res = &mut produce_slice_future => res,
                            };
                            let (parent_slot, parent_hash) = parent;
                            if new_hash != parent_hash {
                                assert_ne!(new_slot, parent_slot);
                                debug!(
                                    "changed parent from {} in slot {} to {} in slot {}",
                                    &hex::encode(parent_hash)[..8],
                                    parent_slot,
                                    &hex::encode(new_hash)[..8],
                                    new_slot
                                );
                            } else {
                                debug!("parent is ready, continuing with same parent");
                            }
                            // ParentReady was seen, start the DELTA_BLOCK timer
                            // account for the time it took to finish producing current slice
                            debug!("starting blocktime timer");
                            let time_left = self.delta_block.saturating_sub(start.elapsed());
                            (payload, time_left, txs_in_slice)
                        }
                    }
                } else {
                    // after we saw ParentReady event, simply produce slices with timeout
                    tokio::select! {
                        () = tokio::time::sleep(duration_left) => {
                            // timeout expired, preempt slice production
                            preempt_sender.send(()).unwrap();
                            let (payload, _, txs_in_slice) = produce_slice_future.await;
                            (payload, Duration::ZERO, txs_in_slice)
                        }
                        (payload, time_elapsed, txs_in_slice) = &mut produce_slice_future => {
                            (payload, duration_left.saturating_sub(time_elapsed), txs_in_slice)
                        }
                    }
                };

            txs_in_block += txs_in_slice;

            let is_last = slice_index.is_max() || new_duration_left.is_zero();
            if let Some(ref parent_rcv) = parent_ready_receiver
                && is_last
            {
                assert!(parent_rcv.is_terminated());
            }
            let header = SliceHeader::new(slot, slice_index, is_last);

            let start = Instant::now();
            let maybe_block_hash = self.shred_and_disseminate(header, payload).await?;

            match maybe_block_hash {
                Some(block_hash) => return Ok((block_hash, txs_in_block)),
                None => {
                    assert!(!new_duration_left.is_zero());
                    duration_left = new_duration_left.saturating_sub(start.elapsed());
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
/// - there is an incoming message on the `preempt_receiver`.
///
/// Returns the slice payload, amount of time elapsed, and number of transactions packed.
async fn produce_slice_payload<T>(
    txs_receiver: &T,
    parent: Option<BlockId>,
    min_duration: Duration,
    mut preempt_receiver: oneshot::Receiver<()>,
) -> (SlicePayload, Duration, usize)
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

    loop {
        let res = tokio::select! {
            res = &mut preempt_receiver => {
                let () = res.expect("sender dropped");
                break;
            }
            res = txs_receiver.receive() => res,
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
            break;
        }
    }

    let num_txs = txs.len();
    let txs = bincode::serde::encode_to_vec(&txs, bincode::config::standard())
        .expect("serialization should not panic");
    let payload = SlicePayload::new(parent, txs);

    // idle if necessary
    // TODO: instead actually spend more time waiting for and selecting transactions
    if start_time.elapsed() < min_duration && !preempt_receiver.is_terminated() {
        tokio::select! {
            res = &mut preempt_receiver => res.expect("sender dropped"),
            () = tokio::time::sleep(min_duration - start_time.elapsed()) => {}
        }
    }

    debug!(
        "produced slice with {} txs in {}ms",
        num_txs,
        start_time.elapsed().as_millis()
    );

    (payload, start_time.elapsed(), num_txs)
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
                        .disseminated_block_hash(last_slot_in_prev_window)
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
    use crate::network::{UdpNetwork, localhost_ip_sockaddr};
    use crate::shredder::TOTAL_SHREDS;
    use crate::test_utils::generate_validators;

    #[tokio::test]
    async fn produce_slice_empty_slices() {
        let txs_receiver = UdpNetwork::new_with_any_port();

        let (preempt_sender, preempt_receiver) = oneshot::channel();
        preempt_sender.send(()).unwrap();
        let parent = None;
        let (payload, _, num_txs) =
            produce_slice_payload(&txs_receiver, parent, Duration::ZERO, preempt_receiver).await;
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 1 byte
        assert_eq!(payload.data.len(), 1);
        assert_eq!(num_txs, 0);

        let (preempt_sender, preempt_receiver) = oneshot::channel();
        preempt_sender.send(()).unwrap();
        let parent = Some((Slot::genesis(), Hash::default()));
        let (payload, _, num_txs) =
            produce_slice_payload(&txs_receiver, parent, Duration::ZERO, preempt_receiver).await;
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 1 byte
        assert_eq!(payload.data.len(), 1);
        assert_eq!(num_txs, 0);
    }

    #[tokio::test]
    async fn produce_slice_full_slices() {
        let txs_receiver = UdpNetwork::new_with_any_port();
        let addr = localhost_ip_sockaddr(txs_receiver.port());
        let txs_sender = UdpNetwork::new_with_any_port();
        // do not preempt slice
        let (_preempt_sender, preempt_receiver) = oneshot::channel();

        tokio::spawn(async move {
            for i in 0..255 {
                let data = vec![i; MAX_TRANSACTION_SIZE];
                let msg = NetworkMessage::Transaction(Transaction(data));
                txs_sender.send(&msg, addr).await.unwrap();
            }
        });

        let parent = None;
        let (payload, _, num_txs) =
            produce_slice_payload(&txs_receiver, parent, Duration::ZERO, preempt_receiver).await;
        assert_eq!(payload.parent, parent);
        assert!(payload.data.len() <= MAX_DATA_PER_SLICE);
        assert!(payload.data.len() > MAX_DATA_PER_SLICE - MAX_TRANSACTION_SIZE);
        assert!(num_txs > 0);
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

        let (block_id, num_txs) = block_producer
            .produce_block_parent_ready(slot, block_info.parent)
            .await
            .unwrap();
        assert_eq!(slot, block_id.0);
        assert_eq!(block_info.hash, block_id.1);
        assert_eq!(num_txs, 0);
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

        let (parent_ready_tx, parent_ready_rx) = oneshot::channel();

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
                    // last shred; send ParentReady event before continuing
                    parent_ready_tx.send(new_parent).unwrap();
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

        let port = block_producer.txs_receiver.port();
        let txs_sender = UdpNetwork::new_with_any_port();
        for _ in 0..MAX_TRANSACTIONS_PER_SLICE {
            txs_sender
                .send(
                    &NetworkMessage::Transaction(Transaction(vec![1u8; MAX_TRANSACTION_SIZE])),
                    localhost_ip_sockaddr(port),
                )
                .await
                .unwrap();
        }

        let (block_id, num_txs) = block_producer
            .produce_block_parent_not_ready(slot, old_block_info.parent, parent_ready_rx)
            .await
            .unwrap();

        assert_eq!(slot, block_id.0);
        assert_eq!(new_block_info.hash, block_id.1);
        assert_eq!(new_block_info.parent, new_parent);
        assert!(num_txs > 0);
    }
}
