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
use wincode::config::DefaultConfig;

use crate::consensus::{Blockstore, Pool, ValidatorEpochInfo};
use crate::crypto::merkle::{BlockHash, GENESIS_BLOCK_HASH, MerkleRoot};
use crate::crypto::signature;
use crate::network::{Network, TransactionNetwork};
use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
use crate::types::{Slice, SliceHeader, SliceIndex, SlicePayload, Slot};
use crate::{BlockId, Disseminator, MAX_TRANSACTION_SIZE};

/// Produces blocks from transactions and disseminates them.
///
/// This is the leader's side of the consensus protocol.
/// Produces blocks in accordance with the consensus protocol's timeouts.
/// Receives transactions from clients via a [`Network`] instance and packs them into blocks.
/// Finished blocks are shredded and disseminated via a [`Disseminator`] instance.
pub(super) struct BlockProducer<D: Disseminator, T: Network> {
    /// Own validator's secret key (used e.g. for block production).
    /// This is not the same as the voting secret key, which is held by [`super::Votor`].
    secret_key: signature::SecretKey,
    /// Other validators' info.
    epoch_info: Arc<ValidatorEpochInfo>,

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

    /// Should be set to [`super::DELTA_BLOCK`] in production.
    /// Stored as a field to aid in testing.
    delta_block: Duration,
    /// Should be set to [`super::DELTA_FIRST_SLICE`] in production.
    /// Stored as a field to aid in testing.
    delta_first_slice: Duration,
}

impl<D, T> BlockProducer<D, T>
where
    D: Disseminator,
    T: TransactionNetwork,
{
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        secret_key: signature::SecretKey,
        epoch_info: Arc<ValidatorEpochInfo>,
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
            let leader = self.epoch_info.epoch_info().leader(first_slot_in_window);
            if leader.id != self.epoch_info.own_id() {
                debug!(
                    "[val {}] not producing in window {first_slot_in_window}..{last_slot_in_window}, not leader",
                    self.epoch_info.own_id()
                );
                continue;
            }

            // genesis block is already produced
            if first_slot_in_window.is_genesis() {
                continue;
            }

            // wait for ParentReady or block in previous slot
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
                    self.produce_block(first_slot_in_window, parent, None).await?
                }
                SlotReady::ParentReadyNotSeen(parent, rx) => {
                    self.produce_block(first_slot_in_window, parent, Some(rx)).await?
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
                block_id = self.produce_block(slot, block_id, None).await?;
                debug!(
                    "produced block {} in {} ms",
                    slot,
                    start.elapsed().as_millis()
                );
            }
        }

        Ok(())
    }

    /// Produces a block for the given slot.
    ///
    /// When `parent_ready_rx` is `None`, the parent is already known and the DELTA_BLOCK timer
    /// starts immediately. When `Some`, block production begins optimistically while racing
    /// slice production against the `ParentReady` event; the timer starts upon receipt.
    #[hotpath::measure]
    async fn produce_block(
        &self,
        slot: Slot,
        parent_block_id: BlockId,
        mut parent_ready_rx: Option<oneshot::Receiver<BlockId>>,
    ) -> Result<BlockId> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = &parent_block_id;
        if parent_ready_rx.is_some() {
            assert_eq!(*parent_slot, slot.prev());
            assert!(slot.is_start_of_window());
            info!(
                "optimistically producing block in slot {} with parent {} in slot {}",
                slot,
                &hex::encode(parent_hash.as_hash())[..8],
                *parent_slot,
            );
        } else {
            info!(
                "producing block in slot {} with ready parent {} in slot {}",
                slot,
                &hex::encode(parent_hash.as_hash())[..8],
                parent_slot,
            );
        }

        // DELTA_BLOCK timer starts immediately when the parent is known; otherwise
        // it starts upon receipt of the ParentReady event.
        let mut duration_left = if parent_ready_rx.is_none() {
            self.delta_block
        } else {
            Duration::MAX
        };

        for slice_index in SliceIndex::all() {
            // Proactively wait for ParentReady before the last slice, giving it the full
            // DELTA_BLOCK window rather than producing it speculatively and then blocking.
            let mut parent_correction: Option<BlockId> = None;
            if slice_index.is_max()
                && let Some(rx) = parent_ready_rx.as_mut().filter(|rx| !rx.is_terminated())
            {
                parent_correction = apply_parent_update(&parent_block_id, rx.await.unwrap());
                debug!("starting blocktime timer");
                duration_left = self.delta_block;
            }

            let parent = if slice_index.is_first() {
                Some(
                    parent_correction
                        .take()
                        .unwrap_or_else(|| parent_block_id.clone()),
                )
            } else {
                parent_correction.take()
            };

            let time_for_slice = duration_left.min(if slice_index.is_first() {
                self.delta_first_slice
            } else {
                self.delta_block
            });

            let is_waiting = parent_ready_rx.as_ref().is_some_and(|rx| !rx.is_terminated());

            let produce_future = produce_slice_payload(&self.txs_receiver, parent, time_for_slice);

            let (payload, new_duration_left) = if is_waiting {
                let rx = parent_ready_rx.as_mut().unwrap();
                pin!(produce_future);
                tokio::select! {
                    res = &mut produce_future => {
                        let (payload, _) = res;
                        // ParentReady not yet seen; do not start DELTA_BLOCK timer yet
                        (payload, Duration::MAX)
                    }
                    res = rx => {
                        // Got ParentReady while producing this slice; start the timer,
                        // accounting for the time needed to finish the current slice.
                        let start = Instant::now();
                        let (mut payload, _) = produce_future.await;
                        if let Some(new) = apply_parent_update(&parent_block_id, res.unwrap()) {
                            payload.parent = Some(new);
                        }
                        debug!("starting blocktime timer");
                        (payload, self.delta_block.saturating_sub(start.elapsed()))
                    }
                }
            } else {
                let (payload, remaining) = produce_future.await;
                // When the parent was known from the start, deduct the first slice's elapsed
                // time from the DELTA_BLOCK budget (timer runs from the very beginning).
                let new_dl = if parent_ready_rx.is_none() && slice_index.is_first() {
                    let elapsed = time_for_slice.saturating_sub(remaining);
                    duration_left.saturating_sub(elapsed)
                } else {
                    remaining
                };
                (payload, new_dl)
            };

            let is_last = slice_index.is_max() || new_duration_left.is_zero();
            let header = SliceHeader {
                slot,
                slice_index,
                is_last,
            };

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
    /// Returns `Ok(Some(hash))` for the last slice of a block, `Ok(None)` otherwise.
    #[hotpath::measure]
    async fn shred_and_disseminate(
        &self,
        header: SliceHeader,
        payload: SlicePayload,
    ) -> Result<Option<BlockHash>> {
        let slot = header.slot;
        let is_last = header.is_last;
        let slice = Slice::from_parts(header, payload);
        let mut maybe_block_hash = None;
        // PERF: new shredder every time!
        let shreds = RegularShredder::default()
            .shred(slice, &self.secret_key)
            .expect("shredding of valid slice should never fail");
        for s in shreds {
            self.disseminator.send(&s).await?;
            // PERF: move expensive add_shred() call out of block production
            let block = self
                .blockstore
                .write()
                .await
                .add_own_shred_as_leader(s)
                .await;
            if let Ok(Some(block_info)) = block {
                assert!(maybe_block_hash.is_none());
                maybe_block_hash = Some(block_info.hash.clone());
                let block_id = (slot, block_info.hash.clone());
                self.pool
                    .write()
                    .await
                    .add_block(block_id, block_info.parent)
                    .await;
            }
        }
        if is_last {
            Ok(Some(maybe_block_hash.unwrap()))
        } else {
            assert!(maybe_block_hash.is_none());
            Ok(None)
        }
    }
}

/// Logs and returns the new `BlockId` iff the `ParentReady` event changed the parent.
///
/// Returns `None` when the parent is unchanged (caller should keep using the existing one).
fn apply_parent_update(old: &BlockId, new: BlockId) -> Option<BlockId> {
    let (old_slot, old_hash) = old;
    let (new_slot, new_hash) = &new;
    if new_hash != old_hash {
        assert_ne!(new_slot, old_slot);
        debug!(
            "changed parent from {} in slot {} to {} in slot {}",
            &hex::encode(old_hash.as_hash())[..8],
            old_slot,
            &hex::encode(new_hash.as_hash())[..8],
            new_slot,
        );
        Some(new)
    } else {
        debug!("parent is ready, continuing with same parent");
        None
    }
}

/// Collects transactions into a slice payload, waiting up to `duration_left` for more.
///
/// Returns the completed payload and the remaining time in `duration_left` after the slice
/// was filled (zero if the timeout expired before the slice was full).
async fn produce_slice_payload<T>(
    txs_receiver: &T,
    parent: Option<BlockId>,
    duration_left: Duration,
) -> (SlicePayload, Duration)
where
    T: TransactionNetwork,
{
    let start_time = Instant::now();

    // each slice should be able hold at least 1 transaction
    // need 8 bytes to encode number of txs + 8 bytes to encode the length of the tx payload
    const_assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE + 8 + 8);

    // reserve space for parent and 8 bytes to encode number of txs
    let parent_encoded_len =
        <Option<BlockId> as wincode::SchemaWrite<DefaultConfig>>::size_of(&parent).unwrap();
    let mut slice_capacity_left = MAX_DATA_PER_SLICE
        .checked_sub(parent_encoded_len + 8)
        .unwrap();
    let mut txs = Vec::new();

    let ret = loop {
        let sleep_duration = duration_left.saturating_sub(start_time.elapsed());
        let res = tokio::select! {
            () = tokio::time::sleep(sleep_duration) => {
                break Duration::ZERO;
            }
            res = txs_receiver.receive() => {
                res
            }
        };
        let tx = res.expect("receiving tx");
        let tx = wincode::serialize(&tx).expect("serialization should not panic");
        slice_capacity_left = slice_capacity_left.checked_sub(tx.len()).unwrap();
        txs.push(tx);

        // if there is not enough space for another tx, break
        // this needs to account for the 8 bytes to encode the length of the tx payload
        if slice_capacity_left < MAX_TRANSACTION_SIZE + 8 {
            break duration_left.saturating_sub(start_time.elapsed());
        }
    };

    // TODO: not accounting for this potentially expensive operation in duration_left calculation above.
    let txs = wincode::serialize(&txs).expect("serialization should not panic");
    let payload = SlicePayload::new(parent, txs);
    (payload, ret)
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
        return SlotReady::Ready((Slot::genesis(), GENESIS_BLOCK_HASH));
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
                        return Some((last_slot_in_prev_window, hash.clone()));
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
                Some((slot, hash)) => SlotReady::ParentReadyNotSeen((slot, hash.clone()), rx),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use mockall::{Sequence, predicate};

    use super::*;
    use crate::consensus::blockstore::MockBlockstore;
    use crate::consensus::pool::MockPool;
    use crate::consensus::{BlockInfo, ValidatorEpochInfo};
    use crate::crypto::Hash;
    use crate::disseminator::MockDisseminator;
    use crate::network::{UdpNetwork, localhost_ip_sockaddr};
    use crate::shredder::TOTAL_SHREDS;
    use crate::test_utils::generate_validators;
    use crate::{Transaction, ValidatorId};

    #[tokio::test]
    async fn produce_slice_empty_slices() {
        let txs_receiver: UdpNetwork<Transaction, Transaction> = UdpNetwork::new_with_any_port();
        let duration_left = Duration::from_micros(0);

        let parent = None;
        let (payload, maybe_duration) =
            produce_slice_payload(&txs_receiver, parent.clone(), duration_left).await;
        assert_eq!(maybe_duration, Duration::ZERO);
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 8 bytes
        assert_eq!(payload.data.len(), 8);

        let parent = Some((Slot::genesis(), GENESIS_BLOCK_HASH));
        let (payload, maybe_duration) =
            produce_slice_payload(&txs_receiver, parent.clone(), duration_left).await;
        assert_eq!(maybe_duration, Duration::ZERO);
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 8 bytes
        assert_eq!(payload.data.len(), 8);
    }

    #[tokio::test]
    async fn produce_slice_full_slices() {
        let txs_receiver: UdpNetwork<Transaction, Transaction> = UdpNetwork::new_with_any_port();
        let addr = localhost_ip_sockaddr(txs_receiver.port());
        let txs_sender: UdpNetwork<Transaction, Transaction> = UdpNetwork::new_with_any_port();
        // long enough duration so hopefully doesn't fire while collecting txs
        let duration_left = Duration::from_secs(100);

        tokio::spawn(async move {
            for i in 0..255 {
                let data = vec![i; MAX_TRANSACTION_SIZE];
                let msg = Transaction(data);
                txs_sender.send(&msg, addr).await.unwrap();
            }
        });

        let parent = None;
        let (payload, maybe_duration) =
            produce_slice_payload(&txs_receiver, parent.clone(), duration_left).await;
        assert!(maybe_duration > Duration::ZERO);
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
        let parent = (slot.prev(), GENESIS_BLOCK_HASH);

        let mut pool = MockPool::new();
        let p = parent.clone();
        pool.expect_wait_for_parent_ready()
            .with(predicate::eq(slot))
            .return_once(move |_slot| Either::Left(p));
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
        let parent = (slot.prev(), GENESIS_BLOCK_HASH);
        let (tx, rx) = oneshot::channel();
        tx.send(parent.clone()).unwrap();

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
    ) -> BlockProducer<MockDisseminator, UdpNetwork<Transaction, Transaction>> {
        let secret_key = signature::SecretKey::new(&mut rand::rng());
        let (_, epoch_info) = generate_validators(11);
        let epoch_info = Arc::new(ValidatorEpochInfo::new(ValidatorId::new(0), epoch_info));
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
        let hash: BlockHash = Hash::random_for_test().into();
        let hash_prev: BlockHash = Hash::random_for_test().into();
        let block_info = BlockInfo {
            hash: hash.clone(),
            parent: (slot.prev(), hash_prev.clone()),
        };

        // Handles TOTAL_SHRED number of calls.
        // The first TOTAL_SHRED - 1 calls return None.
        // The last call returns Some.
        let mut seq = Sequence::new();
        let mut blockstore = MockBlockstore::new();
        blockstore
            .expect_add_own_shred_as_leader()
            .times(TOTAL_SHREDS - 1)
            .in_sequence(&mut seq)
            .returning(move |_| Box::pin(async move { Ok(None) }));
        let bi = block_info.clone();
        blockstore
            .expect_add_own_shred_as_leader()
            .times(1)
            .in_sequence(&mut seq)
            .returning(move |_| {
                let bi = bi.clone();
                Box::pin(async move { Ok(Some(bi)) })
            });

        let mut pool = MockPool::new();
        let bi = block_info.clone();
        pool.expect_add_block()
            .returning(move |ret_block_id, ret_parent_block_id| {
                assert_eq!(ret_block_id, (slot, bi.hash.clone()));
                assert_eq!(bi.parent, ret_parent_block_id);
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
            .produce_block(slot, block_info.parent, None)
            .await
            .unwrap();
        assert_eq!(slot, ret.0);
        assert_eq!(block_info.hash, ret.1);
    }

    #[tokio::test]
    async fn verify_produce_block_parent_not_ready() {
        let slot = Slot::windows().nth(10).unwrap();
        let slot_hash: BlockHash = Hash::random_for_test().into();
        let old_parent = (slot.prev(), Hash::random_for_test().into());
        let new_parent = (slot.prev().prev(), Hash::random_for_test().into());
        let old_block_info = BlockInfo {
            hash: slot_hash.clone(),
            parent: old_parent,
        };
        let new_block_info = BlockInfo {
            hash: slot_hash,
            parent: new_parent.clone(),
        };

        let (first_slice_finished_tx, first_slice_finished_rx) = oneshot::channel();
        let (start_second_slice_tx, start_second_slice_rx) = oneshot::channel();

        let mut seq = Sequence::new();
        let mut blockstore = MockBlockstore::new();

        // handle first slice
        blockstore
            .expect_add_own_shred_as_leader()
            .times(TOTAL_SHREDS - 1)
            .in_sequence(&mut seq)
            .returning(move |_| Box::pin(async move { Ok(None) }));
        blockstore
            .expect_add_own_shred_as_leader()
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
            .expect_add_own_shred_as_leader()
            .times(TOTAL_SHREDS - 1)
            .in_sequence(&mut seq)
            .returning(move |_| Box::pin(async move { Ok(None) }));
        let nbi = new_block_info.clone();
        blockstore
            .expect_add_own_shred_as_leader()
            .times(1)
            .in_sequence(&mut seq)
            .returning(move |_| {
                let nbi = nbi.clone();
                Box::pin(async {
                    // final shred of second slice
                    // block is constructed with the new parent
                    Ok(Some(nbi))
                })
            });

        let mut pool = MockPool::new();
        let nbi = new_block_info.clone();
        pool.expect_add_block()
            .returning(move |ret_block_id, ret_parent_block_id| {
                assert_eq!(ret_block_id, (slot, nbi.hash.clone()));
                assert_eq!(nbi.parent, ret_parent_block_id);
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

        let np = new_parent.clone();
        tokio::spawn(async move {
            let () = first_slice_finished_rx.await.unwrap();
            parent_ready_tx.send(np).unwrap();
            start_second_slice_tx.send(()).unwrap();
        });

        let ret = block_producer
            .produce_block(slot, old_block_info.parent, Some(parent_ready_rx))
            .await
            .unwrap();

        assert_eq!(slot, ret.0);
        assert_eq!(new_block_info.hash, ret.1);
        assert_eq!(new_block_info.parent, new_parent);
    }
}
