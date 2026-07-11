// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Block production, leader-side of the consensus protocol.

use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::Result;
use fastrace::Span;
use log::{debug, info, warn};
use static_assertions::const_assert;
use tokio::pin;
use tokio::sync::{mpsc, oneshot, watch};
use tokio::time::sleep;
use tokio_util::sync::CancellationToken;

use crate::consensus::core::Input;
use crate::consensus::driver::ParentReadyMap;
use crate::consensus::{SharedBlockstore, ValidatorEpochInfo};
use crate::crypto::merkle::{BlockHash, GENESIS_BLOCK_HASH};
use crate::crypto::signature;
use crate::network::{Network, TransactionNetwork};
use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, ShredderPool, TOTAL_SHREDS};
use crate::types::{Slice, SliceHeader, SliceIndex, SlicePayload, Slot};
use crate::{BlockId, Disseminator, MAX_TRANSACTION_SIZE};

/// Produces blocks from transactions and dissminates them.
///
/// This is the leader's side of the consensus protocol.
/// Produces blocks in accordance with the consensus protocol's timeouts.
/// Receives transactions from clients via a [`Network`] instance and packs them into blocks.
/// Finished blocks are shredded and disseminated via a [`Disseminator`] instance.
pub(super) struct BlockProducer<D: Disseminator, T: Network> {
    /// Own validator's secret key (used e.g. for block production).
    /// This is not the same as the voting secret key, which is held by the consensus core.
    secret_key: signature::SecretKey,
    /// Other validators' info.
    epoch_info: Arc<ValidatorEpochInfo>,

    /// Blockstore for storing raw block data.
    blockstore: SharedBlockstore,
    /// Feeds drained blockstore events to the consensus core.
    inputs: mpsc::Sender<Input>,
    /// Observes the first ready parent per window, published by the driver.
    parent_ready: watch::Receiver<ParentReadyMap>,
    /// Observes the highest finalized slot, published by the driver.
    finalized: watch::Receiver<Slot>,

    /// Block dissemination network protocol for shreds.
    disseminator: Arc<D>,
    /// Network connection to receive transactions from clients.
    txs_receiver: T,

    /// Pool of shredders for shredding produced slices.
    ///
    /// Reused across slices to avoid reallocating Reed-Solomon working memory.
    shredders: ShredderPool<RegularShredder>,

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
    #[expect(clippy::too_many_arguments)]
    pub(super) fn new(
        secret_key: signature::SecretKey,
        epoch_info: Arc<ValidatorEpochInfo>,
        disseminator: Arc<D>,
        txs_receiver: T,
        blockstore: SharedBlockstore,
        inputs: mpsc::Sender<Input>,
        parent_ready: watch::Receiver<ParentReadyMap>,
        finalized: watch::Receiver<Slot>,
        cancel_token: CancellationToken,
        delta_block: Duration,
        delta_first_slice: Duration,
    ) -> Self {
        assert!(delta_block >= delta_first_slice);
        Self {
            secret_key,
            epoch_info,
            blockstore,
            inputs,
            parent_ready,
            finalized,
            disseminator,
            txs_receiver,
            // block production is sequential, so a single shredder is enough
            shredders: ShredderPool::with_size(1),
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

            // wait for ParentReady or block in previous slot
            let slot_ready = wait_for_first_slot(
                self.parent_ready.clone(),
                self.finalized.clone(),
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
                        // genesis block is already produced so skip it
                        (first_slot_in_window, GENESIS_BLOCK_HASH)
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
    /// The `parent_block_id` refers to the block of the previous slot which may end up not being the actually parent of the block.
    #[hotpath::measure]
    pub(super) async fn produce_block_parent_not_ready(
        &self,
        slot: Slot,
        parent_block_id: BlockId,
        mut parent_ready_receiver: oneshot::Receiver<BlockId>,
    ) -> Result<BlockId> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = &parent_block_id;
        assert_eq!(*parent_slot, slot.prev());
        assert!(slot.is_start_of_window());
        info!(
            "optimistically producing block in slot {} with parent {} in slot {}",
            slot,
            parent_hash.short_hex(),
            *parent_slot,
        );

        // only start the DELTA_BLOCK timer once the ParentReady event is seen
        let mut duration_left = Duration::MAX;
        for slice_index in SliceIndex::all() {
            let parent = if slice_index.is_first() {
                Some(parent_block_id.clone())
            } else {
                None
            };

            let time_for_slice = if slice_index.is_first() {
                // make sure first slice is produced on time
                // TODO: this can be made more accurate, only needed if production of first slice
                // still takes more than delta_first_slice after we saw ParentReady, not if:
                // 1. first slice is produced before ParentReady is seen, OR
                // 2. first slice finishes at most delta_first_slice after ParentReady is seen
                duration_left.min(self.delta_first_slice)
            } else {
                // cap timeout for each slice to `DELTA_BLOCK`
                // makes sure optimistic block production yields before timeout would expire
                duration_left.min(self.delta_block)
            };
            let produce_slice_future =
                produce_slice_payload(&self.txs_receiver, parent, time_for_slice);

            // If we have not yet received the ParentReady event, wait for it concurrently while producing the next slice.
            let (mut payload, new_duration_left) = if parent_ready_receiver.is_terminated() {
                produce_slice_future.await
            } else {
                pin!(produce_slice_future);
                tokio::select! {
                    res = &mut produce_slice_future => {
                        let (payload, _new_duration_left) = res;
                        // ParentReady event still not seen, do not start DELTA_BLOCK timer yet
                        (payload, Duration::MAX)
                    }
                    res = &mut parent_ready_receiver => {
                        // Got ParentReady event while producing slice.
                        // It's a NOP if we have been using the same parent as before.

                        let start = Instant::now();
                        let (mut payload, _maybe_duration) = produce_slice_future.await;
                        apply_parent_ready(&mut payload, res, &parent_block_id);
                        // ParentReady was seen, start the DELTA_BLOCK timer
                        // account for the time it took to finish producing the slice
                        debug!("starting blocktime timer");
                        let duration = self.delta_block.saturating_sub(start.elapsed());
                        (payload, duration)
                    }
                }
            };

            let is_last = slice_index.is_max() || new_duration_left.is_zero();
            if is_last && !parent_ready_receiver.is_terminated() {
                let received = (&mut parent_ready_receiver).await;
                apply_parent_ready(&mut payload, received, &parent_block_id);
            }
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

    /// Produces a block in the situation where we have already seen the `ParentReady` event.
    ///
    /// The `parent_block_id` refers to the block that is the ready parent.
    #[hotpath::measure]
    pub(crate) async fn produce_block_parent_ready(
        &self,
        slot: Slot,
        parent_block_id: BlockId,
    ) -> Result<BlockId> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = &parent_block_id;
        info!(
            "producing block in slot {} with ready parent {} in slot {}",
            slot,
            parent_hash.short_hex(),
            parent_slot,
        );

        let mut duration_left = self.delta_block;
        for slice_index in SliceIndex::all() {
            let (payload, new_duration_left) = if slice_index.is_first() {
                // make sure first slice is produced quickly enough so that other nodes do not generate the [`TimeoutCrashedLeader`] event
                let time_for_slice = self.delta_first_slice;
                let (payload, slice_duration_left) = produce_slice_payload(
                    &self.txs_receiver,
                    Some(parent_block_id.clone()),
                    time_for_slice,
                )
                .await;
                let elapsed = self.delta_first_slice.saturating_sub(slice_duration_left);
                let left = duration_left.saturating_sub(elapsed);

                (payload, left)
            } else {
                produce_slice_payload(&self.txs_receiver, None, duration_left).await
            };
            let is_last = slice_index.is_max() || new_duration_left.is_zero();
            let header = SliceHeader {
                slot,
                slice_index,
                is_last,
            };

            if let Some(block_hash) = self.shred_and_disseminate(header, payload).await? {
                return Ok((slot, block_hash));
            } else {
                assert!(!new_duration_left.is_zero());
                duration_left = new_duration_left;
            }
        }
        unreachable!()
    }

    /// Shreds and disseminates the slice payload.
    ///
    /// Returns Ok(Some(hash of the block)) if this is the last slice.
    /// Returns Ok(None) otherwise.
    #[hotpath::measure]
    async fn shred_and_disseminate(
        &self,
        header: SliceHeader,
        payload: SlicePayload,
    ) -> Result<Option<BlockHash>> {
        let slot = header.slot;
        let slice_index = header.slice_index;
        let is_last = header.is_last;
        // Build the slice by moving the payload in, then shred it by reference.
        // Shredding only reads the payload, so we can reclaim it afterwards and
        // hand a ready-made slice to the blockstore, instead of making it
        // Reed-Solomon-decode our own data back out.
        let slice = Slice::from_parts(header, payload);
        // Box the shreds so the large array lives on the heap instead of bloating
        // this future across the dissemination and `add_own_slice` awaits below.
        let shreds = Box::new(
            self.shredders
                .checkout()
                .expect("pool always has a shredder, block production is sequential")
                .shred(&slice, &self.secret_key)
                .expect("shredding of valid slice should never fail"),
        );
        let (_header, payload) = slice.deconstruct();

        // Disseminate every shred. Dissemination is best-effort: a send failure
        // is usually transient (e.g. a full socket buffer), so we try every
        // shred rather than bailing on the first, and we never propagate the
        // error. The slice is recorded locally below regardless, so any shred
        // that didn't make it out is recoverable by peers via repair — aborting
        // block production over a transient send error would needlessly stall
        // this leader.
        let mut failed = 0;
        let mut first_err = None;
        for s in shreds.iter() {
            if let Err(e) = self.disseminator.send(s.as_shred()).await {
                failed += 1;
                first_err.get_or_insert(e);
            }
        }

        // Fast path: we already have every shred and the decoded payload, so the
        // blockstore can skip RS-decode, Merkle verification and the per-shred
        // lock churn. The completed block hands back (slot, hash). Feed the
        // buffered events to the consensus core after releasing the write lock;
        // the core registers the completed block with the pool itself.
        let (block_info, events) = {
            let mut blockstore = self.blockstore.write().await;
            let block_info = blockstore.add_own_slice(payload, shreds);
            (block_info, blockstore.take_events())
        };
        for event in events {
            if self
                .inputs
                .send(Input::BlockstoreEvent(event))
                .await
                .is_err()
            {
                debug!("consensus core inbox closed, dropping input");
            }
        }

        if let Some(e) = first_err {
            warn!(
                "failed to disseminate {failed}/{TOTAL_SHREDS} shreds for slice {slice_index} in slot {slot}: {e}"
            );
        }

        match block_info {
            Some(block_info) => {
                // Trusted local data: a violation here is our own producer bug,
                // and the only alternative is proposing a truncated block that
                // followers can never reconstruct. Crash loudly instead.
                assert!(is_last, "block completed before its last slice");
                Ok(Some(block_info.hash))
            }
            None => {
                assert!(!is_last, "last slice did not complete the block");
                Ok(None)
            }
        }
    }
}

/// Unwraps a received `ParentReady` event and applies its parent to `payload`.
///
/// A no-op if the ready parent matches the one we were already building on.
fn apply_parent_ready(
    payload: &mut SlicePayload,
    received: Result<BlockId, oneshot::error::RecvError>,
    parent_block_id: &BlockId,
) {
    let (new_slot, new_hash) = received.expect("ParentReady sender should not be dropped");
    let (parent_slot, parent_hash) = parent_block_id;
    if &new_hash == parent_hash {
        debug!("parent is ready, continuing with same parent");
    } else {
        assert_ne!(&new_slot, parent_slot);
        debug!(
            "changed parent from {} in slot {} to {} in slot {}",
            parent_hash.short_hex(),
            parent_slot,
            new_hash.short_hex(),
            new_slot
        );
        payload.parent = Some((new_slot, new_hash));
    }
}

/// Produces a slice payload.
///
/// Listens to transactions on `txs_receive` for at most `duration_left`.
/// Manually serializes a [`Vec<Transaction>`] to keep track of how much space is left.
/// Stops if either the slice cannot fit any more transactions, or time runs out.
///
/// Returns the slice payload and the remaining duration.
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
    // +8 to encode number of txs, +8 to encode tx payload length
    const_assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE + 8 + 8);

    // reserve space for: parent info, and
    // 8 bytes for SlicePayload::data length
    let parent_encoded_len = wincode::serialized_size(&parent)
        .expect("computing serialized size of parent should not fail")
        as usize;
    let buffer_space = MAX_DATA_PER_SLICE - parent_encoded_len - 8;
    let mut buffer = Vec::<u8>::with_capacity(buffer_space);
    let mut tx_count = 0u64;
    // reserve space for the length prefix
    buffer.extend([0; 8]);

    let ret = loop {
        let sleep_duration = duration_left.saturating_sub(start_time.elapsed());
        let res = tokio::select! {
            () = sleep(sleep_duration) => {
                break Duration::ZERO;
            }
            res = txs_receiver.receive() => res,
        };
        let tx = res.expect("receiving tx");
        tx_count += 1;
        wincode::serialize_into(&mut buffer, &tx)
            .expect("serializing transaction into buffer should not fail");

        // if there is not enough space for another tx, break
        // +8 for the transaction length overhead
        if buffer_space - buffer.len() < MAX_TRANSACTION_SIZE + 8 {
            break duration_left.saturating_sub(start_time.elapsed());
        }
    };

    buffer[0..8].copy_from_slice(&tx_count.to_le_bytes());

    (SlicePayload::new(parent, buffer), ret)
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
/// - the driver published a ready parent for it (Pool's `ParentReady`), OR
/// - the blockstore has stored a block for the previous slot.
///
/// See [`SlotReady`] for what is returned.
async fn wait_for_first_slot(
    mut parent_ready: watch::Receiver<ParentReadyMap>,
    finalized: watch::Receiver<Slot>,
    blockstore: SharedBlockstore,
    first_slot_in_window: Slot,
) -> SlotReady {
    assert!(first_slot_in_window.is_start_of_window());
    if first_slot_in_window.is_genesis_window() {
        return SlotReady::Ready((Slot::genesis(), GENESIS_BLOCK_HASH));
    }

    // Concurrently wait for:
    // - a ready parent published by the driver,
    // - block reconstruction in blockstore, OR
    // - notification that a later slot was finalized.
    let watch_for_oneshot = parent_ready.clone();
    tokio::select! {
        res = parent_ready.wait_for(|map| map.contains_key(&first_slot_in_window)) => {
            match res {
                Ok(map) => SlotReady::Ready(map[&first_slot_in_window].clone()),
                // the driver shut down; the node is going down anyway
                Err(_) => SlotReady::Skip,
            }
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
                    if *finalized.borrow() >= first_slot_in_window {
                        return None;
                    }
                    sleep(Duration::from_millis(1)).await;
                }
            });
            handle.await.expect("error in task")
        } => {
            match res {
                None => SlotReady::Skip,
                Some((slot, hash)) => {
                    let rx = parent_ready_oneshot(watch_for_oneshot, first_slot_in_window);
                    SlotReady::ParentReadyNotSeen((slot, hash), rx)
                }
            }
        }
    }
}

/// Bridges the parent-ready watch to a oneshot channel for the given `slot`.
///
/// The returned receiver resolves with the first ready parent for `slot`,
/// mirroring the interface [`BlockProducer::produce_block_parent_not_ready`]
/// selects on while producing optimistically. If the driver shuts down before
/// a parent is ready, the sender is dropped.
fn parent_ready_oneshot(
    mut parent_ready: watch::Receiver<ParentReadyMap>,
    slot: Slot,
) -> oneshot::Receiver<BlockId> {
    let (tx, rx) = oneshot::channel();
    tokio::spawn(async move {
        if let Ok(map) = parent_ready.wait_for(|map| map.contains_key(&slot)).await {
            let _ = tx.send(map[&slot].clone());
        }
    });
    rx
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use mockall::Sequence;
    use tokio::sync::RwLock;

    use super::*;
    use crate::consensus::blockstore::MockBlockstore;
    use crate::consensus::{BlockInfo, ValidatorEpochInfo};
    use crate::crypto::Hash;
    use crate::disseminator::MockDisseminator;
    use crate::network::{UdpNetwork, localhost_ip_sockaddr};
    use crate::test_utils::{generate_validators, random_block_id};
    use crate::{Transaction, ValidatorIndex};

    /// Fresh channels standing in for the driver's side of the wiring.
    ///
    /// Held (not read) for the duration of a test so the producer never
    /// sees closed channels.
    struct DriverStandIn {
        _input_rx: mpsc::Receiver<Input>,
        _parent_ready_tx: watch::Sender<ParentReadyMap>,
        _finalized_tx: watch::Sender<Slot>,
    }

    #[tokio::test]
    async fn produce_slice_empty_slices() {
        let txs_receiver: UdpNetwork<Transaction, Transaction> = UdpNetwork::new_with_any_port();
        let duration_left = Duration::ZERO;

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
        let parent_len = wincode::serialized_size(&parent).unwrap() as usize;
        let (payload, maybe_duration) =
            produce_slice_payload(&txs_receiver, parent.clone(), duration_left).await;
        assert!(maybe_duration > Duration::ZERO);
        assert_eq!(payload.parent, parent);
        let max_len = MAX_DATA_PER_SLICE - parent_len - 8;
        assert!(payload.data.len() <= max_len);
        assert!(payload.data.len() + MAX_TRANSACTION_SIZE + 8 > max_len);
    }

    #[tokio::test]
    async fn wait_for_first_slot_genesis() {
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(MockBlockstore::new()));
        let (_parent_ready_tx, parent_ready_rx) = watch::channel(ParentReadyMap::new());
        let (_finalized_tx, finalized_rx) = watch::channel(Slot::genesis());

        let status =
            wait_for_first_slot(parent_ready_rx, finalized_rx, blockstore, Slot::genesis()).await;
        assert!(matches!(status, SlotReady::Ready(_)));
    }

    #[tokio::test]
    async fn wait_for_first_slot_parent_already_ready() {
        // the concurrent blockstore poll may run before the ready parent wins
        let mut mock_blockstore = MockBlockstore::new();
        mock_blockstore
            .expect_disseminated_block_hash()
            .returning(|_| None);
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(mock_blockstore));
        let (parent_ready_tx, parent_ready_rx) = watch::channel(ParentReadyMap::new());
        let (_finalized_tx, finalized_rx) = watch::channel(Slot::genesis());

        let slot = Slot::windows().nth(10).unwrap();
        let parent = (slot.prev(), GENESIS_BLOCK_HASH);
        parent_ready_tx.send_modify(|map| {
            map.insert(slot, parent.clone());
        });

        let status = wait_for_first_slot(parent_ready_rx, finalized_rx, blockstore, slot).await;
        match status {
            SlotReady::Ready(p) => assert_eq!(p, parent),
            other => panic!("unexpected {other:?}"),
        }
    }

    #[tokio::test]
    async fn wait_for_first_slot_parent_ready_later() {
        // the blockstore poll runs until the (delayed) parent becomes ready
        let mut mock_blockstore = MockBlockstore::new();
        mock_blockstore
            .expect_disseminated_block_hash()
            .returning(|_| None);
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(mock_blockstore));
        let (parent_ready_tx, parent_ready_rx) = watch::channel(ParentReadyMap::new());
        let (_finalized_tx, finalized_rx) = watch::channel(Slot::genesis());

        let slot = Slot::windows().nth(10).unwrap();
        let parent = (slot.prev(), GENESIS_BLOCK_HASH);

        // parent becomes ready only while we are already waiting
        let p = parent.clone();
        tokio::spawn(async move {
            sleep(Duration::from_millis(50)).await;
            parent_ready_tx.send_modify(|map| {
                map.insert(slot, p);
            });
        });

        let status = wait_for_first_slot(parent_ready_rx, finalized_rx, blockstore, slot).await;
        match status {
            SlotReady::Ready(p) => assert_eq!(p, parent),
            other => panic!("unexpected {other:?}"),
        }
    }

    /// A bunch of boilerplate to initialize and return a [`BlockProducer`].
    fn setup(
        blockstore: MockBlockstore,
        disseminator: MockDisseminator,
        delta_block: Duration,
        delta_first_slice: Duration,
    ) -> (
        BlockProducer<MockDisseminator, UdpNetwork<Transaction, Transaction>>,
        DriverStandIn,
    ) {
        let secret_key = signature::SecretKey::new(&mut rand::rng());
        let (_, epoch_info) = generate_validators(11);
        let epoch_info = Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(0), epoch_info));
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(blockstore));
        let disseminator = Arc::new(disseminator);
        let txs_receiver = UdpNetwork::new_with_any_port();
        let cancel_token = CancellationToken::new();
        let (input_tx, input_rx) = mpsc::channel(100);
        let (parent_ready_tx, parent_ready_rx) = watch::channel(ParentReadyMap::new());
        let (finalized_tx, finalized_rx) = watch::channel(Slot::genesis());

        let producer = BlockProducer::new(
            secret_key,
            epoch_info,
            disseminator,
            txs_receiver,
            blockstore,
            input_tx,
            parent_ready_rx,
            finalized_rx,
            cancel_token,
            delta_block,
            delta_first_slice,
        );
        let stand_in = DriverStandIn {
            _input_rx: input_rx,
            _parent_ready_tx: parent_ready_tx,
            _finalized_tx: finalized_tx,
        };
        (producer, stand_in)
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

        // The producer ingests its own block one slice at a time via the fast
        // path; a single-slice block completes on the only `add_own_slice` call.
        let mut blockstore = MockBlockstore::new();
        let bi = block_info.clone();
        blockstore
            .expect_add_own_slice()
            .times(1)
            .returning(move |_slice, _shreds| Some(bi.clone()));
        blockstore.expect_take_events().returning(Vec::new);

        let mut disseminator = MockDisseminator::new();
        disseminator
            .expect_send()
            .returning(|_| Box::pin(async { Ok(()) }));
        let (block_producer, _driver) = setup(
            blockstore,
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
        let slot_hash: BlockHash = Hash::random_for_test().into();
        let old_parent = random_block_id(slot.prev());
        let new_parent = random_block_id(slot.prev().prev());
        let old_block_info = BlockInfo {
            hash: slot_hash.clone(),
            parent: old_parent,
        };
        let new_block_info = BlockInfo {
            hash: slot_hash,
            parent: new_parent.clone(),
        };

        // NOTE: the blockstore is now sync, so the rendezvous blocks on std
        // channels inside the mock (briefly blocking the runtime thread) and a
        // plain OS thread plays the coordinator that reacts in between.
        let (first_slice_finished_tx, first_slice_finished_rx) = std::sync::mpsc::channel();
        let (start_second_slice_tx, start_second_slice_rx) = std::sync::mpsc::channel();

        let mut seq = Sequence::new();
        let mut blockstore = MockBlockstore::new();

        // first slice: signal completion, then wait for the parent-ready event
        // before the producer moves on to the second slice
        blockstore
            .expect_add_own_slice()
            .times(1)
            .in_sequence(&mut seq)
            .return_once(move |_slice, _shreds| {
                first_slice_finished_tx.send(()).unwrap();
                let () = start_second_slice_rx.recv().unwrap();
                None
            });

        // second (last) slice: block is constructed with the new parent
        let nbi = new_block_info.clone();
        blockstore
            .expect_add_own_slice()
            .times(1)
            .in_sequence(&mut seq)
            .returning(move |_slice, _shreds| Some(nbi.clone()));
        blockstore.expect_take_events().returning(Vec::new);

        let mut disseminator = MockDisseminator::new();
        disseminator
            .expect_send()
            .returning(|_| Box::pin(async { Ok(()) }));
        let (block_producer, _driver) = setup(
            blockstore,
            disseminator,
            Duration::from_micros(0),
            Duration::from_millis(0),
        );

        let (parent_ready_tx, parent_ready_rx) = oneshot::channel();

        let np = new_parent.clone();
        std::thread::spawn(move || {
            let () = first_slice_finished_rx.recv().unwrap();
            parent_ready_tx.send(np).unwrap();
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
