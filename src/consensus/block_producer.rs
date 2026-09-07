// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Block production, leader-side of the consensus protocol.

use std::ops::ControlFlow;
use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::Result;
use either::Either;
use fastrace::Span;
use log::{debug, info, warn};
use tokio::pin;
use tokio::sync::oneshot;
use tokio::time::sleep;
use tokio_util::sync::CancellationToken;

use crate::consensus::{SharedBlockstore, SharedPool, ValidatorEpochInfo};
use crate::crypto::merkle::{BlockHash, GENESIS_BLOCK_HASH};
use crate::crypto::signature;
use crate::network::{Network, TransactionNetwork};
use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, ShredderPool, TOTAL_SHREDS};
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
    blockstore: SharedBlockstore,
    /// Pool of votes and certificates.
    pool: SharedPool,

    /// Block dissemination network protocol for shreds.
    disseminator: Arc<D>,
    /// Network connection to receive transactions from clients.
    txs_receiver: T,
    /// Pool of shredders, reused across all slices and blocks we produce.
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
        pool: SharedPool,
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

            // genesis block is already produced
            // otherwise, wait for ParentReady or block in previous slot
            let slot_ready = wait_for_first_slot(
                self.pool.clone(),
                self.blockstore.clone(),
                first_slot_in_window,
            )
            .await;

            // produce first block
            let (mut parent, mut rx) = match slot_ready {
                SlotReady::Skip => {
                    warn!(
                        "not producing in window {first_slot_in_window}..{last_slot_in_window}, saw later finalization"
                    );
                    continue;
                }
                SlotReady::Ready(parent) => (parent, None),
                SlotReady::ParentReadyNotSeen(parent, rx) => (parent, Some(rx)),
            };

            // produce remaining blocks, skip first slot if genesis
            let skip = first_slot_in_window.is_genesis() as usize;
            for slot in first_slot_in_window.slots_in_window().skip(skip) {
                let start = Instant::now();
                let Some(block_id) = self.produce_block(slot, parent, rx).await? else {
                    // The window was finalized while we were still producing it (Pool pruned
                    // the slot, dropping the `ParentReady` sender). The block is moot, so stop
                    // and move on to the next window, mirroring the `SlotReady::Skip` path above.
                    break;
                };
                parent = block_id;
                rx = None;
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
    /// If `parent_ready_rx` is `None`, the parent is already confirmed and the [`super::DELTA_BLOCK`]
    /// timer starts immediately. Otherwise production begins optimistically on the guessed
    /// parent and the timer starts once the `ParentReady` event arrives (see [`SliceProducer`],
    /// which owns all of the optimistic-handover and timing state).
    ///
    /// Returns `Ok(None)` if production was aborted because the slot was pruned while we were
    /// producing it: a dropped `parent_ready_rx` sender means the Pool finalized past this slot,
    /// so the block is moot and the caller should stop producing this window.
    #[hotpath::measure]
    async fn produce_block(
        &self,
        slot: Slot,
        parent_block_id: BlockId,
        parent_ready_rx: Option<oneshot::Receiver<BlockId>>,
    ) -> Result<Option<BlockId>> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));

        // Optimistic production guesses the parent from the previous slot and may switch to
        // the real one once the `ParentReady` event arrives. Otherwise the parent is known.
        let optimistic = parent_ready_rx.is_some();
        let (parent_slot, parent_hash) = &parent_block_id;
        if optimistic {
            assert_eq!(parent_slot, &slot.prev());
            assert!(slot.is_start_of_window());
        }
        info!(
            "producing block in slot {slot} with {} parent {} in slot {parent_slot}",
            if optimistic { "optimistic" } else { "ready" },
            parent_hash.short_hex(),
        );

        let mut producer = SliceProducer::new(
            parent_block_id,
            parent_ready_rx,
            self.delta_block,
            self.delta_first_slice,
        );

        for slice_index in SliceIndex::all() {
            let (payload, is_last) = match producer
                .next_slice(&self.txs_receiver, slice_index)
                .await
            {
                SliceOutcome::Produced { payload, is_last } => (payload, is_last),
                // The Pool pruned this slot (finalization advanced past it), so the block
                // is moot; stop and let the caller move on to the next window.
                SliceOutcome::Aborted => {
                    warn!(
                        "aborting block production for slot {slot}: slot pruned (ParentReady sender dropped)"
                    );
                    return Ok(None);
                }
            };

            let header = SliceHeader {
                slot,
                slice_index,
                is_last,
            };
            // A block completes (`Some`) only on its last slice; the `is_last` invariant is
            // owned and asserted (both directions) inside `shred_and_disseminate`.
            if let Some(block_hash) = self.shred_and_disseminate(header, payload).await? {
                return Ok(Some((slot, block_hash)));
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
        // lock churn. The completed block hands back (slot, hash).
        let block_info = self
            .blockstore
            .write()
            .await
            .add_own_slice(payload, shreds)
            .await;

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
                let block_id = (slot, block_info.hash.clone());
                self.pool
                    .write()
                    .await
                    .add_block(block_id, block_info.parent)
                    .await;
                Ok(Some(block_info.hash))
            }
            None => {
                assert!(!is_last, "last slice did not complete the block");
                Ok(None)
            }
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
        // The confirmed parent may share the optimistic guess's slot (the previous leader
        // equivocated and a different block there was certified) or sit in an earlier slot
        // (intervening slots were skipped), but never a later one: a `ParentReady` for a
        // window-start slot only certifies parents strictly before it.
        debug_assert!(new_slot <= old_slot);
        debug!(
            "changed parent from {} in slot {} to {} in slot {}",
            old_hash.short_hex(),
            old_slot,
            new_hash.short_hex(),
            new_slot,
        );
        Some(new)
    } else {
        debug!("parent is ready, continuing with same parent");
        None
    }
}

/// Collects transactions into a slice payload, gathering until the slice is full or `deadline`.
///
/// Listens to transactions on `txs_receiver` and manually serializes them into a
/// [`Vec<Transaction>`] to track how much space is left, reserving room for `parent` (if any)
/// plus the 8-byte length prefix. Stops once another transaction could not fit, or `deadline`
/// is reached.
async fn produce_slice_payload<T>(
    txs_receiver: &T,
    parent: Option<BlockId>,
    deadline: Instant,
) -> SlicePayload
where
    T: TransactionNetwork,
{
    // each slice should be able hold at least 1 transaction
    // +8 to encode number of txs, +8 to encode tx payload length
    const _: () = assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE + 8 + 8);

    // reserve space for the parent info and 8 bytes for the SlicePayload::data length
    let parent_encoded_len = wincode::serialized_size(&parent)
        .expect("computing serialized size of parent should not fail")
        as usize;
    let buffer_space = MAX_DATA_PER_SLICE - parent_encoded_len - 8;
    let mut buffer = Vec::<u8>::with_capacity(buffer_space);
    let mut tx_count = 0u64;
    // reserve space for the length prefix
    buffer.extend([0; 8]);

    loop {
        let sleep_duration = deadline.saturating_duration_since(Instant::now());
        let res = tokio::select! {
            () = sleep(sleep_duration) => break,
            res = txs_receiver.receive() => res,
        };
        let tx = res.expect("receiving tx");
        tx_count += 1;
        wincode::serialize_into(&mut buffer, &tx)
            .expect("serializing transaction into buffer should not fail");

        // if there is not enough space for another tx, break
        // +8 for the transaction length overhead
        if buffer_space - buffer.len() < MAX_TRANSACTION_SIZE + 8 {
            break;
        }
    }

    buffer[0..8].copy_from_slice(&tx_count.to_le_bytes());
    SlicePayload::new(parent, buffer)
}

/// Outcome of producing a single slice via [`SliceProducer::next_slice`].
enum SliceOutcome {
    /// Slice produced successfully; `is_last` marks the final slice of the block.
    Produced {
        payload: SlicePayload,
        is_last: bool,
    },
    /// The `ParentReady` sender was dropped (the slot was pruned after finalization advanced
    /// past it). Production must abort; the block is moot.
    Aborted,
}

/// Drives production of the slices of one block, owning the optimistic `ParentReady` handover
/// and the [`super::DELTA_BLOCK`] timing.
///
/// Each slice's parent is decided *before* the slice is produced: the first slice carries the
/// (possibly guessed) parent; if `ParentReady` later confirms a *different* parent, the first
/// slice produced afterwards carries the correction exactly once (the wire format allows one
/// such parent override on a non-first slice, see `try_reconstruct_block`). No payload is ever
/// mutated after production, so a slice only reserves parent space when it actually carries one.
struct SliceProducer {
    /// Best-known parent: the optimistic guess until `ParentReady` confirms the real one.
    parent: BlockId,
    /// Delivers the confirmed parent while we are still producing optimistically; `None` once
    /// the parent is confirmed (or it was already confirmed when production started).
    parent_ready_rx: Option<oneshot::Receiver<BlockId>>,
    /// Set once `ParentReady` confirmed a parent that differs from our guess and that has not
    /// yet been written onto a slice. The next slice produced carries it, exactly once.
    override_pending: bool,
    /// Absolute end of the [`super::DELTA_BLOCK`] budget, set once the parent is confirmed; `None` while
    /// still producing optimistically (the timer has not started yet).
    deadline: Option<Instant>,
    delta_block: Duration,
    delta_first_slice: Duration,
}

impl SliceProducer {
    fn new(
        parent: BlockId,
        parent_ready_rx: Option<oneshot::Receiver<BlockId>>,
        delta_block: Duration,
        delta_first_slice: Duration,
    ) -> Self {
        // When the parent is already confirmed, the timer starts right away.
        let deadline = parent_ready_rx
            .is_none()
            .then(|| Instant::now() + delta_block);
        Self {
            parent,
            parent_ready_rx,
            override_pending: false,
            deadline,
            delta_block,
            delta_first_slice,
        }
    }

    /// Produces the next slice, resolving the optimistic `ParentReady` handover as needed.
    async fn next_slice<T>(&mut self, txs_receiver: &T, slice_index: SliceIndex) -> SliceOutcome
    where
        T: TransactionNetwork,
    {
        let is_first = slice_index.is_first();
        let is_max = slice_index.is_max();

        // The final slice is the last chance to carry a parent correction, so block for
        // `ParentReady` before producing it if it is still pending.
        if is_max && self.parent_ready_rx.is_some() {
            let mut rx = self.parent_ready_rx.take().expect("just checked is_some");
            if self.apply_parent_ready((&mut rx).await).is_break() {
                return SliceOutcome::Aborted;
            }
        }

        let parent = self.parent_for_slice(is_first);
        let slice_deadline = self.slice_deadline(is_first);

        // While still optimistic, race tx-gathering against `ParentReady`: whichever resolves
        // first wins. The event starts the timer and may flag an override for the next slice.
        let payload = if self.parent_ready_rx.is_some() {
            let mut rx = self.parent_ready_rx.take().expect("just checked is_some");
            let produce = produce_slice_payload(txs_receiver, parent, slice_deadline);
            pin!(produce);
            tokio::select! {
                payload = &mut produce => {
                    // `ParentReady` not seen yet; keep awaiting it on later slices.
                    self.parent_ready_rx = Some(rx);
                    payload
                }
                res = &mut rx => {
                    if self.apply_parent_ready(res).is_break() {
                        return SliceOutcome::Aborted;
                    }
                    // finish gathering this slice (its parent was already decided above)
                    produce.await
                }
            }
        } else {
            produce_slice_payload(txs_receiver, parent, slice_deadline).await
        };

        let is_last = self.is_last_slice(is_max);
        SliceOutcome::Produced { payload, is_last }
    }

    /// Whether the slice just produced completes the block.
    ///
    /// True once the block-time budget is spent (or the max slice index is reached) — but
    /// *never* while a parent override is still owed. A mid-slice `ParentReady` handover confirms
    /// the override *after* this slice's parent was already fixed (see [`Self::next_slice`] and
    /// [`Self::parent_for_slice`]), so the correction can only ride a *later* slice. Ending the
    /// block here would strand it, leaving followers to reconstruct on the stale guessed parent
    /// and orphan the slot.
    fn is_last_slice(&self, is_max: bool) -> bool {
        // A pending override never coincides with the max slice: there the handover is applied
        // *before* the parent is chosen (see [`Self::next_slice`]), so the override is written
        // onto this slice rather than deferred. Forcing `false` below therefore always leaves a
        // (non-max) next slice index to carry the deferred correction.
        debug_assert!(!(is_max && self.override_pending));
        if self.override_pending {
            return false;
        }
        is_max || self.deadline.is_some_and(|d| Instant::now() >= d)
    }

    /// The parent this slice carries: the first slice always carries the current best parent;
    /// the first slice after a confirmed change carries the correction (once); others none.
    fn parent_for_slice(&mut self, is_first: bool) -> Option<BlockId> {
        if is_first {
            Some(self.parent.clone())
        } else if self.override_pending {
            self.override_pending = false;
            Some(self.parent.clone())
        } else {
            None
        }
    }

    /// Deadline for producing one slice.
    ///
    /// The per-slice cap (`delta_first_slice` for the first slice, else `delta_block`),
    /// clamped to the block deadline once the timer is running.
    fn slice_deadline(&self, is_first: bool) -> Instant {
        let cap = if is_first {
            self.delta_first_slice
        } else {
            self.delta_block
        };
        let by_cap = Instant::now() + cap;
        match self.deadline {
            Some(deadline) => deadline.min(by_cap),
            None => by_cap,
        }
    }

    /// Applies a resolved `ParentReady`: starts the timer and,
    /// if the confirmed parent differs from our guess,
    /// records an override for the next slice.
    ///
    /// Returns [`ControlFlow::Break`] if the sender was dropped
    /// (the slot was pruned and production must abort).
    fn apply_parent_ready(
        &mut self,
        res: Result<BlockId, oneshot::error::RecvError>,
    ) -> ControlFlow<()> {
        let Ok(new_parent) = res else {
            return ControlFlow::Break(());
        };
        if let Some(new) = apply_parent_update(&self.parent, new_parent) {
            self.parent = new;
            self.override_pending = true;
        }
        debug!("starting blocktime timer");
        self.deadline = Some(Instant::now() + self.delta_block);
        ControlFlow::Continue(())
    }
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
    pool: SharedPool,
    blockstore: SharedBlockstore,
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
            match res {
                Ok(parent) => SlotReady::Ready(parent),
                // The Pool pruned this slot's `ParentReady` state (finalization advanced past
                // the window), dropping the sender. The window is moot, so skip it — the same
                // outcome the finalization-poll branch below yields, and mirroring the
                // `SliceOutcome::Aborted` path in `produce_block`.
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
    use std::time::{Duration, Instant};

    use mockall::{Sequence, predicate};
    use tokio::sync::RwLock;

    use super::*;
    use crate::consensus::blockstore::MockBlockstore;
    use crate::consensus::pool::MockPool;
    use crate::consensus::{BlockInfo, ValidatorEpochInfo};
    use crate::crypto::Hash;
    use crate::disseminator::MockDisseminator;
    use crate::network::{UdpNetwork, localhost_ip_sockaddr};
    use crate::test_utils::{generate_validators, random_block_id};
    use crate::{Transaction, ValidatorIndex};

    /// An [`Instant`] one second in the past, i.e. a block-time budget that is already spent.
    fn spent_deadline() -> Instant {
        Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("monotonic clock is more than 1s past its epoch")
    }

    #[tokio::test]
    async fn produce_slice_empty_slices() {
        let txs_receiver: UdpNetwork<Transaction, Transaction> = UdpNetwork::new_with_any_port();
        // a deadline in the past makes production return immediately with no transactions
        let deadline = Instant::now();

        let parent = None;
        let payload = produce_slice_payload(&txs_receiver, parent.clone(), deadline).await;
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 8 bytes
        assert_eq!(payload.data.len(), 8);

        let parent = Some((Slot::genesis(), GENESIS_BLOCK_HASH));
        let payload = produce_slice_payload(&txs_receiver, parent.clone(), deadline).await;
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
        let payload = produce_slice_payload(
            &txs_receiver,
            parent.clone(),
            Instant::now() + duration_left,
        )
        .await;
        assert_eq!(payload.parent, parent);
        let max_len = MAX_DATA_PER_SLICE - parent_len - 8;
        assert!(payload.data.len() <= max_len);
        assert!(payload.data.len() + MAX_TRANSACTION_SIZE + 8 > max_len);
    }

    /// A full slice that carries a parent must still fit within `MAX_DATA_PER_SLICE`:
    /// `produce_slice_payload` reserves room for the parent up front before packing txs, so
    /// shredding the slice can never fail because of the parent.
    #[tokio::test]
    async fn produce_slice_full_slice_with_parent_fits() {
        let txs_receiver: UdpNetwork<Transaction, Transaction> = UdpNetwork::new_with_any_port();
        let addr = localhost_ip_sockaddr(txs_receiver.port());
        let txs_sender: UdpNetwork<Transaction, Transaction> = UdpNetwork::new_with_any_port();
        let duration_left = Duration::from_secs(100);

        tokio::spawn(async move {
            for i in 0..255 {
                let data = vec![i; MAX_TRANSACTION_SIZE];
                txs_sender.send(&Transaction(data), addr).await.unwrap();
            }
        });

        let parent = Some((Slot::genesis(), GENESIS_BLOCK_HASH));
        let payload = produce_slice_payload(
            &txs_receiver,
            parent.clone(),
            Instant::now() + duration_left,
        )
        .await;
        assert_eq!(payload.parent, parent);
        // the slice is full: it cannot fit another transaction
        assert!(payload.to_bytes().len() + MAX_TRANSACTION_SIZE + 8 > MAX_DATA_PER_SLICE);
        // but it still fits within the slice limit, including the reserved parent
        assert!(payload.to_bytes().len() <= MAX_DATA_PER_SLICE);
    }

    /// When an optimistic `ParentReady` confirms a *different* parent than we guessed, the
    /// correction is written onto exactly one slice — the first produced after the handover,
    /// never the first slice and never twice — and the timer only starts at the handover.
    #[test]
    fn slice_producer_writes_override_once_after_handover() {
        let delta = Duration::from_millis(400);
        let slot = Slot::windows().nth(10).unwrap();
        let guess = random_block_id(slot.prev());
        let confirmed = random_block_id(slot.prev().prev());

        let (_tx, rx) = oneshot::channel();
        let mut producer = SliceProducer::new(guess.clone(), Some(rx), delta, delta);

        // first slice carries the optimistic guess; the timer has not started yet
        assert_eq!(producer.parent_for_slice(true), Some(guess));
        assert!(producer.deadline.is_none());

        // the handover confirms a different parent: the timer starts, an override is queued
        assert_eq!(
            producer.apply_parent_ready(Ok(confirmed.clone())),
            ControlFlow::Continue(())
        );
        assert!(producer.deadline.is_some());

        // the next non-first slice carries the correction, exactly once
        assert_eq!(producer.parent_for_slice(false), Some(confirmed));
        assert_eq!(producer.parent_for_slice(false), None);
    }

    /// A slice must never be marked as the block's last while a confirmed parent override is
    /// still owed: the correction can only ride a later slice, so ending the block here would
    /// strand it and leave followers reconstructing on the stale guessed parent.
    #[test]
    fn slice_producer_defers_last_slice_while_override_pending() {
        let delta = Duration::from_millis(400);
        let slot = Slot::windows().nth(10).unwrap();
        let guess = random_block_id(slot.prev());
        let confirmed = random_block_id(slot.prev().prev());

        let (_tx, rx) = oneshot::channel();
        let mut producer = SliceProducer::new(guess, Some(rx), delta, delta);

        // A mid-slice handover confirms a different parent and queues the override; force the
        // block-time budget to be already spent so, without the guard, this slice would be last.
        assert_eq!(
            producer.apply_parent_ready(Ok(confirmed.clone())),
            ControlFlow::Continue(())
        );
        producer.deadline = Some(spent_deadline());
        assert!(producer.override_pending);

        // The budget is spent, yet the owed override forbids ending the block on this slice.
        assert!(!producer.is_last_slice(false));

        // The next slice writes the override (clearing it); only now may the block end.
        assert_eq!(producer.parent_for_slice(false), Some(confirmed));
        assert!(!producer.override_pending);
        assert!(producer.is_last_slice(false));
    }

    /// With no override owed, a spent block-time budget (or the max slice index) ends the block.
    #[test]
    fn slice_producer_last_slice_without_override() {
        let delta = Duration::from_millis(400);
        let guess = random_block_id(Slot::windows().nth(10).unwrap().prev());
        let mut producer = SliceProducer::new(guess, None, delta, delta);

        // Budget not yet spent: not the last slice.
        producer.deadline = Some(Instant::now() + Duration::from_secs(1));
        assert!(!producer.is_last_slice(false));

        // Budget spent: last slice.
        producer.deadline = Some(spent_deadline());
        assert!(producer.is_last_slice(false));

        // The max slice index always ends the block.
        producer.deadline = None;
        assert!(producer.is_last_slice(true));
    }

    /// A handover confirming the *same* parent we guessed writes no override.
    #[test]
    fn slice_producer_no_override_when_parent_unchanged() {
        let delta = Duration::from_millis(400);
        let guess = random_block_id(Slot::windows().nth(10).unwrap().prev());

        let (_tx, rx) = oneshot::channel();
        let mut producer = SliceProducer::new(guess.clone(), Some(rx), delta, delta);

        assert_eq!(producer.parent_for_slice(true), Some(guess.clone()));
        assert_eq!(
            producer.apply_parent_ready(Ok(guess)),
            ControlFlow::Continue(())
        );
        assert_eq!(producer.parent_for_slice(false), None);
    }

    /// A dropped `ParentReady` sender (the slot was pruned) makes the handover signal an abort.
    #[tokio::test]
    async fn slice_producer_apply_parent_ready_aborts_on_dropped_sender() {
        let delta = Duration::from_millis(400);
        let guess = random_block_id(Slot::windows().nth(10).unwrap().prev());

        let (tx, rx) = oneshot::channel::<BlockId>();
        drop(tx);
        let dropped = rx.await; // resolves to `Err(RecvError)`

        let mut producer = SliceProducer::new(guess, None, delta, delta);
        assert_eq!(producer.apply_parent_ready(dropped), ControlFlow::Break(()));
    }

    #[tokio::test]
    async fn wait_for_first_slot_genesis() {
        let pool: SharedPool = Arc::new(RwLock::new(MockPool::new()));
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(MockBlockstore::new()));

        let status = wait_for_first_slot(pool, blockstore, Slot::genesis()).await;
        assert!(matches!(status, SlotReady::Ready(_)));
    }

    #[tokio::test]
    async fn wait_for_first_slot_parent_already_ready() {
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(MockBlockstore::new()));

        let slot = Slot::windows().nth(10).unwrap();
        let parent = (slot.prev(), GENESIS_BLOCK_HASH);

        let mut pool = MockPool::new();
        let p = parent.clone();
        pool.expect_wait_for_parent_ready()
            .with(predicate::eq(slot))
            .return_once(move |_slot| Either::Left(p));
        let pool: SharedPool = Arc::new(RwLock::new(pool));

        let status = wait_for_first_slot(pool, blockstore, slot).await;
        match status {
            SlotReady::Ready(p) => assert_eq!(p, parent),
            other => panic!("unexpected {other:?}"),
        }
    }

    #[tokio::test]
    async fn wait_for_first_slot_parent_ready_later() {
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(MockBlockstore::new()));

        let slot = Slot::windows().nth(10).unwrap();
        let parent = (slot.prev(), GENESIS_BLOCK_HASH);
        let (tx, rx) = oneshot::channel();
        tx.send(parent.clone()).unwrap();

        let mut pool = MockPool::new();
        pool.expect_wait_for_parent_ready()
            .with(predicate::eq(slot))
            .return_once(move |_slot| Either::Right(rx));
        let pool: SharedPool = Arc::new(RwLock::new(pool));

        let status = wait_for_first_slot(pool, blockstore, slot).await;
        match status {
            SlotReady::Ready(p) => assert_eq!(p, parent),
            other => panic!("unexpected {other:?}"),
        }
    }

    /// A dropped `ParentReady` sender — the Pool pruned the slot after finalization advanced past
    /// the window — must make `wait_for_first_slot` skip the window rather than panic, mirroring
    /// the `SliceOutcome::Aborted` handling in `produce_block`.
    #[tokio::test]
    async fn wait_for_first_slot_skips_on_dropped_parent_ready() {
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(MockBlockstore::new()));

        let slot = Slot::windows().nth(10).unwrap();
        // Drop the sender, exactly as `ParentReadyTracker::prune` does when the slot is pruned;
        // the receiver then resolves to `Err(RecvError)` in the `ParentReady` select branch.
        let (tx, rx) = oneshot::channel::<BlockId>();
        drop(tx);

        let mut pool = MockPool::new();
        pool.expect_wait_for_parent_ready()
            .with(predicate::eq(slot))
            .return_once(move |_slot| Either::Right(rx));
        let pool: SharedPool = Arc::new(RwLock::new(pool));

        let status = wait_for_first_slot(pool, blockstore, slot).await;
        assert!(matches!(status, SlotReady::Skip), "unexpected {status:?}");
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
        let epoch_info = Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(0), epoch_info));
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(blockstore));
        let pool: SharedPool = Arc::new(RwLock::new(pool));
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

        // The producer ingests its own block one slice at a time via the fast
        // path; a single-slice block completes on the only `add_own_slice` call.
        let mut blockstore = MockBlockstore::new();
        let bi = block_info.clone();
        blockstore
            .expect_add_own_slice()
            .times(1)
            .returning(move |_slice, _shreds| {
                let bi = bi.clone();
                Box::pin(async move { Some(bi) })
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
            .unwrap()
            .expect("block should be produced, not aborted");
        assert_eq!(slot, ret.0);
        assert_eq!(block_info.hash, ret.1);
    }

    /// When an optimistic `ParentReady` lands *after* the first slice but confirms a *different*
    /// parent than we guessed, the correction must reach the wire even if the handover arrives on
    /// what would otherwise be the block's last slice: it rides one extra slice rather than being
    /// silently dropped (which would orphan the slot on the stale guessed parent).
    #[tokio::test]
    async fn verify_produce_block_parent_not_ready() {
        let slot = Slot::windows().nth(10).unwrap();
        let slot_hash: BlockHash = Hash::random_for_test().into();
        let old_parent = random_block_id(slot.prev());
        let new_parent = random_block_id(slot.prev().prev());
        let old_block_info = BlockInfo {
            hash: slot_hash.clone(),
            parent: old_parent.clone(),
        };
        let new_block_info = BlockInfo {
            hash: slot_hash,
            parent: new_parent.clone(),
        };

        let (first_slice_finished_tx, first_slice_finished_rx) = oneshot::channel();
        let (start_second_slice_tx, start_second_slice_rx) = oneshot::channel();

        // Records the parent each produced slice carries on the wire, so we can assert the
        // override actually landed rather than trusting the mock's return value.
        let wire_parents: Arc<std::sync::Mutex<Vec<Option<BlockId>>>> = Arc::default();

        let mut seq = Sequence::new();
        let mut blockstore = MockBlockstore::new();

        // First slice: record its parent, signal completion, then block until the parent-ready
        // event has been delivered so the handover deterministically lands on a later slice.
        let rec = wire_parents.clone();
        blockstore
            .expect_add_own_slice()
            .times(1)
            .in_sequence(&mut seq)
            .return_once(move |payload, _shreds| {
                rec.lock().unwrap().push(payload.parent);
                Box::pin(async move {
                    first_slice_finished_tx.send(()).unwrap();
                    let () = start_second_slice_rx.await.unwrap();
                    None
                })
            });

        // Later slices: record each parent and complete the block on whichever slice the producer
        // marks as last (read from the slice header replicated into every shred), not on a fixed
        // slice count — the override rides an extra slice, so the block ends one slice later.
        let rec = wire_parents.clone();
        let nbi = new_block_info.clone();
        blockstore
            .expect_add_own_slice()
            .returning(move |payload, shreds| {
                rec.lock().unwrap().push(payload.parent);
                let is_last = shreds[0].payload().header.is_last;
                let nbi = nbi.clone();
                Box::pin(async move { is_last.then_some(nbi) })
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
        // A non-zero `delta_block` keeps later-slice tx-gathering pending, so the already-delivered
        // parent-ready wins the optimistic race deterministically (rather than racing an
        // immediately-ready empty slice); the first slice still completes promptly.
        let block_producer = setup(
            blockstore,
            pool,
            disseminator,
            Duration::from_millis(10),
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
            .unwrap()
            .expect("block should be produced, not aborted");

        assert_eq!(slot, ret.0);
        assert_eq!(new_block_info.hash, ret.1);

        // The wire proves it: the first slice carries the guessed parent, and exactly one later
        // slice carries the confirmed one — the deferred override, never dropped.
        let wire_parents = std::mem::take(&mut *wire_parents.lock().unwrap());
        assert_eq!(wire_parents.first(), Some(&Some(old_parent)));
        let overrides: Vec<&BlockId> = wire_parents[1..].iter().flatten().collect();
        assert_eq!(overrides, vec![&new_parent]);
    }

    /// If the `ParentReady` sender is dropped while we are optimistically producing (the Pool
    /// pruned the slot after finalization advanced past it), `produce_block` must abort and
    /// return `Ok(None)` rather than swallowing the drop and emitting a block for a moot slot.
    #[tokio::test]
    async fn produce_block_aborts_on_dropped_parent_ready() {
        let slot = Slot::windows().nth(10).unwrap();
        let parent = random_block_id(slot.prev());

        // A dropped sender: the receiver resolves to `Err` when polled, exactly as it would
        // after `ParentReadyTracker::prune` drops the slot's `ParentReadyState`.
        let (parent_ready_tx, parent_ready_rx) = oneshot::channel::<BlockId>();
        drop(parent_ready_tx);

        // Nothing should be shredded, disseminated, or added: the abort fires on the optimistic
        // race for the first slice, before any slice is produced.
        let mut blockstore = MockBlockstore::new();
        blockstore.expect_add_own_slice().never();
        let mut pool = MockPool::new();
        pool.expect_add_block().never();
        let mut disseminator = MockDisseminator::new();
        disseminator.expect_send().never();

        // Long slice budgets so payload production stays pending, making the optimistic race
        // resolve deterministically on the already-dropped `ParentReady` channel.
        let block_producer = setup(
            blockstore,
            pool,
            disseminator,
            Duration::from_secs(100),
            Duration::from_secs(100),
        );

        let ret = block_producer
            .produce_block(slot, parent, Some(parent_ready_rx))
            .await
            .unwrap();
        assert!(
            ret.is_none(),
            "a dropped ParentReady sender must abort production, not emit a block"
        );
    }
}
