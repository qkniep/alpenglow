// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parallel shred signature verification stage.
//!
//! Sits between the network receive path and the consumers (Rotor relay
//! forwarding, blockstore ingest). Raw [`Shred`]s are submitted via
//! [`ShredVerifier::submit`], distributed round-robin across a fixed pool of
//! worker tasks that run [`ValidatedShred::try_new`], and successfully
//! verified shreds are emitted on the receiver returned from
//! [`ShredVerifier::spawn`]. Shreds with bad signatures are dropped silently.
//!
//! Workers share a [`SliceRootCache`] that records the first verified Merkle
//! root seen for each (slot, slice). On a cache hit the Ed25519 verify is
//! skipped — the cached root already carries a verified leader signature, and
//! a matching derived root means this shred is covered by the same signature.
//!
//! Once a worker observes a second distinct valid root for any slice in a
//! slot, the leader is provably equivocating for that slot. The cache marks
//! the slot equivocated and subsequent shreds for it are dropped before
//! verify — the blockstore would reject them via `leader_misbehaved`
//! anyway, and absent this short-circuit a Byzantine leader could force a
//! full Ed25519 verify per shred by spamming distinct-but-valid root sigs.
//! The two shreds that exposed the equivocation are still forwarded so the
//! blockstore sees both signatures and updates its own state.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use moka::sync::Cache;
use tokio::sync::mpsc;
use tokio_util::sync::CancellationToken;

use crate::Slot;
use crate::consensus::ValidatorEpochInfo;
use crate::crypto::merkle::SliceRoot;
use crate::shredder::{Shred, ValidatedShred};
use crate::types::SliceIndex;

/// Number of worker tasks running shred signature verification in parallel.
pub const NUM_VERIFY_WORKERS: usize = 4;

/// Bound on each worker's input queue and on the verified-shred output queue.
const VERIFY_QUEUE_SIZE: usize = 1024;

/// Maximum number of (slot, slice) → root entries kept in the shared cache.
/// Each entry is ~50 bytes, so this caps the cache at a few megabytes.
/// Entries are evicted LRU by moka, which is fine: cache misses just fall
/// back to the full Ed25519 verify.
const CACHE_CAPACITY: u64 = 100_000;

/// Cap on the per-slot equivocation set. Entries are only inserted when a
/// slot is proven equivocating, which is rare, so this only needs to bound
/// pathological growth.
const EQUIVOCATED_SLOTS_CAPACITY: u64 = 4_096;

/// Concurrent cache shared by the verifier workers.
///
/// Has two parts:
///   * `roots`: the first verified Merkle root we saw per (slot, slice).
///     Used to short-circuit Ed25519 verify when a subsequent shred derives
///     the same root.
///   * `equivocated_slots`: slots for which we observed two distinct valid
///     roots for some slice — i.e. proof of leader equivocation. Workers
///     drop incoming shreds for these slots without verifying.
pub struct SliceRootCache {
    roots: Cache<(Slot, SliceIndex), SliceRoot>,
    equivocated_slots: Cache<Slot, ()>,
}

impl SliceRootCache {
    #[must_use]
    pub fn new() -> Self {
        Self {
            roots: Cache::new(CACHE_CAPACITY),
            equivocated_slots: Cache::new(EQUIVOCATED_SLOTS_CAPACITY),
        }
    }

    pub fn get(&self, slot: Slot, slice: SliceIndex) -> Option<SliceRoot> {
        self.roots.get(&(slot, slice))
    }

    /// Inserts only if no entry exists yet for this key — keeps the
    /// first-seen verified root authoritative.
    pub fn insert_if_absent(&self, slot: Slot, slice: SliceIndex, root: SliceRoot) {
        let key = (slot, slice);
        if self.roots.get(&key).is_none() {
            self.roots.insert(key, root);
        }
    }

    pub fn is_slot_equivocated(&self, slot: Slot) -> bool {
        self.equivocated_slots.get(&slot).is_some()
    }

    pub fn mark_slot_equivocated(&self, slot: Slot) {
        self.equivocated_slots.insert(slot, ());
    }
}

impl Default for SliceRootCache {
    fn default() -> Self {
        Self::new()
    }
}

/// A pool of worker tasks that verify [`Shred`] signatures in parallel.
///
/// See the module-level docs for the overall pipeline shape.
pub struct ShredVerifier {
    /// Per-worker input channels. Shreds submitted via [`Self::submit`] are
    /// round-robin'd across these.
    worker_txs: Vec<mpsc::Sender<Shred>>,
    /// Round-robin counter for `submit`.
    next: AtomicUsize,
}

impl ShredVerifier {
    /// Spawns `num_workers` verifier tasks and returns the verifier handle
    /// together with the receiver downstream consumers should pull verified
    /// shreds from.
    pub fn spawn(
        num_workers: usize,
        epoch_info: Arc<ValidatorEpochInfo>,
        cancel_token: CancellationToken,
    ) -> (Self, mpsc::Receiver<ValidatedShred>) {
        assert!(num_workers > 0);
        let (output_tx, output_rx) = mpsc::channel(VERIFY_QUEUE_SIZE);
        let cache = Arc::new(SliceRootCache::new());
        let mut worker_txs = Vec::with_capacity(num_workers);
        for _ in 0..num_workers {
            let (input_tx, input_rx) = mpsc::channel(VERIFY_QUEUE_SIZE);
            worker_txs.push(input_tx);
            let output_tx = output_tx.clone();
            let epoch_info = epoch_info.clone();
            let cache = cache.clone();
            let cancel_token = cancel_token.clone();
            tokio::spawn(async move {
                Self::worker(input_rx, output_tx, epoch_info, cache, cancel_token).await
            });
        }
        let verifier = Self {
            worker_txs,
            next: AtomicUsize::new(0),
        };
        (verifier, output_rx)
    }

    /// Submits a shred for verification. Awaits if the chosen worker's queue
    /// is full (bounded backpressure to the caller).
    pub async fn submit(&self, shred: Shred) {
        let i = self.next.fetch_add(1, Ordering::Relaxed) % self.worker_txs.len();
        // Send failures only occur if the worker task has terminated, which only
        // happens on shutdown; drop the shred in that case.
        let _ = self.worker_txs[i].send(shred).await;
    }

    async fn worker(
        mut input_rx: mpsc::Receiver<Shred>,
        output_tx: mpsc::Sender<ValidatedShred>,
        epoch_info: Arc<ValidatorEpochInfo>,
        cache: Arc<SliceRootCache>,
        cancel_token: CancellationToken,
    ) {
        loop {
            tokio::select! {
                res = input_rx.recv() => {
                    let Some(shred) = res else { break };
                    let slot = shred.payload().header.slot;
                    let slice = shred.payload().header.slice_index;

                    // Slots known to have already produced equivocating shreds
                    // are dropped without Ed25519 verify, so a Byzantine leader
                    // can't force unbounded sig-verify work by spamming distinct
                    // valid roots once two have been observed.
                    if cache.is_slot_equivocated(slot) {
                        continue;
                    }

                    let leader_pk = epoch_info.epoch_info().leader(slot).pubkey;
                    let cached = cache.get(slot, slice);
                    let Ok(validated) = ValidatedShred::try_new(shred, cached.as_ref(), &leader_pk)
                    else {
                        continue;
                    };

                    match cached {
                        None => {
                            cache.insert_if_absent(
                                slot,
                                slice,
                                validated.merkle_root().clone(),
                            );
                        }
                        Some(prev) if &prev != validated.merkle_root() => {
                            // Two distinct valid roots for the same slice — the
                            // leader is provably equivocating for this slot.
                            // Forward this shred too so the blockstore sees
                            // both signatures, then mark the slot so future
                            // shreds short-circuit before verify.
                            cache.mark_slot_equivocated(slot);
                        }
                        Some(_) => {}
                    }

                    if output_tx.send(validated).await.is_err() {
                        break;
                    }
                }
                () = cancel_token.cancelled() => break,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::time::Duration;

    use tokio::time::timeout;

    use super::*;
    use crate::consensus::EpochInfo;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::network::dontcare_sockaddr;
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, TOTAL_SHREDS};
    use crate::types::slice::create_slice_with_invalid_txs;
    use crate::{Stake, ValidatorId, ValidatorInfo};

    /// Build a single-validator epoch info whose Ed25519 key matches `sk`,
    /// so any shred signed by `sk` verifies against `leader(slot).pubkey`.
    fn single_validator_epoch(sk: &SecretKey) -> Arc<ValidatorEpochInfo> {
        let id = ValidatorId::new(0);
        let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
        let info = ValidatorInfo {
            id,
            stake: Stake::new(1),
            pubkey: sk.to_pk(),
            voting_pubkey: voting_sk.to_pk(),
            all2all_address: dontcare_sockaddr(),
            disseminator_address: dontcare_sockaddr(),
            repair_request_address: dontcare_sockaddr(),
            repair_response_address: dontcare_sockaddr(),
        };
        Arc::new(ValidatorEpochInfo::new(id, EpochInfo::new(vec![info])))
    }

    fn shredded_slice() -> (Vec<ValidatedShred>, SecretKey) {
        let mut shredder = RegularShredder::default();
        let sk = SecretKey::new(&mut rand::rng());
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let shreds = shredder.shred(slice, &sk).unwrap().to_vec();
        (shreds, sk)
    }

    #[tokio::test]
    async fn verifies_valid_shred() {
        let (shreds, sk) = shredded_slice();
        let epoch_info = single_validator_epoch(&sk);
        let (verifier, mut rx) = ShredVerifier::spawn(2, epoch_info, CancellationToken::new());

        let original = shreds[0].clone().into_shred();
        let expected_root = shreds[0].merkle_root().clone();
        verifier.submit(original).await;

        let validated = timeout(Duration::from_secs(1), rx.recv())
            .await
            .expect("verifier should emit a result")
            .expect("output channel still open");
        assert_eq!(validated.merkle_root(), &expected_root);
    }

    #[tokio::test]
    async fn drops_shred_with_bad_signature() {
        let (shreds, sk) = shredded_slice();
        let epoch_info = single_validator_epoch(&sk);
        let (verifier, mut rx) = ShredVerifier::spawn(2, epoch_info, CancellationToken::new());

        // Corrupt the payload so the derived Merkle root no longer matches the
        // signed one. The worker should drop this silently.
        let mut bad = shreds[0].clone().into_shred();
        bad.payload_mut().data.fill(0);
        verifier.submit(bad).await;

        // Send a valid shred afterward so we can prove the worker is alive
        // and the bad one was dropped rather than buffered.
        let good = shreds[1].clone().into_shred();
        let good_root = shreds[1].merkle_root().clone();
        verifier.submit(good).await;

        let validated = timeout(Duration::from_secs(1), rx.recv())
            .await
            .expect("verifier should emit the good shred")
            .unwrap();
        assert_eq!(validated.merkle_root(), &good_root);
        // No second emission should appear (corrupt shred was dropped).
        assert!(timeout(Duration::from_millis(50), rx.recv()).await.is_err());
    }

    #[tokio::test]
    async fn distributes_across_workers() {
        let (shreds, sk) = shredded_slice();
        let epoch_info = single_validator_epoch(&sk);
        let (verifier, mut rx) = ShredVerifier::spawn(4, epoch_info, CancellationToken::new());

        let expected_roots: HashSet<_> = shreds
            .iter()
            .map(|s| s.merkle_root().clone())
            .collect();
        // All shreds in a single slice share the same root, but the per-shred
        // path through different workers should each emit one verified shred.
        let expected_count = shreds.len();
        for shred in shreds {
            verifier.submit(shred.into_shred()).await;
        }

        let mut seen_roots = HashSet::new();
        let mut received = 0;
        while received < expected_count {
            let validated = timeout(Duration::from_secs(1), rx.recv())
                .await
                .expect("verifier should keep emitting")
                .unwrap();
            seen_roots.insert(validated.merkle_root().clone());
            received += 1;
        }
        assert_eq!(received, TOTAL_SHREDS);
        assert_eq!(seen_roots, expected_roots);
    }

    #[tokio::test]
    async fn equivocation_short_circuits_further_shreds() {
        // Produce two distinct slices for the same slot signed by the same
        // leader: each constitutes a different valid Merkle root, so feeding
        // shreds from both proves equivocation.
        let mut shredder = RegularShredder::default();
        let sk = SecretKey::new(&mut rand::rng());
        let slot = crate::Slot::new(1);
        let mut slice_a = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let mut slice_b = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        // Force both slices into the same (slot, slice_index) so the cache
        // treats them as competing roots for the same slot.
        slice_a.slot = slot;
        slice_b.slot = slot;
        let shreds_a = shredder.shred(slice_a, &sk).unwrap();
        let shreds_b = shredder.shred(slice_b, &sk).unwrap();
        assert_ne!(shreds_a[0].merkle_root(), shreds_b[0].merkle_root());

        let epoch_info = single_validator_epoch(&sk);
        // Single worker so submission order is also processing order.
        let (verifier, mut rx) =
            ShredVerifier::spawn(1, epoch_info, CancellationToken::new());

        // First shred (root A) goes through, caches A.
        verifier.submit(shreds_a[0].clone().into_shred()).await;
        // Second shred with a different valid root (root B) goes through,
        // and triggers the slot-equivocated mark.
        verifier.submit(shreds_b[0].clone().into_shred()).await;
        // A third shred with yet another root would now be dropped before
        // any sig verify. We simulate that by feeding more of slice B's
        // shreds; once the slot is marked equivocated they should all drop.
        for shred in shreds_b.iter().skip(1).take(3) {
            verifier.submit(shred.clone().into_shred()).await;
        }

        // We expect exactly two emissions (the equivocation exposure).
        let _first = timeout(Duration::from_secs(1), rx.recv())
            .await
            .expect("first")
            .unwrap();
        let _second = timeout(Duration::from_secs(1), rx.recv())
            .await
            .expect("second")
            .unwrap();
        // No further shreds should arrive — they're dropped pre-verify.
        assert!(timeout(Duration::from_millis(100), rx.recv()).await.is_err());
    }

    #[tokio::test]
    async fn cancellation_shuts_workers_down() {
        let (shreds, sk) = shredded_slice();
        let epoch_info = single_validator_epoch(&sk);
        let cancel_token = CancellationToken::new();
        let (_verifier, mut rx) =
            ShredVerifier::spawn(2, epoch_info, cancel_token.clone());

        // Cancel without submitting anything; the workers should exit and
        // the output channel's senders should be dropped, closing rx.
        cancel_token.cancel();
        // Workers also drop their output_tx clones; once all clones drop, recv
        // returns None. Give the runtime a moment to process the cancellation.
        let res = timeout(Duration::from_secs(1), rx.recv()).await;
        assert!(matches!(res, Ok(None)), "expected closed channel, got {res:?}");

        // Sanity: shreds aren't needed for this assertion but make sure their
        // construction didn't side-channel anything (e.g. waited on cancel).
        drop(shreds);
    }
}
