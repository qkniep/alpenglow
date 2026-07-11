// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Async driver for the synchronous [`ConsensusCore`].
//!
//! The driver task is the only owner of the [`ConsensusCore`]: it feeds the
//! core [`Input`]s from the shared inbox (filled by the ingest tasks), fires
//! [`Input::Tick`] when the core's next deadline is due, and routes each
//! [`Output`] to the edge that performs the corresponding I/O:
//!
//! - [`Output::Broadcast`] → best-effort [`All2All`] broadcast, inline
//! - [`Output::RequestRepair`] → the repair loop's channel
//! - [`Output::ParentReady`] / [`Output::Finalized`] / [`Output::BlockDisseminated`]
//!   → watch channels observed by the block producer and external callers
//! - [`Output::SliceCommitment`] → the shred-ingest [`CommitmentCache`]
//!
//! The repair loop both consumes repair requests from this task *and* feeds
//! reconstructed blocks back into the inbox, forming the one cycle in the task
//! graph. To keep it deadlock-free, repair requests are never sent blockingly:
//! they are parked in [`Driver::pending_repairs`] and flushed whenever the
//! channel has capacity.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use log::warn;
use tokio::sync::{mpsc, watch};
use tokio_util::sync::CancellationToken;

use super::core::{ConsensusCore, Input, Output};
use crate::crypto::merkle::BlockHash;
use crate::shredder::SliceCommitment;
use crate::types::SliceIndex;
use crate::{All2All, BlockId, Slot};

/// First ready parent per window-start slot, published for the block producer.
pub(crate) type ParentReadyMap = BTreeMap<Slot, BlockId>;

/// Hash of the disseminated block per slot, published for the block producer.
pub(crate) type DisseminatedMap = BTreeMap<Slot, BlockHash>;

/// Edge-side cache of per-slice commitments, populated from
/// [`Output::SliceCommitment`].
///
/// The shred-ingest task reads it to skip signature verification for further
/// shreds of a slice whose commitment the core has already cached. This
/// mirrors the blockstore's internal commitment cache, which the ingest task
/// can no longer read directly now that the blockstore lives inside the core.
///
/// NOTE: entries are never evicted, matching the blockstore itself (whose
/// `prune` has no production caller yet). When blockstore pruning is wired up,
/// this cache should be pruned alongside it.
#[derive(Clone, Default)]
pub(crate) struct CommitmentCache {
    inner: Arc<Mutex<BTreeMap<(Slot, SliceIndex), SliceCommitment>>>,
}

impl CommitmentCache {
    /// Returns the cached commitment for `(slot, slice)`, if any.
    #[must_use]
    pub(crate) fn get(&self, slot: Slot, slice: SliceIndex) -> Option<SliceCommitment> {
        self.lock().get(&(slot, slice)).copied()
    }

    /// Caches `commitment` for `(slot, slice)`.
    fn insert(&self, slot: Slot, slice: SliceIndex, commitment: SliceCommitment) {
        self.lock().insert((slot, slice), commitment);
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, BTreeMap<(Slot, SliceIndex), SliceCommitment>> {
        self.inner.lock().expect("commitment cache mutex poisoned")
    }
}

/// Owns the [`ConsensusCore`] and its I/O edges; see the module docs.
pub(crate) struct Driver<A: All2All> {
    core: ConsensusCore,
    /// Inputs from the ingest tasks (message loop, block producer, repair loop).
    inbox: mpsc::Receiver<Input>,
    /// Network for broadcasting consensus messages to all validators.
    all2all: Arc<A>,
    /// Repair requests destined for the repair loop.
    repairs: mpsc::Sender<BlockId>,
    /// Repair requests waiting for capacity on [`Self::repairs`].
    ///
    /// A set rather than a queue: re-requesting the same block is idempotent,
    /// so duplicates are merged for free.
    pending_repairs: BTreeSet<BlockId>,
    /// Publishes the first ready parent per window, keyed by window-start slot.
    parent_ready: watch::Sender<ParentReadyMap>,
    /// Publishes the disseminated block hash per slot.
    disseminated: watch::Sender<DisseminatedMap>,
    /// Publishes the highest finalized slot.
    finalized: watch::Sender<Slot>,
    /// Shared with the shred-ingest task; updated on [`Output::SliceCommitment`].
    commitments: CommitmentCache,
    /// Indicates whether the node is shutting down.
    cancel_token: CancellationToken,
}

impl<A: All2All> Driver<A> {
    #[expect(clippy::too_many_arguments)]
    pub(crate) fn new(
        core: ConsensusCore,
        inbox: mpsc::Receiver<Input>,
        all2all: Arc<A>,
        repairs: mpsc::Sender<BlockId>,
        parent_ready: watch::Sender<ParentReadyMap>,
        disseminated: watch::Sender<DisseminatedMap>,
        finalized: watch::Sender<Slot>,
        commitments: CommitmentCache,
        cancel_token: CancellationToken,
    ) -> Self {
        Self {
            core,
            inbox,
            all2all,
            repairs,
            pending_repairs: BTreeSet::new(),
            parent_ready,
            disseminated,
            finalized,
            commitments,
            cancel_token,
        }
    }

    /// Runs the driver until shutdown (cancellation or a closed inbox).
    #[fastrace::trace]
    pub(crate) async fn run(mut self) {
        let mut out = Vec::new();
        loop {
            tokio::select! {
                () = self.cancel_token.cancelled() => return,
                input = self.inbox.recv() => match input {
                    Some(input) => self.core.handle(input, Instant::now(), &mut out),
                    None => return,
                },
                () = tokio::time::sleep_until(self.core.next_timeout().into()) => {
                    self.core.handle(Input::Tick, Instant::now(), &mut out);
                }
                // Flush a pending repair request once the channel has capacity.
                // The repair loop also feeds our inbox, so a blocking send here
                // could deadlock the cycle; parking requests keeps this edge
                // non-blocking (see module docs).
                permit = self.repairs.reserve(), if !self.pending_repairs.is_empty() => {
                    if let Ok(permit) = permit {
                        let block_id = self
                            .pending_repairs
                            .pop_first()
                            .expect("pending_repairs is non-empty");
                        permit.send(block_id);
                    }
                }
            }
            for output in out.drain(..) {
                self.route(output).await;
            }
        }
    }

    /// Routes a single core output to its I/O edge.
    ///
    /// Broadcasts are best-effort: a failure of the underlying [`All2All`]
    /// network is logged and otherwise ignored. A transient network error must
    /// not bring down the consensus driver, and a dropped vote/cert is
    /// re-broadcast later via standstill recovery, so a one-off failure
    /// self-heals.
    ///
    /// NOTE: a *persistent* broadcast failure (e.g. a misconfigured firewall or
    /// a full partition) means this node silently stops contributing to
    /// consensus while only logging. Once there is a metrics system, this
    /// should also bump a failure counter so persistent failures become
    /// alertable.
    async fn route(&mut self, output: Output) {
        match output {
            Output::Broadcast(msg) => {
                if let Err(err) = self.all2all.broadcast(&msg).await {
                    warn!("failed to broadcast consensus message: {err}");
                }
            }
            Output::RequestRepair(block_id) => {
                self.pending_repairs.insert(block_id);
            }
            Output::ParentReady { slot, parent } => {
                self.parent_ready.send_modify(|map| {
                    // keep the first ready parent per window; later ones are
                    // alternatives the block producer does not need
                    map.entry(slot).or_insert(parent);
                });
            }
            Output::BlockDisseminated { slot, hash } => {
                self.disseminated.send_modify(|map| {
                    map.entry(slot).or_insert(hash);
                });
            }
            Output::SliceCommitment {
                slot,
                slice,
                commitment,
            } => {
                self.commitments.insert(slot, slice, commitment);
            }
            Output::Finalized(slot) => {
                // prune windows at/below the finalized slot's window start;
                // the block producer no longer needs their parents or blocks
                let window_start = slot.first_slot_in_window();
                self.parent_ready
                    .send_modify(|map| map.retain(|s, _| *s > window_start));
                self.disseminated
                    .send_modify(|map| map.retain(|s, _| *s >= window_start));
                let _ = self.finalized.send(slot);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use async_trait::async_trait;

    use super::super::{ConsensusMessage, Vote};
    use super::*;
    use crate::ValidatorIndex;
    use crate::consensus::ValidatorEpochInfo;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::test_utils::generate_validators;

    /// An [`All2All`] whose `broadcast` always fails, to exercise the driver's
    /// best-effort error handling. `receive` never resolves.
    struct FailingAll2All;

    #[async_trait]
    impl All2All for FailingAll2All {
        async fn broadcast(&self, _msg: &ConsensusMessage) -> std::io::Result<()> {
            Err(std::io::Error::other("simulated broadcast failure"))
        }

        async fn receive(&self) -> std::io::Result<ConsensusMessage> {
            std::future::pending().await
        }
    }

    fn test_driver(
        all2all: Arc<FailingAll2All>,
        inbox: mpsc::Receiver<Input>,
        repairs: mpsc::Sender<BlockId>,
    ) -> Driver<FailingAll2All> {
        let (sks, epoch_info) = generate_validators(2);
        let epoch_info = Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(0), epoch_info));
        let core = ConsensusCore::new(epoch_info, sks[0].clone(), Instant::now());
        let (parent_ready_tx, _) = watch::channel(ParentReadyMap::new());
        let (disseminated_tx, _) = watch::channel(DisseminatedMap::new());
        let (finalized_tx, _) = watch::channel(Slot::genesis());
        Driver::new(
            core,
            inbox,
            all2all,
            repairs,
            parent_ready_tx,
            disseminated_tx,
            finalized_tx,
            CommitmentCache::default(),
            CancellationToken::new(),
        )
    }

    /// A failing network broadcast must be logged and swallowed, never panic
    /// the driver (which has to keep running to preserve liveness).
    #[tokio::test]
    async fn broadcast_failure_does_not_panic() {
        let (_input_tx, input_rx) = mpsc::channel(8);
        let (repair_tx, _repair_rx) = mpsc::channel(8);
        let mut driver = test_driver(Arc::new(FailingAll2All), input_rx, repair_tx);

        let (sks, _) = generate_validators(2);
        let vote = Vote::new_skip(Slot::new(1), &sks[0], ValidatorIndex::new(0));
        driver.route(Output::Broadcast(vote.into())).await;
    }

    /// Repair requests are parked and flushed once the channel has capacity,
    /// never blocking the driver.
    #[tokio::test]
    async fn pending_repairs_flush_on_capacity() {
        let (input_tx, input_rx) = mpsc::channel(8);
        let (repair_tx, mut repair_rx) = mpsc::channel(1);
        let mut driver = test_driver(Arc::new(FailingAll2All), input_rx, repair_tx);

        // fill the repair channel so the first flush has no capacity
        driver
            .repairs
            .try_send((Slot::new(9), GENESIS_BLOCK_HASH))
            .unwrap();

        let b1 = (Slot::new(1), GENESIS_BLOCK_HASH);
        let b2 = (Slot::new(2), GENESIS_BLOCK_HASH);
        driver.route(Output::RequestRepair(b1.clone())).await;
        driver.route(Output::RequestRepair(b2.clone())).await;
        // duplicates merge
        driver.route(Output::RequestRepair(b1.clone())).await;
        assert_eq!(driver.pending_repairs.len(), 2);

        // run the driver; drain the channel and expect the parked requests
        tokio::spawn(driver.run());
        assert_eq!(
            repair_rx.recv().await.unwrap(),
            (Slot::new(9), GENESIS_BLOCK_HASH)
        );
        assert_eq!(repair_rx.recv().await.unwrap(), b1);
        assert_eq!(repair_rx.recv().await.unwrap(), b2);
        // closing the inbox shuts the driver down
        drop(input_tx);
    }

    /// The first ready parent per window wins; later alternatives are ignored.
    #[tokio::test]
    async fn parent_ready_keeps_first_parent() {
        let (_input_tx, input_rx) = mpsc::channel(8);
        let (repair_tx, _repair_rx) = mpsc::channel(8);
        let mut driver = test_driver(Arc::new(FailingAll2All), input_rx, repair_tx);
        let mut watch_rx = driver.parent_ready.subscribe();

        let slot = Slot::new(4);
        let first = (Slot::new(1), GENESIS_BLOCK_HASH);
        let second = (Slot::new(2), GENESIS_BLOCK_HASH);
        driver
            .route(Output::ParentReady {
                slot,
                parent: first.clone(),
            })
            .await;
        driver
            .route(Output::ParentReady {
                slot,
                parent: second,
            })
            .await;
        assert_eq!(watch_rx.borrow_and_update().get(&slot), Some(&first));
    }
}
