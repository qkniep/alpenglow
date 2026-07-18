// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure handling votes and certificates.
//!
//! Any received votes or certificates are placed into the pool.
//! The pool then tracks status for each slot and sends notification to votor.

mod finality_tracker;
mod parent_ready_tracker;
mod slot_state;
mod sorted_vec;

use std::collections::BTreeMap;
use std::ops::RangeBounds;
use std::sync::Arc;

use async_trait::async_trait;
use either::Either;
use log::{debug, info, trace, warn};
use thiserror::Error;
use tokio::sync::{RwLock, oneshot};

use self::finality_tracker::FinalityTracker;
use self::parent_ready_tracker::ParentReadyTracker;
use self::slot_state::{IgnoreReason, SlotState};
use super::{Cert, ValidatedCert, ValidatedVote, ValidatorEpochInfo, Vote};
use crate::consensus::cert::NotarCert;
use crate::consensus::pool::finality_tracker::FinalizationEvent;
use crate::crypto::merkle::BlockHash;
use crate::types::SLOTS_PER_EPOCH;
use crate::{BlockId, Slot, ValidatorIndex};

/// Events emitted by [`PoolImpl`] to [`Votor`].
///
/// [`Votor`]: crate::consensus::votor::Votor
// PERF: Short-lived channel message; boxing the cert isn't worth the allocation.
#[expect(clippy::large_enum_variant)]
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum PoolEvent {
    /// Pool newly marked the given block as a ready `parent` for `slot`.
    ///
    /// This event is only emitted per window, `slot` is always the first slot.
    ParentReady { slot: Slot, parent: BlockId },
    /// The given block has reached the safe-to-notar status.
    SafeToNotar(BlockId),
    /// The given slot has reached the safe-to-skip status.
    SafeToSkip(Slot),
    /// New certificate created in pool (should then be broadcast by Votor).
    CertCreated(Cert),
    /// Standstill timeout has fired.
    ///
    /// The provided slot indicates the highest finalized slot as seen by Pool.
    /// The provided certificates and votes should be re-broadcast.
    Standstill(Slot, Vec<Cert>, Vec<Vote>),
}

impl PoolEvent {
    /// Returns the slot this event refers to.
    pub(crate) const fn slot(&self) -> Slot {
        match self {
            Self::ParentReady { slot, .. }
            | Self::SafeToNotar((slot, _))
            | Self::SafeToSkip(slot)
            | Self::Standstill(slot, _, _) => *slot,
            Self::CertCreated(cert) => cert.slot(),
        }
    }
}

/// A single side-effect the Pool buffered while processing under its write lock.
// PERF: Short-lived outbox entry, moved out on drain; boxing isn't worth the allocation.
#[expect(clippy::large_enum_variant)]
#[derive(Clone, Debug)]
pub enum PoolEffect {
    /// An event destined for Votor.
    VotorEvent(PoolEvent),
    /// A request to repair the given block, destined for the repair loop.
    Repair(BlockId),
}

/// Side-effects the Pool produces while processing under its write lock, to be
/// drained via [`Pool::take_outbox`] and forwarded to Votor and the repair loop
/// once the lock is released (a blocking send under the lock would jam every task
/// contending for it).
///
/// Effects are kept in the single order the Pool produced them. Splitting them
/// into a per-destination queue would reorder the two against each other, e.g.
/// delaying the repair request for a newly certified block behind every Votor
/// event that certification produced.
#[derive(Debug, Default)]
#[must_use = "buffered effects are lost unless forwarded, see `EventForwarder::forward_pool_outbox`"]
pub struct PoolOutbox {
    /// Buffered effects, in the order the Pool produced them.
    pub effects: Vec<PoolEffect>,
}

/// Errors the Pool may return when adding a vote.
///
/// Signature and signer validity are checked up front by [`ValidatedVote`],
/// so they are not represented here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum AddVoteError {
    #[error("slot is either too old or too far in the future")]
    SlotOutOfBounds,
    #[error("duplicate vote")]
    Duplicate,
    #[error("vote constitutes a slashable offence")]
    Slashable(SlashableOffence),
}

/// Errors the Pool may return when adding a certificate.
///
/// Signature validity and stake threshold are checked up front by [`ValidatedCert`],
/// so they are not represented here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum AddCertError {
    #[error("slot is either too old or too far in the future")]
    SlotOutOfBounds,
    #[error("duplicate cert")]
    Duplicate,
}

/// Slashable offences that may be detected by the Pool.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum SlashableOffence {
    #[error("Validator {0} already voted notar on slot {1} for a different hash")]
    NotarDifferentHash(ValidatorIndex, Slot),
    #[error("Validator {0} voted both skip and notarize on slot {1}")]
    SkipAndNotarize(ValidatorIndex, Slot),
    #[error("Validator {0} voted both skip(-fallback) and finalize on slot {1}")]
    SkipAndFinalize(ValidatorIndex, Slot),
    #[error("Validator {0} voted both notar-fallback and finalize on slot {1}")]
    NotarFallbackAndFinalize(ValidatorIndex, Slot),
}

/// Interface for the Pool.
///
/// This is only used for mocking of [`PoolImpl`].
#[async_trait]
#[cfg_attr(test, mockall::automock)]
pub trait Pool {
    async fn add_cert(&mut self, cert: ValidatedCert) -> Result<(), AddCertError>;
    async fn add_vote(&mut self, vote: ValidatedVote) -> Result<(), AddVoteError>;
    async fn add_block(&mut self, block_id: BlockId, parent_id: BlockId);
    /// Builds the standstill-recovery bundle to re-broadcast; see [`PoolImpl::recover_from_standstill`].
    fn recover_from_standstill(&self) -> PoolOutbox;
    /// Drains and returns the side-effects buffered since the last call.
    ///
    /// The caller must forward these to Votor and the repair loop *after* releasing
    /// the Pool lock; see `PoolImpl::enqueue_votor_event`.
    fn take_outbox(&mut self) -> PoolOutbox;
    fn finalized_slot(&self) -> Slot;
    fn parents_ready(&self, slot: Slot) -> &[BlockId];
    fn wait_for_parent_ready(&mut self, slot: Slot) -> Either<BlockId, oneshot::Receiver<BlockId>>;
}

/// Shared, lock-protected handle to a [`Pool`] trait object.
pub type SharedPool = Arc<RwLock<dyn Pool + Send + Sync>>;

/// Pool is the central consensus data structure.
///
/// It holds votes and certificates for each slot.
///
/// This is the main implementation to use when you require the [`Pool`] trait.
pub struct PoolImpl {
    /// State for each slot. Stores all votes and certificates.
    slot_states: BTreeMap<Slot, SlotState>,
    /// Keeps track of which slots have a parent ready.
    parent_ready_tracker: ParentReadyTracker,
    /// Keeps track of which slots are finalized.
    finality_tracker: FinalityTracker,
    /// Keeps track of safe-to-notar blocks waiting for a parent certificate.
    s2n_waiting_parent_cert: BTreeMap<BlockId, BlockId>,

    /// Information about all active validators.
    epoch_info: Arc<ValidatorEpochInfo>,
    /// Buffered side-effects (Votor events + repair requests) produced under the
    /// write lock, drained by the caller via [`Pool::take_outbox`].
    outbox: PoolOutbox,
}

impl PoolImpl {
    /// Creates a new empty pool containing no votes or certificates.
    ///
    /// Any events the pool emits are buffered in its [`PoolOutbox`] and must be
    /// drained by the caller via [`Pool::take_outbox`], then forwarded to Votor and
    /// the repair loop after the write lock is released; see
    /// `PoolImpl::enqueue_votor_event`.
    pub fn new(epoch_info: Arc<ValidatorEpochInfo>) -> Self {
        Self {
            slot_states: BTreeMap::new(),
            parent_ready_tracker: ParentReadyTracker::default(),
            finality_tracker: FinalityTracker::default(),
            s2n_waiting_parent_cert: BTreeMap::new(),
            epoch_info,
            outbox: PoolOutbox::default(),
        }
    }

    /// Adds a new certificate to the pool. Certificate is assumed to be valid.
    ///
    /// Caller needs to ensure that the certificate passes all validity checks:
    /// - slot is not too old or too far in the future
    /// - signature is valid
    /// - certificate is not a duplicate
    async fn add_valid_cert(&mut self, cert: Cert) {
        let slot = cert.slot();

        // actually add certificate
        trace!("adding cert to pool: {cert:?}");
        self.slot_state(slot).add_cert(cert.clone());

        // handle resulting state updates
        match &cert {
            Cert::Notar(_) | Cert::NotarFallback(_) => {
                let block_hash = cert
                    .block_hash()
                    .cloned()
                    .expect("notar(-fallback) cert always references a block");
                let block_id = (slot, block_hash.clone());
                info!(
                    "notarized(-fallback) block {} in slot {}",
                    block_hash.short_hex(),
                    slot
                );
                if matches!(cert, Cert::Notar(_)) {
                    let finalization_event = self.finality_tracker.mark_notarized(block_id.clone());
                    self.handle_finalization(finalization_event).await;
                }

                // potentially notify child waiting for safe-to-notar
                if let Some((child_slot, child_hash)) =
                    self.s2n_waiting_parent_cert.remove(&block_id)
                    && let Some(output) = self
                        .slot_state(child_slot)
                        .notify_parent_certified(child_hash)
                {
                    match output {
                        Either::Left(event) => self.enqueue_votor_event(event),
                        Either::Right((slot, hash)) => self.enqueue_repair((slot, hash)),
                    }
                }

                // add block to parent-ready tracker, send any new parents to Votor.
                let new_parents_ready = self.parent_ready_tracker.mark_notar_fallback(&block_id);
                self.send_parent_ready_events(new_parents_ready);

                // repair this block, if necessary
                self.enqueue_repair((slot, block_hash));
            }
            Cert::Skip(_) => {
                warn!("skipped slot {slot}");
                let new_parents_ready = self.parent_ready_tracker.mark_skipped(slot);
                self.send_parent_ready_events(new_parents_ready);
            }
            Cert::FastFinal(ff_cert) => {
                info!("fast finalized slot {slot}");
                let hash = ff_cert.block_hash().clone();
                let finalization_event = self.finality_tracker.mark_fast_finalized((slot, hash));
                self.handle_finalization(finalization_event).await;
            }
            Cert::Final(_) => {
                info!("slow finalized slot {slot}");
                let finalization_event = self.finality_tracker.mark_finalized(slot);
                self.handle_finalization(finalization_event).await;
            }
        }

        // send to votor for broadcasting
        let event = PoolEvent::CertCreated(cert);
        self.enqueue_votor_event(event);
    }

    /// Mutably accesses the [`SlotState`] for the given `slot`.
    ///
    /// Creates a new [`SlotState`] if none exists yet.
    fn slot_state(&mut self, slot: Slot) -> &mut SlotState {
        self.slot_states
            .entry(slot)
            .or_insert_with(|| SlotState::new(slot, Arc::clone(&self.epoch_info)))
    }

    /// Fetches all certificates for the provided range of `slots`.
    fn get_certs(&self, slots: impl RangeBounds<Slot>) -> Vec<Cert> {
        let mut certs = Vec::new();
        for (_, slot_state) in self.slot_states.range(slots) {
            if let Some(cert) = slot_state.certificates.finalize.clone() {
                certs.push(Cert::Final(cert));
            }
            if let Some(cert) = slot_state.certificates.fast_finalize.clone() {
                certs.push(Cert::FastFinal(cert));
            }
            if let Some(cert) = slot_state.certificates.notar.clone() {
                certs.push(Cert::Notar(cert));
            }
            for cert in slot_state.certificates.notar_fallback.iter().cloned() {
                certs.push(Cert::NotarFallback(cert));
            }
            if let Some(cert) = slot_state.certificates.skip.clone() {
                certs.push(Cert::Skip(cert));
            }
        }
        certs
    }

    /// Fetches finalization certificates for given `slot`, if any.
    ///
    /// Prefers fast-finalization over slow-finalization, if it's available.
    /// In that case this returns only the fast-finalization certificate.
    /// Otherwise, returns the finalization and notarization certificates.
    fn get_final_certs(&self, slot: Slot) -> Vec<Cert> {
        let Some(slot_state) = self.slot_states.get(&slot) else {
            return Vec::new();
        };
        if let Some(ff_cert) = &slot_state.certificates.fast_finalize {
            return vec![Cert::FastFinal(ff_cert.clone())];
        }
        if let Some(final_cert) = &slot_state.certificates.finalize
            && let Some(notar_cert) = &slot_state.certificates.notar
        {
            return vec![
                Cert::Final(final_cert.clone()),
                Cert::Notar(notar_cert.clone()),
            ];
        }
        Vec::new()
    }

    /// Fetches all votes cast by myself for the provided range of `slots`.
    fn get_own_votes(&self, slots: impl RangeBounds<Slot>) -> Vec<Vote> {
        let mut votes = Vec::new();
        let own_id = self.epoch_info.own_id();
        for (_, slot_state) in self.slot_states.range(slots) {
            if let Some(vote) = &slot_state.votes.finalize[own_id.as_usize()] {
                votes.push(Vote::Final(vote.clone()));
            }
            if let Some(vote) = &slot_state.votes.notar[own_id.as_usize()] {
                votes.push(Vote::Notar(vote.clone()));
            }
            for vote in slot_state.votes.notar_fallback[own_id.as_usize()].values() {
                votes.push(Vote::NotarFallback(vote.clone()));
            }
            if let Some(vote) = &slot_state.votes.skip[own_id.as_usize()] {
                votes.push(Vote::Skip(vote.clone()));
            }
            if let Some(vote) = &slot_state.votes.skip_fallback[own_id.as_usize()] {
                votes.push(Vote::SkipFallback(vote.clone()));
            }
        }
        votes
    }

    /// Cleans up state for slots that the finality tracker has pruned.
    ///
    /// After this, [`Self::slot_states`] only contains entries for slots at or
    /// above [`Self::first_unpruned_slot`] = [`FinalityTracker::first_unpruned_slot`].
    fn prune(&mut self) {
        let first_unpruned_slot = self.first_unpruned_slot();
        self.slot_states = self.slot_states.split_off(&first_unpruned_slot);
        self.parent_ready_tracker.prune(first_unpruned_slot);
        // NOTE: The finality tracker prunes its own state internally.
    }

    /// Returns the first slot whose state has not been pruned.
    ///
    /// Everything before this slot is decided;
    /// certificates and votes for those slots can be safely ignored.
    fn first_unpruned_slot(&self) -> Slot {
        self.finality_tracker.first_unpruned_slot()
    }

    /// Returns `true` iff the given parent is ready for the given slot.
    ///
    /// This requires that the parent is at least notarized-fallback.
    /// Also, if the parent is in a slot before `slot-1`, then all slots in
    /// `parent+1..slot-1` (inclusive) must be skip-certified.
    pub fn is_parent_ready(&self, slot: Slot, parent: &BlockId) -> bool {
        self.parent_ready_tracker
            .parents_ready(slot)
            .contains(parent)
    }

    /// Returns `true` iff the pool contains a notar(-fallback) certificate for the slot.
    pub fn has_notar_or_fallback_cert(&self, slot: Slot) -> bool {
        self.slot_states.get(&slot).is_some_and(|state| {
            state.certificates.notar.is_some() || !state.certificates.notar_fallback.is_empty()
        })
    }

    /// Returns the hash of the notarized block for the given slot, if any.
    pub fn get_notarized_block(&self, slot: Slot) -> Option<&BlockHash> {
        self.slot_states
            .get(&slot)
            .and_then(|state| state.certificates.notar.as_ref().map(NotarCert::block_hash))
    }

    /// Returns `true` iff the pool contains a (fast) finalization certificate for the slot.
    pub fn has_final_cert(&self, slot: Slot) -> bool {
        self.slot_states.get(&slot).is_some_and(|state| {
            state.certificates.fast_finalize.is_some() || state.certificates.finalize.is_some()
        })
    }

    /// Returns `true` iff the pool contains a notarization certificate for the slot.
    pub fn has_notar_cert(&self, slot: Slot) -> bool {
        self.slot_states
            .get(&slot)
            .is_some_and(|state| state.certificates.notar.is_some())
    }

    /// Returns `true` iff the pool contains a skip certificate for the slot.
    pub fn has_skip_cert(&self, slot: Slot) -> bool {
        self.slot_states
            .get(&slot)
            .is_some_and(|state| state.certificates.skip.is_some())
    }

    async fn handle_finalization(&mut self, event: FinalizationEvent) {
        let new_parents_ready = self.parent_ready_tracker.handle_finalization(event);
        self.send_parent_ready_events(new_parents_ready);
        self.prune();
    }

    fn send_parent_ready_events(&mut self, parents: impl IntoIterator<Item = (Slot, BlockId)>) {
        for (slot, parent) in parents {
            debug_assert!(slot.is_start_of_window());
            self.enqueue_votor_event(PoolEvent::ParentReady { slot, parent });
        }
    }

    /// Records an event for Votor in the outbox.
    ///
    /// Buffered rather than sent so the caller can forward it off the write lock
    /// (see [`super::EventForwarder`]); a blocking send under the lock would jam
    /// every task contending for it.
    fn enqueue_votor_event(&mut self, event: PoolEvent) {
        self.outbox.effects.push(PoolEffect::VotorEvent(event));
    }

    /// Records a repair request for the given block in the outbox.
    ///
    /// Buffered rather than sent, for the same reason as
    /// [`Self::enqueue_votor_event`].
    fn enqueue_repair(&mut self, block_id: BlockId) {
        self.outbox.effects.push(PoolEffect::Repair(block_id));
    }
}

#[async_trait]
impl Pool for PoolImpl {
    /// Adds a new certificate to the pool.
    #[hotpath::measure]
    async fn add_cert(&mut self, cert: ValidatedCert) -> Result<(), AddCertError> {
        // ignore old and far-in-the-future certificates
        let slot = cert.slot();
        // TODO: set bounds exactly correctly
        let slot_far_in_future = Slot::new(self.finalized_slot().inner() + 2 * SLOTS_PER_EPOCH);
        if slot < self.first_unpruned_slot() || slot >= slot_far_in_future {
            return Err(AddCertError::SlotOutOfBounds);
        }

        let cert = cert.into_cert();

        // check if the certificate is a duplicate
        let certs = &mut self.slot_state(slot).certificates;
        let duplicate = match &cert {
            Cert::Notar(_) => certs.notar.is_some(),
            Cert::NotarFallback(nf_cert) => certs
                .notar_fallback
                .iter()
                .any(|nf| nf.block_hash() == nf_cert.block_hash()),
            Cert::Skip(_) => certs.skip.is_some(),
            Cert::FastFinal(_) => certs.fast_finalize.is_some(),
            Cert::Final(_) => certs.finalize.is_some(),
        };
        if duplicate {
            return Err(AddCertError::Duplicate);
        }

        self.add_valid_cert(cert).await;
        Ok(())
    }

    /// Adds a new vote to the pool.
    #[hotpath::measure]
    async fn add_vote(&mut self, vote: ValidatedVote) -> Result<(), AddVoteError> {
        // ignore old and far-in-the-future votes
        let slot = vote.slot();
        // TODO: set bounds exactly correctly
        let slot_far_in_future = Slot::new(self.finalized_slot().inner() + 2 * SLOTS_PER_EPOCH);
        if slot < self.first_unpruned_slot() || slot >= slot_far_in_future {
            return Err(AddVoteError::SlotOutOfBounds);
        }

        let vote = vote.into_vote();

        // check if vote is valid and should be counted
        let voter = vote.signer();
        // NOTE: `ValidatedVote` already checked the signer and signature
        let voter_stake = self.epoch_info.epoch_info().validator(voter).stake;
        let slot_state = self.slot_state(slot);
        if let Some(offence) = slot_state.check_slashable_offence(&vote) {
            return Err(AddVoteError::Slashable(offence));
        } else if let Some(reason) = slot_state.should_ignore_vote(&vote) {
            match reason {
                IgnoreReason::Duplicate => {}
                IgnoreReason::SkipSkipFallback => {
                    debug!("validator {voter} cast both skip and skip-fallback in slot {slot}");
                }
                IgnoreReason::NotarNotarFallback => {
                    debug!(
                        "validator {voter} cast both notar and notar-fallback for the same block in slot {slot}"
                    );
                }
            }
            return Err(AddVoteError::Duplicate);
        }

        // actually add the vote
        trace!("adding vote to pool: {vote:?}");
        let (new_certs, votor_events, blocks_to_repair) = slot_state.add_vote(vote, voter_stake);

        // handle any resulting events
        for cert in new_certs {
            self.add_valid_cert(cert).await;
        }
        for event in votor_events {
            self.enqueue_votor_event(event);
        }
        for (slot, block_hash) in blocks_to_repair {
            self.enqueue_repair((slot, block_hash));
        }
        Ok(())
    }

    /// Registers a new block with its respective parent in the pool.
    ///
    /// This should be called once for every valid block (e.g. directly by blockstore).
    /// Ensures that the parent information is available for safe-to-notar checks.
    async fn add_block(&mut self, block_id: BlockId, parent_id: BlockId) {
        assert!(block_id.0 > parent_id.0);
        let (slot, block_hash) = &block_id;
        let (parent_slot, parent_hash) = &parent_id;

        let finalization_event = self
            .finality_tracker
            .add_parent(block_id.clone(), parent_id.clone());
        let new_parents_ready = self
            .parent_ready_tracker
            .handle_finalization(finalization_event);
        self.send_parent_ready_events(new_parents_ready);

        self.slot_state(*slot).notify_parent_known(block_hash);
        if let Some(parent_state) = self.slot_states.get(parent_slot)
            && parent_state.is_notar_fallback_or_stronger(parent_hash)
            && let Some(output) = self
                .slot_state(*slot)
                .notify_parent_certified(block_hash.clone())
        {
            match output {
                Either::Left(event) => self.enqueue_votor_event(event),
                Either::Right((slot, hash)) => self.enqueue_repair((slot, hash)),
            }
            return;
        }
        self.s2n_waiting_parent_cert.insert(parent_id, block_id);
    }

    /// Triggers a recovery from a standstill.
    ///
    /// Determines which certificates and votes need to be re-broadcast and returns
    /// them as a [`PoolOutbox`] holding a single [`PoolEvent::Standstill`] for the
    /// caller to forward to Votor. Should be called after not seeing any progress
    /// for the standstill duration.
    ///
    /// NOTE: The bundle may legitimately come out empty. A node that has not
    /// finalized anything yet has no final cert for the genesis slot, which is
    /// exactly the case for a node that booted into a partition or started ahead
    /// of the rest of the cluster. That is a standstill worth reporting, not an
    /// invariant violation, so the recovery path must not assume a final cert.
    fn recover_from_standstill(&self) -> PoolOutbox {
        let slot = self.finalized_slot();
        let mut certs = self.get_final_certs(slot);
        certs.extend(self.get_certs(slot.next()..));
        let votes = self.get_own_votes(slot.next()..);

        warn!("recovering from standstill at slot {slot}");
        debug!(
            "re-broadcasting {} certificates and {} votes",
            certs.len(),
            votes.len()
        );

        // NOTE: This event's slot is the one after the last finalized slot.
        // `Votor` always re-broadcasts the recovery bundle regardless of slot;
        // it intentionally does not gate this on its own finalized slot, which
        // can run ahead of Pool's (final cert vs. final + notar), and could
        // otherwise drop a bundle that Pool emitted precisely because it is stuck.
        let event = PoolEvent::Standstill(slot.next(), certs, votes);

        // return to the caller for (off-lock) forwarding to Votor
        PoolOutbox {
            effects: vec![PoolEffect::VotorEvent(event)],
        }
    }

    fn take_outbox(&mut self) -> PoolOutbox {
        std::mem::take(&mut self.outbox)
    }

    /// Gives the currently highest finalized (fast or slow) slot.
    fn finalized_slot(&self) -> Slot {
        self.finality_tracker.highest_finalized_slot()
    }

    /// Returns all possible parents for the given slot that are ready.
    fn parents_ready(&self, slot: Slot) -> &[BlockId] {
        self.parent_ready_tracker.parents_ready(slot)
    }

    fn wait_for_parent_ready(&mut self, slot: Slot) -> Either<BlockId, oneshot::Receiver<BlockId>> {
        self.parent_ready_tracker.wait_for_parent_ready(slot)
    }
}

/// Replays `votes` into a fresh [`SlotState`] for `slot`.
///
/// Lets out-of-crate benches drive the per-slot vote-counting hot path
/// ([`SlotState::add_vote`]) directly.
/// Every hash in `parents_certified` is marked known and certified up front
/// so the safe-to-notar logic actually runs.
///
/// Returns an event count (certs + votor events + repair);
/// only used as a [`std::hint::black_box`] sink.
#[cfg(feature = "test-utils")]
#[doc(hidden)]
pub fn bench_replay_votes(
    slot: Slot,
    epoch_info: Arc<ValidatorEpochInfo>,
    parents_certified: &[BlockHash],
    votes: &[(Vote, crate::Stake)],
) -> usize {
    let mut state = SlotState::new(slot, epoch_info);
    for hash in parents_certified {
        state.notify_parent_known(hash);
        let _ = state.notify_parent_certified(hash.clone());
    }
    let mut produced = 0;
    for (vote, stake) in votes {
        let (certs, events, repair) = state.add_vote(vote.clone(), *stake);
        produced += certs.len() + events.len() + repair.len();
    }
    produced
}

#[cfg(test)]
mod tests {
    use tokio::sync::mpsc;

    use super::*;
    use crate::consensus::EpochInfo;
    use crate::consensus::cert::{FastFinalCert, NotarCert, SkipCert};
    use crate::consensus::vote::{NotarVote, SkipVote};
    use crate::crypto::Hash;
    use crate::crypto::aggsig::SecretKey;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::test_utils::{generate_validators, random_block_id};
    use crate::types::SLOTS_PER_WINDOW;
    use crate::{ValidatorIndex, ValidatorInfo};

    /// Wraps shared `EpochInfo` with a `ValidatorEpochInfo` for validator 0.
    fn wrap_epoch_info(epoch_info: EpochInfo) -> Arc<ValidatorEpochInfo> {
        Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(0), epoch_info))
    }

    struct TestContext {
        sks: Vec<SecretKey>,
        epoch_info: Arc<ValidatorEpochInfo>,
        pool: PoolImpl,
        votor_tx: mpsc::Sender<PoolEvent>,
        votor_rx: mpsc::Receiver<PoolEvent>,
        repair_tx: mpsc::Sender<BlockId>,
        _repair_rx: mpsc::Receiver<BlockId>,
    }

    fn setup() -> TestContext {
        let (sks, epoch_info) = generate_validators(11);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (votor_tx, votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let pool = PoolImpl::new(epoch_info.clone());
        TestContext {
            sks,
            epoch_info,
            pool,
            votor_tx,
            votor_rx,
            repair_tx,
            _repair_rx,
        }
    }

    impl TestContext {
        /// Returns the validator set for the current epoch.
        fn validators(&self) -> &[ValidatorInfo] {
            self.epoch_info.epoch_info().validators()
        }

        /// Forwards the given pool outbox into the test channels, mirroring what
        /// [`EventForwarder`] does in production after releasing the write lock.
        ///
        /// [`EventForwarder`]: crate::consensus::EventForwarder
        fn forward(&mut self, outbox: PoolOutbox) {
            for effect in outbox.effects {
                match effect {
                    PoolEffect::VotorEvent(event) => self
                        .votor_tx
                        .try_send(event)
                        .expect("test votor channel should have capacity"),
                    PoolEffect::Repair(block) => self
                        .repair_tx
                        .try_send(block)
                        .expect("test repair channel should have capacity"),
                }
            }
        }

        /// Drains the pool's outbox into the test channels.
        fn forward_outbox(&mut self) {
            let outbox = self.pool.take_outbox();
            self.forward(outbox);
        }

        /// Verifies `vote` into a [`ValidatedVote`] and adds it to the pool.
        async fn add_vote(&mut self, vote: Vote) -> Result<(), AddVoteError> {
            // NOTE: signature-rejection is covered by the [`ValidatedVote`] tests
            let vote = ValidatedVote::try_new(vote, self.epoch_info.epoch_info())
                .expect("test vote should pass verification");
            let res = self.pool.add_vote(vote).await;
            self.forward_outbox();
            res
        }

        /// Verifies `cert` into a [`ValidatedCert`] and adds it to the pool.
        async fn add_cert(&mut self, cert: Cert) -> Result<(), AddCertError> {
            // NOTE: certificate rejection is covered by the [`ValidatedCert`] tests
            let cert = ValidatedCert::try_new(cert, self.epoch_info.epoch_info())
                .expect("test cert should pass verification");
            let res = self.pool.add_cert(cert).await;
            self.forward_outbox();
            res
        }

        /// Adds a notarization [`Vote`] for `hash` in `slot` from each of `validators` to the pool.
        async fn add_notar_votes(
            &mut self,
            slot: Slot,
            hash: &BlockHash,
            validators: std::ops::Range<usize>,
        ) {
            for v in validators.map(|v| ValidatorIndex::new(v as u64)) {
                let vote = Vote::new_notar(slot, hash.clone(), &self.sks[v.as_usize()], v);
                assert_eq!(self.add_vote(vote).await, Ok(()));
            }
        }

        /// Adds a notar-fallback [`Vote`] for `hash` in `slot` from each of `validators` to the pool.
        async fn add_notar_fallback_votes(
            &mut self,
            slot: Slot,
            hash: &BlockHash,
            validators: std::ops::Range<usize>,
        ) {
            for v in validators.map(|v| ValidatorIndex::new(v as u64)) {
                let vote = Vote::new_notar_fallback(slot, hash.clone(), &self.sks[v.as_usize()], v);
                assert_eq!(self.add_vote(vote).await, Ok(()));
            }
        }

        /// Adds a skip [`Vote`] for `slot` from each of `validators` to the pool.
        async fn add_skip_votes(&mut self, slot: Slot, validators: std::ops::Range<usize>) {
            for v in validators.map(|v| ValidatorIndex::new(v as u64)) {
                let vote = Vote::new_skip(slot, &self.sks[v.as_usize()], v);
                assert_eq!(self.add_vote(vote).await, Ok(()));
            }
        }

        /// Adds a finalization [`Vote`] for `slot` from each of `validators` to the pool.
        async fn add_final_votes(&mut self, slot: Slot, validators: std::ops::Range<usize>) {
            for v in validators.map(|v| ValidatorIndex::new(v as u64)) {
                let vote = Vote::new_final(slot, &self.sks[v.as_usize()], v);
                assert_eq!(self.add_vote(vote).await, Ok(()));
            }
        }

        /// Signs a [`NotarVote`] for `hash` in `slot` from each of the first `count` validators.
        fn notar_votes(&self, slot: Slot, hash: &BlockHash, count: u64) -> Vec<NotarVote> {
            (0..count)
                .map(|v| {
                    NotarVote::new(
                        slot,
                        hash.clone(),
                        &self.sks[v as usize],
                        ValidatorIndex::new(v),
                    )
                })
                .collect()
        }

        /// Builds a notarization cert for `hash` in `slot` from the first `count` validators.
        fn notar_cert(&self, slot: Slot, hash: &BlockHash, count: u64) -> NotarCert {
            NotarCert::try_new(&self.notar_votes(slot, hash, count), self.validators()).unwrap()
        }

        /// Builds a fast-finalization cert for `hash` in `slot` from the first `count` validators.
        fn fast_final_cert(&self, slot: Slot, hash: &BlockHash, count: u64) -> FastFinalCert {
            FastFinalCert::try_new(&self.notar_votes(slot, hash, count), self.validators()).unwrap()
        }

        /// Fast-finalizes the given block by submitting a unanimous fast-final cert.
        async fn fast_finalize(&mut self, slot: Slot, hash: &BlockHash) {
            let cert = self.fast_final_cert(slot, hash, 11);
            assert_eq!(self.add_cert(Cert::FastFinal(cert)).await, Ok(()));
        }

        /// Drains all pending votor events and reports whether `SafeToNotar(slot, hash)` was emitted.
        fn drained_safe_to_notar(&mut self, slot: Slot, hash: &BlockHash) -> bool {
            let mut seen = false;
            while let Ok(event) = self.votor_rx.try_recv() {
                if let PoolEvent::SafeToNotar((s, h)) = event
                    && s == slot
                    && &h == hash
                {
                    seen = true;
                }
            }
            seen
        }
    }

    /// Notarizing a block must record a `CertCreated` event in the pool's outbox
    /// (rather than sending it under the lock), so the caller can forward it to
    /// Votor losslessly after releasing the write lock.
    #[tokio::test]
    async fn cert_created_event_is_recorded() {
        let mut ctx = setup();

        // Notarize genesis directly on the pool, bypassing the test helpers so the
        // outbox is not drained before we can inspect it.
        for v in (0..11).map(ValidatorIndex::new) {
            let vote = Vote::new_notar(Slot::new(0), GENESIS_BLOCK_HASH, &ctx.sks[v.as_usize()], v);
            let vote = ValidatedVote::try_new(vote, ctx.epoch_info.epoch_info())
                .expect("test vote should pass verification");
            ctx.pool.add_vote(vote).await.unwrap();
        }
        assert!(ctx.pool.has_notar_cert(Slot::new(0)));

        let outbox = ctx.pool.take_outbox();
        assert!(
            outbox.effects.iter().any(|e| matches!(
                e,
                PoolEffect::VotorEvent(PoolEvent::CertCreated(Cert::Notar(_)))
            )),
            "expected a CertCreated event, got {:?}",
            outbox.effects
        );
        // Draining leaves the outbox empty.
        let drained = ctx.pool.take_outbox();
        assert!(drained.effects.is_empty());
    }

    #[tokio::test]
    async fn notarize_block() {
        let mut ctx = setup();

        // all nodes notarize block in slot 0
        assert!(!ctx.pool.has_notar_cert(Slot::new(0)));
        ctx.add_notar_votes(Slot::new(0), &GENESIS_BLOCK_HASH, 0..11)
            .await;
        assert!(ctx.pool.has_notar_cert(Slot::new(0)));

        // just enough nodes notarize block in slot 1
        assert!(!ctx.pool.has_notar_cert(Slot::new(1)));
        ctx.add_notar_votes(Slot::new(1), &GENESIS_BLOCK_HASH, 0..7)
            .await;
        assert!(ctx.pool.has_notar_cert(Slot::new(1)));

        // just NOT enough nodes notarize block in slot 2
        assert!(!ctx.pool.has_notar_cert(Slot::new(2)));
        ctx.add_notar_votes(Slot::new(2), &GENESIS_BLOCK_HASH, 0..6)
            .await;
        assert!(!ctx.pool.has_notar_cert(Slot::new(2)));
    }

    #[tokio::test]
    async fn skip_block() {
        let mut ctx = setup();

        // all nodes vote skip on slot 0
        assert!(!ctx.pool.has_skip_cert(Slot::new(0)));
        ctx.add_skip_votes(Slot::new(0), 0..11).await;
        assert!(ctx.pool.has_skip_cert(Slot::new(0)));

        // just enough nodes vote skip on slot 1
        assert!(!ctx.pool.has_skip_cert(Slot::new(1)));
        ctx.add_skip_votes(Slot::new(1), 0..7).await;
        assert!(ctx.pool.has_skip_cert(Slot::new(1)));

        // just NOT enough nodes notarize block in slot 2
        assert!(!ctx.pool.has_skip_cert(Slot::new(2)));
        ctx.add_skip_votes(Slot::new(2), 0..6).await;
        assert!(!ctx.pool.has_skip_cert(Slot::new(2)));
    }

    #[tokio::test]
    async fn finalize_block() {
        let mut ctx = setup();

        // just enough nodes vote notar, this is NOT enough on its own to finalize
        let slot1 = Slot::genesis().next();
        let hash1: BlockHash = Hash::random_for_test().into();
        ctx.add_notar_votes(slot1, &hash1, 0..7).await;
        assert!(!ctx.pool.has_final_cert(slot1));
        assert_eq!(ctx.pool.finalized_slot(), Slot::genesis());

        // just enough nodes vote final, NOW slot 1 should be finalized
        ctx.add_final_votes(slot1, 0..7).await;
        assert!(ctx.pool.has_final_cert(slot1));
        assert_eq!(ctx.pool.finalized_slot(), slot1);

        // just enough nodes vote final, this is NOT enough on its own to finalize
        let slot2 = slot1.next();
        ctx.add_final_votes(slot2, 0..7).await;
        assert!(ctx.pool.has_final_cert(slot2));
        assert_eq!(ctx.pool.finalized_slot(), slot1);

        // just enough nodes vote notar, NOW slot 2 should be finalized
        let hash2: BlockHash = Hash::random_for_test().into();
        ctx.add_notar_votes(slot2, &hash2, 0..7).await;
        assert!(ctx.pool.has_final_cert(slot2));
        assert_eq!(ctx.pool.finalized_slot(), slot2);

        // just NOT enough nodes vote notar + final on slot 3
        let slot3 = slot2.next();
        let hash3: BlockHash = Hash::random_for_test().into();
        ctx.add_notar_votes(slot3, &hash3, 0..6).await;
        ctx.add_final_votes(slot3, 0..6).await;
        assert!(!ctx.pool.has_final_cert(slot3));
        assert_eq!(ctx.pool.finalized_slot(), slot2);
    }

    #[tokio::test]
    async fn fast_finalize_block() {
        let mut ctx = setup();

        // all nodes vote notarize on slot 0
        assert!(!ctx.pool.has_final_cert(Slot::new(0)));
        ctx.add_notar_votes(Slot::new(0), &GENESIS_BLOCK_HASH, 0..11)
            .await;
        assert!(ctx.pool.has_final_cert(Slot::new(0)));
        assert_eq!(ctx.pool.finalized_slot(), Slot::new(0));

        // just enough nodes to fast finalize slot 1
        assert!(!ctx.pool.has_final_cert(Slot::new(1)));
        ctx.add_notar_votes(Slot::new(1), &GENESIS_BLOCK_HASH, 0..9)
            .await;
        assert!(ctx.pool.has_final_cert(Slot::new(1)));
        assert_eq!(ctx.pool.finalized_slot(), Slot::new(1));

        // just NOT enough nodes to fast finalize slot 2
        assert!(!ctx.pool.has_final_cert(Slot::new(2)));
        ctx.add_notar_votes(Slot::new(2), &GENESIS_BLOCK_HASH, 0..8)
            .await;
        assert!(!ctx.pool.has_final_cert(Slot::new(2)));
        assert_eq!(ctx.pool.finalized_slot(), Slot::new(1));
    }

    #[tokio::test]
    async fn simple_branch_certified() {
        let mut ctx = setup();

        let window = Slot::genesis().slots_in_window().collect::<Vec<_>>();
        let hashes: Vec<BlockHash> = window
            .iter()
            .map(|_| Hash::random_for_test().into())
            .collect();
        for slot in window.iter().skip(1) {
            let hash = &hashes[slot.inner() as usize];
            ctx.add_notar_votes(*slot, hash, 0..7).await;
        }
        let slot = *window.last().unwrap();
        let next = slot.next();
        assert!(
            ctx.pool
                .is_parent_ready(next, &(slot, hashes[next.inner() as usize - 1].clone()))
        );
    }

    #[tokio::test]
    async fn branch_certified_notar_fallback() {
        let mut ctx = setup();

        // receive mixed notar & notar-fallback votes
        let window = Slot::genesis().slots_in_window().collect::<Vec<_>>();
        let hashes: Vec<BlockHash> = window
            .iter()
            .map(|_| Hash::random_for_test().into())
            .collect();
        for slot in window.iter().skip(1) {
            let hash = &hashes[slot.inner() as usize];
            assert!(
                !ctx.pool
                    .is_parent_ready(slot.next(), &(*slot, hash.clone()))
            );
            ctx.add_notar_votes(*slot, hash, 0..4).await;
            ctx.add_notar_fallback_votes(*slot, hash, 4..7).await;
        }
        let slot = *window.last().unwrap();
        let next = slot.next();
        let hash = hashes[next.inner() as usize - 1].clone();
        assert!(ctx.pool.is_parent_ready(next, &(slot, hash)));
    }

    #[tokio::test]
    async fn branch_certified_out_of_order() {
        let mut ctx = setup();

        // first see skip votes for later slots
        let mut window = Slot::new(0).slots_in_window().collect::<Vec<_>>();
        assert!(window.len() > 2);
        window.remove(0);
        window.remove(0);
        for slot in window.iter() {
            ctx.add_skip_votes(*slot, 0..7).await;
        }

        let next = window.last().unwrap().next();
        // no blocks are valid parents yet
        assert!(ctx.pool.parents_ready(next).is_empty());

        // then see notarization votes for slot 1
        let slot1 = Slot::new(1);
        let hash1: BlockHash = Hash::random_for_test().into();
        ctx.add_notar_votes(slot1, &hash1, 0..7).await;

        // branch can only be certified once we saw votes other slots in window
        assert!(ctx.pool.is_parent_ready(next, &(slot1, hash1)));
        // no other blocks are valid parents
        assert_eq!(ctx.pool.parents_ready(next).len(), 1);
    }

    #[tokio::test]
    async fn branch_certified_late_cert() {
        let mut ctx = setup();

        // first see skip votes for later slots
        let window = Slot::genesis().slots_in_window().collect::<Vec<_>>();
        assert!(window.len() > 2);
        for slot in window.iter().skip(2) {
            ctx.add_skip_votes(*slot, 0..7).await;
        }

        // no blocks are valid parents yet
        let next = window.last().unwrap().next();
        assert!(ctx.pool.parents_ready(next).is_empty());

        // then receive notarization cert for slot 1
        let slot1 = Slot::new(1);
        let hash1: BlockHash = Hash::random_for_test().into();
        let cert = ctx.notar_cert(slot1, &hash1, 7);
        ctx.add_cert(Cert::Notar(cert)).await.unwrap();

        // branch can only be certified once we saw votes for parent
        assert!(ctx.pool.is_parent_ready(next, &(slot1, hash1)));
    }

    #[tokio::test]
    async fn regular_handover() {
        let mut ctx = setup();

        let hashes: Vec<BlockHash> = (0..SLOTS_PER_WINDOW)
            .map(|_| Hash::random_for_test().into())
            .collect();

        // notarize all slots of first window
        for slot in (1..SLOTS_PER_WINDOW).map(Slot::new) {
            let hash = &hashes[slot.inner() as usize];
            ctx.add_notar_votes(slot, hash, 0..7).await;
        }

        assert!(ctx.pool.is_parent_ready(
            Slot::new(SLOTS_PER_WINDOW),
            &(
                Slot::new(SLOTS_PER_WINDOW - 1),
                hashes[(SLOTS_PER_WINDOW - 1) as usize].clone()
            )
        ));
    }

    #[tokio::test]
    async fn one_skip_handover() {
        let mut ctx = setup();

        let hashes: Vec<BlockHash> = (0..SLOTS_PER_WINDOW)
            .map(|_| Hash::random_for_test().into())
            .collect();

        // notarize all slots but last one
        for slot in (1..SLOTS_PER_WINDOW - 1).map(Slot::new) {
            let hash = &hashes[slot.inner() as usize];
            ctx.add_notar_votes(slot, hash, 0..7).await;
        }

        // skip last slot
        ctx.add_skip_votes(Slot::new(SLOTS_PER_WINDOW - 1), 0..7)
            .await;

        assert!(ctx.pool.is_parent_ready(
            Slot::new(SLOTS_PER_WINDOW),
            &(
                Slot::new(SLOTS_PER_WINDOW - 2),
                hashes[(SLOTS_PER_WINDOW - 2) as usize].clone()
            )
        ));
    }

    #[tokio::test]
    async fn two_skip_handover() {
        let mut ctx = setup();

        let hashes: Vec<BlockHash> = (0..SLOTS_PER_WINDOW)
            .map(|_| Hash::random_for_test().into())
            .collect::<Vec<_>>();

        // notarize all slots but last two
        for slot in (1..SLOTS_PER_WINDOW - 2).map(Slot::new) {
            let hash = &hashes[slot.inner() as usize];
            ctx.add_notar_votes(slot, hash, 0..7).await;
        }

        // skip last 2 slots
        ctx.add_skip_votes(Slot::new(SLOTS_PER_WINDOW - 2), 0..7)
            .await;
        ctx.add_skip_votes(Slot::new(SLOTS_PER_WINDOW - 1), 0..7)
            .await;

        assert!(ctx.pool.is_parent_ready(
            Slot::new(SLOTS_PER_WINDOW),
            &(
                Slot::new(SLOTS_PER_WINDOW - 3),
                hashes[(SLOTS_PER_WINDOW - 3) as usize].clone()
            )
        ));
    }

    #[tokio::test]
    async fn skip_window_handover() {
        let mut ctx = setup();

        let hashes: Vec<BlockHash> = (0..SLOTS_PER_WINDOW)
            .map(|_| Hash::random_for_test().into())
            .collect();

        // notarize all slots in first window
        for slot in (1..SLOTS_PER_WINDOW).map(Slot::new) {
            let hash = &hashes[slot.inner() as usize];
            ctx.add_notar_votes(slot, hash, 0..7).await;
        }

        // skip all slots in second window
        for slot in (SLOTS_PER_WINDOW..2 * SLOTS_PER_WINDOW).map(Slot::new) {
            ctx.add_skip_votes(slot, 0..7).await;
        }

        assert!(ctx.pool.is_parent_ready(
            Slot::new(2 * SLOTS_PER_WINDOW),
            &(
                Slot::new(SLOTS_PER_WINDOW - 1),
                hashes[(SLOTS_PER_WINDOW - 1) as usize].clone()
            )
        ));
    }

    #[tokio::test]
    async fn pruning() {
        let mut ctx = setup();

        let hashes: Vec<BlockHash> = (0..3 * SLOTS_PER_WINDOW + 10)
            .map(|_| Hash::random_for_test().into())
            .collect();

        // all nodes vote to fast finalize 3 leader windows
        for slot in (1..3 * SLOTS_PER_WINDOW).map(Slot::new) {
            let hash: &BlockHash = &hashes[slot.inner() as usize];
            assert!(!ctx.pool.has_final_cert(slot));
            ctx.add_notar_votes(slot, hash, 0..11).await;
            assert!(ctx.pool.has_final_cert(slot));
        }
        let last_slot = Slot::new(3 * SLOTS_PER_WINDOW - 1);
        assert_eq!(ctx.pool.finalized_slot(), last_slot);

        // finalization triggers pruning, only last slot should be there
        for slot in 0..last_slot.inner() {
            let slot = Slot::new(slot);
            assert!(!ctx.pool.slot_states.contains_key(&slot));
        }
        assert!(ctx.pool.slot_states.contains_key(&(last_slot)));

        // NOT enough nodes vote to fast finalize next 10 slots
        for slot in last_slot.future_slots().take(10) {
            let hash: &BlockHash = &hashes[slot.inner() as usize];
            ctx.add_notar_votes(slot, hash, 0..8).await;
            assert!(!ctx.pool.has_final_cert(slot));
        }
        assert_eq!(ctx.pool.finalized_slot(), last_slot);

        // these slots should still be there
        for s in 0..=10 {
            let slot = Slot::new(last_slot.inner() + s);
            assert!(ctx.pool.slot_states.contains_key(&slot));
        }

        // add one more vote each to finalize next 10 slots
        for slot in last_slot.future_slots().take(10) {
            let hash = &hashes[slot.inner() as usize];
            ctx.add_notar_votes(slot, hash, 8..9).await;
            assert!(ctx.pool.has_final_cert(slot));
        }
        assert_eq!(ctx.pool.finalized_slot().inner(), last_slot.inner() + 10);

        // NOW next 10 slots should be gone
        for s in 0..10 {
            let slot = Slot::new(last_slot.inner() + s);
            assert!(!ctx.pool.slot_states.contains_key(&slot));
        }
        let new_last_slot = Slot::new(last_slot.inner() + 10);
        assert!(ctx.pool.slot_states.contains_key(&new_last_slot));
    }

    #[tokio::test]
    async fn duplicate_votes() {
        let mut ctx = setup();
        let slot = Slot::new(0);

        // insert a notar vote from validator 0
        let vote1 = Vote::new_notar(
            slot,
            GENESIS_BLOCK_HASH,
            &ctx.sks[0],
            ValidatorIndex::new(0),
        );
        assert_eq!(ctx.add_vote(vote1.clone()).await, Ok(()));

        // insert a skip vote from validator 1
        let vote2 = Vote::new_skip(slot, &ctx.sks[1], ValidatorIndex::new(1));
        assert_eq!(ctx.add_vote(vote2.clone()).await, Ok(()));

        // inserting same votes again should fail
        assert_eq!(ctx.add_vote(vote1).await, Err(AddVoteError::Duplicate));
        assert_eq!(ctx.add_vote(vote2).await, Err(AddVoteError::Duplicate));
    }

    #[tokio::test]
    async fn duplicate_certs() {
        let mut ctx = setup();

        // insert a notar cert for first slot
        let first_slot = Slot::genesis().next();
        let hash: BlockHash = Hash::random_for_test().into();
        let notar_cert = ctx.notar_cert(first_slot, &hash, 11);
        assert_eq!(ctx.add_cert(Cert::Notar(notar_cert.clone())).await, Ok(()));

        // insert a skip cert for slot 1
        let second_slot = first_slot.next();
        let skip_votes: Vec<SkipVote> = (0..11)
            .map(|v| SkipVote::new(second_slot, &ctx.sks[v as usize], ValidatorIndex::new(v)))
            .collect();
        let skip_cert = SkipCert::try_new(&skip_votes, &[], ctx.validators()).unwrap();
        assert_eq!(ctx.add_cert(Cert::Skip(skip_cert.clone())).await, Ok(()));

        // inserting same certs again should fail
        assert_eq!(
            ctx.add_cert(Cert::Notar(notar_cert)).await,
            Err(AddCertError::Duplicate)
        );
        assert_eq!(
            ctx.add_cert(Cert::Skip(skip_cert)).await,
            Err(AddCertError::Duplicate)
        );
    }

    #[tokio::test]
    async fn out_of_bounds_votes() {
        let mut ctx = setup();

        // fast-finalize a contiguous run of slots so the pruning watermark advances
        let slot = Slot::new(3 * SLOTS_PER_WINDOW - 1);
        for s in 1..=slot.inner() {
            ctx.add_notar_votes(Slot::new(s), &GENESIS_BLOCK_HASH, 0..11)
                .await;
        }
        assert_eq!(ctx.pool.finalized_slot(), slot);
        assert_eq!(ctx.pool.first_unpruned_slot(), slot);

        // dismiss old votes
        for slot in 0..3 * SLOTS_PER_WINDOW - 1 {
            for v in 0..11 {
                let vote = Vote::new_final(
                    Slot::new(slot),
                    &ctx.sks[v as usize],
                    ValidatorIndex::new(v),
                );
                assert_eq!(ctx.add_vote(vote).await, Err(AddVoteError::SlotOutOfBounds));
            }
        }

        // dismiss far-in-the-future vote
        let slot = Slot::new(5 * SLOTS_PER_EPOCH);
        for v in 0..11 {
            let vote = Vote::new_final(slot, &ctx.sks[v as usize], ValidatorIndex::new(v));
            assert_eq!(ctx.add_vote(vote).await, Err(AddVoteError::SlotOutOfBounds));
        }
    }

    #[tokio::test]
    async fn out_of_bounds_certs() {
        let mut ctx = setup();

        // fast-finalize a contiguous run of slots so the pruning watermark advances
        let slot = Slot::new(3 * SLOTS_PER_WINDOW - 1);
        for s in 1..=slot.inner() {
            ctx.fast_finalize(Slot::new(s), &GENESIS_BLOCK_HASH).await;
        }
        assert_eq!(ctx.pool.first_unpruned_slot(), slot);

        // dismiss old certs
        for slot in 0..3 * SLOTS_PER_WINDOW - 1 {
            let skip_votes: Vec<SkipVote> = (0..11)
                .map(|v| {
                    SkipVote::new(
                        Slot::new(slot),
                        &ctx.sks[v as usize],
                        ValidatorIndex::new(v),
                    )
                })
                .collect();
            let skip_cert = SkipCert::try_new(&skip_votes, &[], ctx.validators()).unwrap();
            assert_eq!(
                ctx.add_cert(Cert::Skip(skip_cert.clone())).await,
                Err(AddCertError::SlotOutOfBounds)
            );
        }

        // dismiss far-in-the-future certs
        let slot = Slot::new(3 * SLOTS_PER_EPOCH);
        let skip_votes: Vec<SkipVote> = (0..11)
            .map(|v| SkipVote::new(slot, &ctx.sks[v as usize], ValidatorIndex::new(v)))
            .collect();
        let skip_cert = SkipCert::try_new(&skip_votes, &[], ctx.validators()).unwrap();
        assert_eq!(
            ctx.add_cert(Cert::Skip(skip_cert.clone())).await,
            Err(AddCertError::SlotOutOfBounds)
        );
    }

    #[tokio::test]
    async fn slow_finalize_closing_gap_no_double_parent_ready() {
        let mut ctx = setup();
        let next_start = Slot::windows().nth(1).unwrap();
        let gap_slot = next_start.prev();
        let watermark_slot = gap_slot.prev();

        // fast-finalize every slot below `gap_slot`
        for s in 1..gap_slot.inner() {
            ctx.fast_finalize(Slot::new(s), &GENESIS_BLOCK_HASH).await;
        }
        // this moves the watermark just below it
        assert_eq!(ctx.pool.first_unpruned_slot(), watermark_slot);

        // `gap_slot` gets a final cert but no notarization yet
        let gap_hash: BlockHash = Hash::random_for_test().into();
        ctx.add_final_votes(gap_slot, 0..7).await;
        assert!(ctx.pool.has_final_cert(gap_slot));
        assert_eq!(ctx.pool.first_unpruned_slot(), watermark_slot);

        // fast-finalize `next_start`, introducing a gap
        ctx.fast_finalize(next_start, &GENESIS_BLOCK_HASH).await;
        assert_eq!(ctx.pool.finalized_slot(), next_start);
        // cannot prune past the gap
        assert_eq!(ctx.pool.first_unpruned_slot(), watermark_slot);

        // `gap_slot`'s notarization closes the gap
        ctx.add_notar_votes(gap_slot, &gap_hash, 0..7).await;
        // jumping the watermark across both slots
        assert_eq!(ctx.pool.first_unpruned_slot(), next_start);

        // `gap_slot` is propagated as a ready parent exactly once
        assert_eq!(ctx.pool.parents_ready(next_start).iter().count(), 1);
    }

    /// A node that has not finalized anything yet has no final cert for the
    /// genesis slot. Standstill recovery must still produce a bundle (an empty one)
    /// rather than panic — booting into a partition, or ahead of the rest of the
    /// cluster, is exactly when recovery needs to run.
    #[tokio::test]
    async fn standstill_recovery_without_any_final_cert() {
        let mut ctx = setup();

        assert_eq!(ctx.pool.finalized_slot(), Slot::genesis());
        let outbox = ctx.pool.recover_from_standstill();
        ctx.forward(outbox);

        let event = ctx.votor_rx.recv().await.unwrap();
        let PoolEvent::Standstill(slot, certs, votes) = event else {
            unreachable!("unexpected event {event:?}");
        };
        assert_eq!(slot, Slot::genesis().next());
        assert!(certs.is_empty());
        assert!(votes.is_empty());
    }

    #[tokio::test]
    async fn standstill_recovery() {
        let mut ctx = setup();

        // all nodes vote for first slot (it's fast finalized)
        let slot1 = Slot::genesis().next();
        let hash1: BlockHash = Hash::random_for_test().into();
        ctx.add_notar_votes(slot1, &hash1, 0..11).await;

        // we also vote for next slot, see only final votes (it's missing notar)
        let slot2 = slot1.next();
        ctx.add_final_votes(slot2, 0..7).await;

        // we also vote for next slot, see no other votes
        let slot3 = slot2.next();
        let hash3: BlockHash = Hash::random_for_test().into();
        ctx.add_notar_votes(slot3, &hash3, 0..1).await;

        // initiate standstill
        let outbox = ctx.pool.recover_from_standstill();
        ctx.forward(outbox);

        // wait for standstill event
        let (slot, certs, votes) = loop {
            let event = ctx.votor_rx.recv().await.unwrap();
            match event {
                PoolEvent::CertCreated(_) => {
                    continue;
                }
                PoolEvent::Standstill(slot, certs, votes) => {
                    break (slot, certs, votes);
                }
                _ => unreachable!("unexpected event {event:?}"),
            }
        };

        // check against expected response
        assert_eq!(slot, slot2);
        assert_eq!(certs.len(), 2);
        for cert in certs {
            if matches!(cert, Cert::FastFinal(_)) {
                assert_eq!(cert.slot(), slot1);
            } else if matches!(cert, Cert::Final(_)) {
                assert_eq!(cert.slot(), slot2);
            } else {
                unreachable!("unexpected cert {cert:?}");
            }
        }
        assert_eq!(votes.len(), 2);
        for vote in votes {
            assert_eq!(vote.signer(), ValidatorIndex::new(0));
            if matches!(vote, Vote::Final(_)) {
                assert_eq!(vote.slot(), slot2);
            } else if matches!(vote, Vote::Notar(_)) {
                assert_eq!(vote.slot(), slot3);
            } else {
                unreachable!("unexpected vote {vote:?}");
            }
        }
    }

    #[tokio::test]
    async fn parent_ready_upon_finalization() {
        let mut ctx = setup();

        // fast finalize block in 2nd slot of 2nd window
        let slot1 = Slot::windows().nth(1).unwrap();
        let block0 = random_block_id(slot1.prev());
        let block1 = random_block_id(slot1);
        let block2 = random_block_id(slot1.next());
        ctx.add_notar_votes(block2.0, &block2.1, 0..11).await;

        // should construct 3 certs (notar-fallback + notar + fast-final)
        for _ in 0..3 {
            let event = ctx.votor_rx.recv().await;
            assert!(matches!(event, Some(PoolEvent::CertCreated(_))));
        }

        // no ParentReady yet
        assert_eq!(
            ctx.votor_rx.try_recv().err(),
            Some(mpsc::error::TryRecvError::Empty)
        );

        // add its ancestors
        ctx.pool.add_block(block2.clone(), block1.clone()).await;
        ctx.pool.add_block(block1.clone(), block0.clone()).await;
        ctx.forward_outbox();

        // should emit ParentReady as a result
        let Ok(event) = ctx.votor_rx.try_recv() else {
            panic!("expected to receive ParentReady event");
        };
        match event {
            PoolEvent::ParentReady { slot, parent } => {
                assert_eq!(slot, slot1);
                assert_eq!(parent, block0);
            }
            _ => unreachable!("unexpected event {event:?}"),
        }
    }

    #[tokio::test]
    async fn safe_to_notar_notar_cert_only() {
        let mut ctx = setup();

        let slot1 = Slot::genesis().next();
        let slot2 = slot1.next();
        let hash1: BlockHash = Hash::random_for_test().into();
        let hash2: BlockHash = Hash::random_for_test().into();

        // parent (slot1) is notarized only via a received notar cert
        let cert = ctx.notar_cert(slot1, &hash1, 7);
        ctx.add_cert(Cert::Notar(cert)).await.unwrap();

        // register the child block
        ctx.pool
            .add_block((slot2, hash2.clone()), (slot1, hash1.clone()))
            .await;

        // we skip slot2, but 40% of others notarize the child
        ctx.add_skip_votes(slot2, 0..1).await;
        ctx.add_notar_votes(slot2, &hash2, 1..6).await;

        // child should now be safe-to-notar
        assert!(
            ctx.drained_safe_to_notar(slot2, &hash2),
            "child should be safe-to-notar once its parent is notarized via a received cert"
        );
    }

    #[tokio::test]
    async fn safe_to_notar_fast_final_cert_only() {
        let mut ctx = setup();

        let slot1 = Slot::genesis().next();
        let slot2 = slot1.next();
        let hash1: BlockHash = Hash::random_for_test().into();
        let hash2: BlockHash = Hash::random_for_test().into();

        // parent (slot1) is fast-finalized only via a received cert
        let cert = ctx.fast_final_cert(slot1, &hash1, 9);
        ctx.add_cert(Cert::FastFinal(cert)).await.unwrap();

        // register the child block
        ctx.pool
            .add_block((slot2, hash2.clone()), (slot1, hash1.clone()))
            .await;

        // we skip slot2, but 40% of others notarize the child
        ctx.add_skip_votes(slot2, 0..1).await;
        ctx.add_notar_votes(slot2, &hash2, 1..6).await;

        // child should now be safe-to-notar
        assert!(
            ctx.drained_safe_to_notar(slot2, &hash2),
            "child should be safe-to-notar once its parent is fast-finalized via a received cert"
        );
    }
}
