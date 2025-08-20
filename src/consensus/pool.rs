// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure handling votes and certificates.
//!
//! Any received votes or certificates are placed into the pool.
//! The pool then tracks status for each slot and sends notification to votor.

mod parent_ready_tracker;
mod slot_state;

use std::collections::BTreeMap;
use std::sync::Arc;

use async_trait::async_trait;
use either::Either;
use log::{debug, info, trace, warn};
use mockall::automock;
use thiserror::Error;
use tokio::sync::mpsc::Sender;
use tokio::sync::oneshot;

use crate::crypto::Hash;
use crate::types::SLOTS_PER_EPOCH;
use crate::{BlockId, Slot, ValidatorId};

use super::blockstore::BlockInfo;
use super::votor::VotorEvent;
use super::{Cert, EpochInfo, Vote};

use parent_ready_tracker::ParentReadyTracker;
use slot_state::SlotState;

/// Errors the Pool may return when adding a vote.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum AddVoteError {
    #[error("slot is either too old or too far in the future")]
    SlotOutOfBounds,
    #[error("invalid signature on the vote")]
    InvalidSignature,
    #[error("duplicate vote")]
    Duplicate,
    #[error("vote constitutes a slashable offence")]
    Slashable(SlashableOffence),
}

/// Errors the Pool may return when adding a certificate.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum AddCertError {
    #[error("slot is either too old or too far in the future")]
    SlotOutOfBounds,
    #[error("invalid signature on the cert")]
    InvalidSignature,
    #[error("duplicate cert")]
    Duplicate,
}

/// Slashable offences that may be detected by the Pool.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum SlashableOffence {
    #[error("Validator {0} already voted notar on slot {1} for a different hash")]
    NotarDifferentHash(ValidatorId, Slot),
    #[error("Validator {0} voted both skip and notarize on slot {1}")]
    SkipAndNotarize(ValidatorId, Slot),
    #[error("Validator {0} voted both skip(-fallback) and finalize on slot {1}")]
    SkipAndFinalize(ValidatorId, Slot),
    #[error("Validator {0} voted both notar-fallback and finalize on slot {1}")]
    NotarFallbackAndFinalize(ValidatorId, Slot),
}

#[async_trait]
#[automock]
pub trait Pool {
    async fn add_cert(&mut self, cert: Cert) -> Result<(), AddCertError>;
    async fn add_vote(&mut self, vote: Vote) -> Result<(), AddVoteError>;
    async fn add_block(&mut self, slot: Slot, block_info: BlockInfo);
    async fn recover_from_standstill(&self);
    fn finalized_slot(&self) -> Slot;
    fn parents_ready(&self, slot: Slot) -> &[(Slot, Hash)];
    fn wait_for_parent_ready(&mut self, slot: Slot) -> Either<BlockId, oneshot::Receiver<BlockId>>;
}

/// Pool is the central consensus data structure.
/// It holds votes and certificates for each slot.
pub struct PoolImpl {
    /// State for each slot. Stores all votes and certificates.
    slot_states: BTreeMap<Slot, SlotState>,
    /// Keeps track of which slots have a parent ready.
    parent_ready_tracker: ParentReadyTracker,
    /// Keeps track of safe-to-notar blocks waiting for a parent certificate.
    s2n_waiting_parent_cert: BTreeMap<(Slot, Hash), (Slot, Hash)>,

    /// Highest slot that is at least notarized fallabck.
    highest_notarized_fallback_slot: Slot,
    /// Highest slot that was finalized (slow or fast).
    highest_finalized_slot: Slot,

    /// Information about all active validators.
    epoch_info: Arc<EpochInfo>,
    /// Channel for sending events related to voting logic to Votor.
    votor_event_channel: Sender<VotorEvent>,
    /// Channel for sending repair requests to the repair loop.
    repair_channel: Sender<(Slot, Hash)>,
}

impl PoolImpl {
    /// Creates a new empty pool containing no votes or certificates.
    ///
    /// Any later emitted events will be sent on provided `votor_event_channel`.
    pub fn new(
        epoch_info: Arc<EpochInfo>,
        votor_event_channel: Sender<VotorEvent>,
        repair_channel: Sender<(Slot, Hash)>,
    ) -> Self {
        Self {
            slot_states: BTreeMap::new(),
            parent_ready_tracker: ParentReadyTracker::default(),
            s2n_waiting_parent_cert: BTreeMap::new(),
            highest_notarized_fallback_slot: Slot::new(0),
            highest_finalized_slot: Slot::new(0),
            epoch_info,
            votor_event_channel,
            repair_channel,
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
                let block_hash = cert.block_hash().unwrap();
                let h = &hex::encode(block_hash)[..8];
                info!("notarized(-fallback) block {h} in slot {slot}");
                self.highest_notarized_fallback_slot =
                    slot.max(self.highest_notarized_fallback_slot);

                // potentially notify child waiting for safe-to-notar
                if let Some((child_slot, child_hash)) =
                    self.s2n_waiting_parent_cert.remove(&(slot, block_hash))
                    && let Some(output) = self
                        .slot_state(child_slot)
                        .notify_parent_certified(child_hash)
                {
                    match output {
                        Either::Left(event) => {
                            self.votor_event_channel.send(event).await.unwrap();
                        }
                        Either::Right((slot, hash)) => {
                            self.repair_channel.send((slot, hash)).await.unwrap();
                        }
                    }
                }

                // add block to parent-ready tracker, send any new parents to Votor.
                let new_parents_ready = self
                    .parent_ready_tracker
                    .mark_notar_fallback((slot, block_hash));
                for (slot, (parent_slot, parent_hash)) in new_parents_ready {
                    debug_assert!(slot.is_start_of_window());
                    let event = VotorEvent::ParentReady {
                        slot,
                        parent_slot,
                        parent_hash,
                    };
                    self.votor_event_channel.send(event).await.unwrap();
                }

                // repair this block, if necessary
                self.repair_channel.send((slot, block_hash)).await.unwrap();
            }
            Cert::Skip(_) => {
                warn!("skipped slot {slot}");
                let newly_certified = self.parent_ready_tracker.mark_skipped(slot);
                for (slot, (parent_slot, parent_hash)) in newly_certified {
                    debug_assert!(slot.is_start_of_window());
                    let event = VotorEvent::ParentReady {
                        slot,
                        parent_slot,
                        parent_hash,
                    };
                    self.votor_event_channel.send(event).await.unwrap();
                }
            }
            Cert::FastFinal(_) => {
                info!("fast finalized slot {slot}");
                self.highest_finalized_slot = slot.max(self.highest_finalized_slot);
                self.prune();
            }
            Cert::Final(_) => {
                info!("slow finalized slot {slot}");
                self.highest_finalized_slot = slot.max(self.highest_finalized_slot);
                self.prune();
            }
        }

        // send to votor for broadcasting
        let event = VotorEvent::CertCreated(Box::new(cert));
        self.votor_event_channel.send(event).await.unwrap();
    }

    fn slot_state(&mut self, slot: Slot) -> &mut SlotState {
        self.slot_states
            .entry(slot)
            .or_insert_with(|| SlotState::new(slot, Arc::clone(&self.epoch_info)))
    }

    fn get_certs(&self, slot: Slot) -> Vec<Cert> {
        let mut certs = Vec::new();
        for (_, slot_state) in self.slot_states.range(slot..) {
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

    fn get_own_votes(&self, slot: Slot) -> Vec<Vote> {
        let mut votes = Vec::new();
        let own_id = self.epoch_info.own_id;
        for (_, slot_state) in self.slot_states.range(slot..) {
            if let Some(vote) = &slot_state.votes.finalize[own_id as usize] {
                votes.push(vote.clone());
            }
            if let Some((_, vote)) = &slot_state.votes.notar[own_id as usize] {
                votes.push(vote.clone());
            }
            for (_, vote) in &slot_state.votes.notar_fallback[own_id as usize] {
                votes.push(vote.clone());
            }
            if let Some(vote) = &slot_state.votes.skip[own_id as usize] {
                votes.push(vote.clone());
            }
            if let Some(vote) = &slot_state.votes.skip_fallback[own_id as usize] {
                votes.push(vote.clone());
            }
        }
        votes
    }

    /// Cleans up old finalized slots from the pool.
    ///
    /// After this, [`Self::slot_states`] will only contain entries for slots
    /// >= [`Self::highest_finalized_slot`].
    fn prune(&mut self) {
        let last_slot = self.highest_finalized_slot;
        self.slot_states = self.slot_states.split_off(&last_slot);
    }

    /// Returns `true` iff the given parent is ready for the given slot.
    ///
    /// This requires that the parent is at least notarized-fallback.
    /// Also, if the parent is in a slot before `slot-1`, then all slots in
    /// `parent+1..slot-1` (inclusive) must be skip-certified.
    pub fn is_parent_ready(&self, slot: Slot, parent: (Slot, Hash)) -> bool {
        self.parent_ready_tracker
            .parents_ready(slot)
            .contains(&parent)
    }

    /// Returns `true` iff the pool contains a notar(-fallback) certificate for the slot.
    pub fn is_notarized_fallback(&self, slot: Slot) -> bool {
        self.slot_states.get(&slot).is_some_and(|state| {
            state.certificates.notar.is_some() || !state.certificates.notar_fallback.is_empty()
        })
    }

    /// Gives the current tip of the chain for block production.
    pub fn get_tip(&self) -> Slot {
        self.highest_notarized_fallback_slot
    }

    /// Returns `true` iff the pool contains a (fast) finalization certificate for the slot.
    pub fn is_finalized(&self, slot: Slot) -> bool {
        self.slot_states.get(&slot).is_some_and(|state| {
            state.certificates.fast_finalize.is_some() || state.certificates.finalize.is_some()
        })
    }

    /// Returns `true` iff the pool contains a notarization certificate for the slot.
    pub fn is_notarized(&self, slot: Slot) -> bool {
        self.slot_states
            .get(&slot)
            .is_some_and(|state| state.certificates.notar.is_some())
    }

    /// Returns `true` iff the pool contains a skip certificate for the slot.
    pub fn is_skip_certified(&self, slot: Slot) -> bool {
        self.slot_states
            .get(&slot)
            .is_some_and(|state| state.certificates.skip.is_some())
    }
}

#[async_trait]
impl Pool for PoolImpl {
    /// Adds a new certificate to the pool. Checks validity of the certificate.
    async fn add_cert(&mut self, cert: Cert) -> Result<(), AddCertError> {
        // ignore old and far-in-the-future certificates
        let slot = cert.slot();
        // TODO: set bounds exactly correctly,
        //       use correct validator set & stake distribution
        let slot_far_in_future =
            Slot::new(self.highest_finalized_slot.inner() + 2 * SLOTS_PER_EPOCH);
        if slot <= self.highest_finalized_slot || slot >= slot_far_in_future {
            return Err(AddCertError::SlotOutOfBounds);
        }

        // verify signature
        if !cert.check_sig(&self.epoch_info.validators) {
            return Err(AddCertError::InvalidSignature);
        }

        // get `SlotCertificates`, initialize if it doesn't exist yet
        let certs = &mut self.slot_state(slot).certificates;

        // check if the certificate is a duplicate
        let duplicate = match cert {
            Cert::Notar(_) => certs.notar.is_some(),
            Cert::NotarFallback(_) => certs
                .notar_fallback
                .iter()
                .any(|nf| nf.block_hash() == &cert.block_hash().unwrap()),
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

    /// Adds a new vote to the pool. Checks validity of the vote.
    async fn add_vote(&mut self, vote: Vote) -> Result<(), AddVoteError> {
        // ignore old and far-in-the-future votes
        let slot = vote.slot();
        // TODO: set bounds exactly correctly,
        //       use correct validator set & stake distribution
        let slot_far_in_future =
            Slot::new(self.highest_finalized_slot.inner() + 2 * SLOTS_PER_EPOCH);
        if slot < self.highest_finalized_slot || slot >= slot_far_in_future {
            return Err(AddVoteError::SlotOutOfBounds);
        }

        // verify signature
        let pk = &self.epoch_info.validator(vote.signer()).voting_pubkey;
        if !vote.check_sig(pk) {
            return Err(AddVoteError::InvalidSignature);
        }

        // check if vote is valid and should be counted
        let voter = vote.signer();
        let voter_stake = self.epoch_info.validator(voter).stake;
        if let Some(offence) = self.slot_state(slot).check_slashable_offence(&vote) {
            return Err(AddVoteError::Slashable(offence));
        } else if self.slot_state(slot).should_ignore_vote(&vote) {
            return Err(AddVoteError::Duplicate);
        }

        // actually add the vote
        trace!("adding vote to pool: {vote:?}");
        let (new_certs, votor_events, blocks_to_repair) =
            self.slot_state(slot).add_vote(vote, voter_stake);

        // handle any resulting events
        for cert in new_certs {
            self.add_valid_cert(cert).await;
        }
        for event in votor_events {
            self.votor_event_channel.send(event).await.unwrap();
        }
        for (slot, block_hash) in blocks_to_repair {
            self.repair_channel.send((slot, block_hash)).await.unwrap();
        }
        Ok(())
    }

    /// Registers a new block with its respective parent in the pool.
    ///
    /// This should be called once for every valid block (e.g. directly by blockstore).
    /// Ensures that the parent information is available for safe-to-notar checks.
    async fn add_block(&mut self, slot: Slot, block_info: BlockInfo) {
        let BlockInfo {
            hash: block_hash,
            parent_slot,
            parent_hash,
        } = block_info;
        self.slot_state(slot).notify_parent_known(block_hash);
        if let Some(parent_state) = self.slot_states.get(&parent_slot)
            && parent_state.is_notar_fallback(&parent_hash)
            && let Some(output) = self.slot_state(slot).notify_parent_certified(block_hash)
        {
            match output {
                Either::Left(event) => {
                    self.votor_event_channel.send(event).await.unwrap();
                }
                Either::Right((slot, hash)) => {
                    self.repair_channel.send((slot, hash)).await.unwrap();
                }
            }
            return;
        }
        self.s2n_waiting_parent_cert
            .insert((parent_slot, parent_hash), (slot, block_hash));
    }

    /// Triggers a recovery from a standstill.
    ///
    /// Determines which certificates and votes need to be re-broadcast.
    /// Emits the corresponding [`VotorEvent::Standstill`] event for Votor.
    /// Should be called after not seeing any progress for the standstill duration.
    async fn recover_from_standstill(&self) {
        let slot = self.highest_finalized_slot;
        let certs = self.get_certs(slot);
        let votes = self.get_own_votes(slot.next());

        warn!("recovering from standstill at slot {slot}");
        debug!(
            "re-broadcasting {} certificates and {} votes",
            certs.len(),
            votes.len()
        );

        // NOTE: This event corresponds to the slot after the last finalized one,
        //       this way it is ignored by `Votor` iff a new slot was finalized.
        let event = VotorEvent::Standstill(slot.next(), certs, votes);

        // send to votor for broadcasting
        self.votor_event_channel.send(event).await.unwrap();
    }

    /// Gives the currently highest finalized (fast or slow) slot.
    fn finalized_slot(&self) -> Slot {
        self.highest_finalized_slot
    }

    /// Returns all possible parents for the given slot that are ready.
    fn parents_ready(&self, slot: Slot) -> &[(Slot, Hash)] {
        self.parent_ready_tracker.parents_ready(slot)
    }

    fn wait_for_parent_ready(&mut self, slot: Slot) -> Either<BlockId, oneshot::Receiver<BlockId>> {
        self.parent_ready_tracker.wait_for_parent_ready(slot)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::consensus::cert::{FastFinalCert, NotarCert, SkipCert};
    use crate::crypto::aggsig::SecretKey;
    use crate::test_utils::generate_validators;
    use crate::types::SLOTS_PER_WINDOW;

    use tokio::sync::mpsc;

    #[tokio::test]
    async fn handle_invalid_votes() {
        let (_, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        let wrong_sk = SecretKey::new(&mut rand::rng());
        let vote = Vote::new_notar(Slot::new(0), Hash::default(), &wrong_sk, 0);
        assert_eq!(
            pool.add_vote(vote).await,
            Err(AddVoteError::InvalidSignature)
        );
    }

    #[tokio::test]
    async fn notarize_block() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // all nodes notarize block in slot 0
        assert!(!pool.is_notarized(Slot::new(0)));
        for v in 0..11 {
            let vote = Vote::new_notar(Slot::new(0), Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(Slot::new(0)));

        // just enough nodes notarize block in slot 1
        assert!(!pool.is_notarized(Slot::new(1)));
        for v in 0..7 {
            let vote = Vote::new_notar(Slot::new(1), Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(Slot::new(1)));

        // just NOT enough nodes notarize block in slot 2
        assert!(!pool.is_notarized(Slot::new(2)));
        for v in 0..6 {
            let vote = Vote::new_notar(Slot::new(2), Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_notarized(Slot::new(2)));
    }

    #[tokio::test]
    async fn skip_block() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // all nodes vote skip on slot 0
        assert!(!pool.is_skip_certified(Slot::new(0)));
        for v in 0..11 {
            let vote = Vote::new_skip(Slot::new(0), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_skip_certified(Slot::new(0)));

        // just enough nodes vote skip on slot 1
        assert!(!pool.is_skip_certified(Slot::new(1)));
        for v in 0..7 {
            let vote = Vote::new_skip(Slot::new(1), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_skip_certified(Slot::new(1)));

        // just NOT enough nodes notarize block in slot 2
        assert!(!pool.is_skip_certified(Slot::new(2)));
        for v in 0..6 {
            let vote = Vote::new_skip(Slot::new(2), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_skip_certified(Slot::new(2)));
    }

    #[tokio::test]
    async fn finalize_block() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // all nodes vote finalize on slot 0
        assert!(!pool.is_finalized(Slot::new(0)));
        for v in 0..11 {
            let vote = Vote::new_final(Slot::new(0), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(Slot::new(0)));
        assert!(pool.highest_finalized_slot == Slot::new(0));

        // just enough nodes vote finalize on slot 1
        assert!(!pool.is_finalized(Slot::new(1)));
        for v in 0..7 {
            let vote = Vote::new_final(Slot::new(1), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(Slot::new(1)));
        assert!(pool.highest_finalized_slot == Slot::new(1));

        // just NOT enough nodes vote finalize on slot 2
        assert!(!pool.is_finalized(Slot::new(2)));
        for v in 0..6 {
            let vote = Vote::new_final(Slot::new(2), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_finalized(Slot::new(2)));
        assert!(pool.highest_finalized_slot == Slot::new(1));
    }

    #[tokio::test]
    async fn fast_finalize_block() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // all nodes vote notarize on slot 0
        assert!(!pool.is_finalized(Slot::new(0)));
        for v in 0..11 {
            let vote = Vote::new_notar(Slot::new(0), Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(Slot::new(0)));
        assert!(pool.highest_finalized_slot == Slot::new(0));

        // just enough nodes to fast finalize slot 1
        assert!(!pool.is_finalized(Slot::new(1)));
        for v in 0..9 {
            let vote = Vote::new_notar(Slot::new(1), Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(Slot::new(1)));
        assert!(pool.highest_finalized_slot == Slot::new(1));

        // just NOT enough nodes to fast finalize slot 2
        assert!(!pool.is_finalized(Slot::new(2)));
        for v in 0..8 {
            let vote = Vote::new_notar(Slot::new(2), Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_finalized(Slot::new(2)));
        assert!(pool.highest_finalized_slot == Slot::new(1));
    }

    #[tokio::test]
    async fn simple_branch_certified() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        let window = Slot::new(0).slots_in_window().collect::<Vec<_>>();
        for slot in window.iter() {
            for v in 0..7 {
                let vote = Vote::new_notar(*slot, [slot.inner() as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }
        let slot = *window.last().unwrap();
        let next = slot.next();
        assert!(pool.is_parent_ready(next, (slot, [next.inner() as u8 - 1; 32])));
    }

    #[tokio::test]
    async fn branch_certified_notar_fallback() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // receive mixed notar & notar-fallback votes
        let window = Slot::new(0).slots_in_window().collect::<Vec<_>>();
        for slot in window.iter() {
            assert!(!pool.is_parent_ready(slot.next(), (*slot, [slot.inner() as u8; 32])));
            for v in 0..4 {
                let vote = Vote::new_notar(*slot, [slot.inner() as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
            for v in 4..7 {
                let vote =
                    Vote::new_notar_fallback(*slot, [slot.inner() as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }
        let slot = *window.last().unwrap();
        let next = slot.next();
        assert!(pool.is_parent_ready(next, (slot, [next.inner() as u8 - 1; 32])));
    }

    #[tokio::test]
    async fn branch_certified_out_of_order() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // first see skip votes for later slots
        let mut window = Slot::new(0).slots_in_window().collect::<Vec<_>>();
        assert!(window.len() > 2);
        window.remove(0);
        window.remove(0);
        for slot in window.iter() {
            for v in 0..7 {
                let vote = Vote::new_skip(*slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        let next = window.last().unwrap().next();
        // no blocks are valid parents yet
        assert!(pool.parents_ready(next).is_empty());

        // then see notarization votes for slot 1
        let slot_1 = Slot::new(1);
        for v in 0..7 {
            let vote = Vote::new_notar(slot_1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }

        // branch can only be certified once we saw votes other slots in window
        assert!(pool.is_parent_ready(next, (slot_1, [1; 32])));
        // no other blocks are valid parents
        assert_eq!(pool.parents_ready(next).len(), 1);
    }

    #[tokio::test]
    async fn branch_certified_late_cert() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info.clone(), votor_tx, repair_tx);

        // first see skip votes for later slots
        let mut window = Slot::new(0).slots_in_window().collect::<Vec<_>>();
        assert!(window.len() > 2);
        window.remove(0);
        window.remove(0);
        for slot in window.iter() {
            for v in 0..7 {
                let vote = Vote::new_skip(*slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // no blocks are valid parents yet
        let next = window.last().unwrap().next();
        assert!(pool.parents_ready(next).is_empty());

        // then receive notarization cert for slot 1
        let slot_1 = Slot::new(1);
        let mut votes = Vec::new();
        for v in 0..7 {
            votes.push(Vote::new_notar(slot_1, [1; 32], &sks[v as usize], v));
        }
        let cert = NotarCert::try_new(&votes, &epoch_info.validators).unwrap();
        pool.add_cert(Cert::Notar(cert)).await.unwrap();

        // branch can only be certified once we saw votes for parent
        assert!(pool.is_parent_ready(next, (slot_1, [1; 32])));
    }

    #[tokio::test]
    async fn regular_handover() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // notarize all slots of first window
        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_notar(Slot::new(slot), [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        assert!(pool.is_parent_ready(
            Slot::new(SLOTS_PER_WINDOW),
            (
                Slot::new(SLOTS_PER_WINDOW - 1),
                [(SLOTS_PER_WINDOW - 1) as u8; 32]
            )
        ));
    }

    #[tokio::test]
    async fn one_skip_handover() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // notarize all slots but last one
        for slot in 0..SLOTS_PER_WINDOW - 1 {
            for v in 0..7 {
                let vote = Vote::new_notar(Slot::new(slot), [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip last slot
        for v in 0..7 {
            let vote = Vote::new_skip(Slot::new(SLOTS_PER_WINDOW - 1), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }

        assert!(pool.is_parent_ready(
            Slot::new(SLOTS_PER_WINDOW),
            (
                Slot::new(SLOTS_PER_WINDOW - 2),
                [(SLOTS_PER_WINDOW - 2) as u8; 32]
            )
        ));
    }

    #[tokio::test]
    async fn two_skip_handover() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // notarize all slots but last two
        for slot in 0..SLOTS_PER_WINDOW - 2 {
            for v in 0..7 {
                let vote = Vote::new_notar(Slot::new(slot), [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip last 2 slots
        for v in 0..7 {
            let vote = Vote::new_skip(Slot::new(SLOTS_PER_WINDOW - 2), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        for v in 0..7 {
            let vote = Vote::new_skip(Slot::new(SLOTS_PER_WINDOW - 1), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }

        assert!(pool.is_parent_ready(
            Slot::new(SLOTS_PER_WINDOW),
            (
                Slot::new(SLOTS_PER_WINDOW - 3),
                [(SLOTS_PER_WINDOW - 3) as u8; 32]
            )
        ));
    }

    #[tokio::test]
    async fn skip_window_handover() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // notarize all slots in first window
        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_notar(Slot::new(slot), [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip all slots in second window
        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_skip(Slot::new(SLOTS_PER_WINDOW + slot), &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        assert!(pool.is_parent_ready(
            Slot::new(2 * SLOTS_PER_WINDOW),
            (
                Slot::new(SLOTS_PER_WINDOW - 1),
                [(SLOTS_PER_WINDOW - 1) as u8; 32]
            )
        ));
    }

    #[tokio::test]
    async fn pruning() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // all nodes vote finalize on 3 leader windows
        for slot in 0..3 * SLOTS_PER_WINDOW {
            let slot = Slot::new(slot);
            assert!(!pool.is_finalized(slot));
            for v in 0..11 {
                let vote = Vote::new_final(slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
            assert!(pool.is_finalized(slot));
        }
        let last_slot = Slot::new(3 * SLOTS_PER_WINDOW - 1);
        assert_eq!(pool.highest_finalized_slot, last_slot);

        // finalization triggers pruning, only last slot should be there
        for slot in 0..last_slot.inner() {
            let slot = Slot::new(slot);
            assert!(!pool.slot_states.contains_key(&slot));
        }
        assert!(pool.slot_states.contains_key(&(last_slot)));

        // NOT enough nodes vote finalize on next 10 slots
        for s in 1..=10 {
            let slot = Slot::new(last_slot.inner() + s);
            for v in 0..6 {
                let vote = Vote::new_final(slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
            assert!(!pool.is_finalized(slot));
        }
        assert_eq!(pool.highest_finalized_slot, last_slot);

        // these slots should still be there
        for s in 0..=10 {
            let slot = Slot::new(last_slot.inner() + s);
            assert!(pool.slot_states.contains_key(&slot));
        }

        // add one more vote each to finalize next 10 slots
        for s in 1..=10 {
            let slot = Slot::new(last_slot.inner() + s);
            let vote = Vote::new_final(slot, &sks[6], 6);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
            assert!(pool.is_finalized(slot));
        }
        assert_eq!(pool.highest_finalized_slot.inner(), last_slot.inner() + 10);

        // NOW first 10 slots should be gone
        for s in 0..10 {
            let slot = Slot::new(last_slot.inner() + s);
            assert!(!pool.slot_states.contains_key(&slot));
        }
        assert!(
            pool.slot_states
                .contains_key(&Slot::new(last_slot.inner() + 10))
        );
    }

    #[tokio::test]
    async fn duplicate_votes() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // insert a notar vote from validator 0
        let vote = Vote::new_notar(Slot::new(0), Hash::default(), &sks[0], 0);
        assert_eq!(pool.add_vote(vote).await, Ok(()));

        // insert a skip vote from validator 1
        let vote = Vote::new_skip(Slot::new(0), &sks[1], 1);
        assert_eq!(pool.add_vote(vote).await, Ok(()));

        // inserting same votes again should fail
        let vote = Vote::new_notar(Slot::new(0), Hash::default(), &sks[0], 0);
        assert_eq!(pool.add_vote(vote).await, Err(AddVoteError::Duplicate));
        let vote = Vote::new_skip(Slot::new(0), &sks[1], 1);
        assert_eq!(pool.add_vote(vote).await, Err(AddVoteError::Duplicate));
    }

    #[tokio::test]
    async fn duplicate_certs() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info.clone(), votor_tx, repair_tx);

        // insert a notar cert for first slot
        let mut votes = Vec::new();
        let first_slot = Slot::genesis().next();
        for v in 0..11 {
            votes.push(Vote::new_notar(first_slot, [1; 32], &sks[v as usize], v));
        }
        let notar_cert = NotarCert::try_new(&votes, &epoch_info.validators).unwrap();
        assert_eq!(pool.add_cert(Cert::Notar(notar_cert.clone())).await, Ok(()));

        // insert a skip cert for slot 1
        let mut votes = Vec::new();
        let second_slot = first_slot.next();
        for v in 0..11 {
            votes.push(Vote::new_skip(second_slot, &sks[v as usize], v));
        }
        let skip_cert = SkipCert::try_new(&votes, &epoch_info.validators).unwrap();
        assert_eq!(pool.add_cert(Cert::Skip(skip_cert.clone())).await, Ok(()));

        // inserting same certs again should fail
        assert_eq!(
            pool.add_cert(Cert::Notar(notar_cert)).await,
            Err(AddCertError::Duplicate)
        );
        assert_eq!(
            pool.add_cert(Cert::Skip(skip_cert)).await,
            Err(AddCertError::Duplicate)
        );
    }

    #[tokio::test]
    async fn out_of_bounds_votes() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info, votor_tx, repair_tx);

        // all nodes vote finalize last slot of 3rd leader windows
        let slot = Slot::new(3 * SLOTS_PER_WINDOW - 1);
        for v in 0..11 {
            let vote = Vote::new_notar(slot, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert_eq!(pool.highest_finalized_slot, slot);

        // dismiss old votes
        for slot in 0..3 * SLOTS_PER_WINDOW - 1 {
            for v in 0..11 {
                let vote = Vote::new_final(Slot::new(slot), &sks[v as usize], v);
                assert_eq!(
                    pool.add_vote(vote).await,
                    Err(AddVoteError::SlotOutOfBounds)
                );
            }
        }

        // dismiss far-in-the-future vote
        let slot = Slot::new(5 * SLOTS_PER_EPOCH);
        for v in 0..11 {
            let vote = Vote::new_final(slot, &sks[v as usize], v);
            assert_eq!(
                pool.add_vote(vote).await,
                Err(AddVoteError::SlotOutOfBounds)
            );
        }
    }

    #[tokio::test]
    async fn out_of_bounds_certs() {
        let (sks, epoch_info) = generate_validators(11);
        let (votor_tx, _votor_rx) = mpsc::channel(1024);
        let (repair_tx, _repair_rx) = mpsc::channel(1024);
        let mut pool = PoolImpl::new(epoch_info.clone(), votor_tx, repair_tx);

        // insert a notar cert for last slot of 3rd leader window
        let slot = Slot::new(3 * SLOTS_PER_WINDOW - 1);
        let mut votes = Vec::new();
        for v in 0..11 {
            votes.push(Vote::new_notar(slot, Hash::default(), &sks[v as usize], v));
        }
        let ff_cert = FastFinalCert::try_new(&votes, &epoch_info.validators).unwrap();
        assert_eq!(
            pool.add_cert(Cert::FastFinal(ff_cert.clone())).await,
            Ok(())
        );

        // dismiss old certs
        for slot in 0..3 * SLOTS_PER_WINDOW - 1 {
            let mut votes = Vec::new();
            for v in 0..11 {
                votes.push(Vote::new_skip(Slot::new(slot), &sks[v as usize], v));
            }
            let skip_cert = SkipCert::try_new(&votes, &epoch_info.validators).unwrap();
            assert_eq!(
                pool.add_cert(Cert::Skip(skip_cert.clone())).await,
                Err(AddCertError::SlotOutOfBounds)
            );
        }

        // dismiss far-in-the-future certs
        let slot = Slot::new(3 * SLOTS_PER_EPOCH);
        let mut votes = Vec::new();
        for v in 0..11 {
            votes.push(Vote::new_skip(slot, &sks[v as usize], v));
        }
        let skip_cert = SkipCert::try_new(&votes, &epoch_info.validators).unwrap();
        assert_eq!(
            pool.add_cert(Cert::Skip(skip_cert.clone())).await,
            Err(AddCertError::SlotOutOfBounds)
        );
    }
}
