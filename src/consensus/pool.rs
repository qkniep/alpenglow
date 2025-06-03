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

use log::{info, trace, warn};
use thiserror::Error;
use tokio::sync::mpsc::Sender;

use crate::crypto::Hash;
use crate::{Slot, ValidatorId};

use super::blockstore::BlockInfo;
use super::votor::VotorEvent;
use super::{Cert, EpochInfo, SLOTS_PER_EPOCH, SLOTS_PER_WINDOW, Vote};

use parent_ready_tracker::ParentReadyTracker;
use slot_state::SlotState;

// TODO: remove this?
const PRUNING_OFFSET: Slot = 64;

/// Errors the Pool may throw when adding a vote or certificate.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum PoolError {
    #[error("slot is either too old or too far in the future")]
    SlotOutOfBounds,
    #[error("invalid signature on vote/cert")]
    InvalidSignature,
    #[error("duplicate vote/cert")]
    Duplicate,
    #[error("vote constitutes a slashable offence")]
    Slashable(SlashableOffence),
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

/// Pool is the central consensus data structure.
/// It holds votes and certificates for each slot.
pub struct Pool {
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
}

impl Pool {
    /// Creates a new empty pool containing no votes or certificates.
    ///
    /// Any later emitted events will be sent on provided `votor_event_channel`.
    pub fn new(epoch_info: Arc<EpochInfo>, votor_event_channel: Sender<VotorEvent>) -> Self {
        Self {
            slot_states: BTreeMap::new(),
            parent_ready_tracker: ParentReadyTracker::new(),
            s2n_waiting_parent_cert: BTreeMap::new(),
            highest_notarized_fallback_slot: 0,
            highest_finalized_slot: 0,
            epoch_info,
            votor_event_channel,
        }
    }

    /// Adds a new certificate to the pool. Checks validity of the certificate.
    ///
    /// # Errors
    ///
    /// - Returns [`PoolError::SlotOutOfBounds`] if the slot is too old or too far in the future.
    /// - Returns [`PoolError::InvalidSignature`] if the certificate's signature is invalid.
    /// - Returns [`PoolError::Duplicate`] if the certificate can be ignored as duplicate.
    pub async fn add_cert(&mut self, cert: Cert) -> Result<(), PoolError> {
        // ignore old and far-in-the-future certificates
        let slot = cert.slot();
        // TODO: set bounds exactly correctly,
        //       use correct validator set & stake distribution
        if slot < self.highest_finalized_slot
            || slot == self.highest_finalized_slot + 2 * SLOTS_PER_EPOCH
        {
            return Err(PoolError::SlotOutOfBounds);
        }

        // verify signature
        if !cert.check_sig(&self.epoch_info.validators) {
            return Err(PoolError::InvalidSignature);
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
            return Err(PoolError::Duplicate);
        }

        self.add_valid_cert(cert).await;
        Ok(())
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
                if let Some(event) = self.slot_state(slot).notify_parent_certified(block_hash) {
                    self.votor_event_channel.send(event).await.unwrap();
                }
                let new_parents_ready = self
                    .parent_ready_tracker
                    .mark_notar_fallback((slot, block_hash));
                for (slot, (parent_slot, parent_hash)) in new_parents_ready {
                    assert_eq!(slot % SLOTS_PER_WINDOW, 0);
                    let event = VotorEvent::ParentReady {
                        slot,
                        parent_slot,
                        parent_hash,
                    };
                    self.votor_event_channel.send(event).await.unwrap();
                }
                self.highest_notarized_fallback_slot =
                    slot.max(self.highest_notarized_fallback_slot);
            }
            Cert::Skip(_) => {
                warn!("skipped slot {slot}");
                let newly_certified = self.parent_ready_tracker.mark_skipped(slot);
                for (slot, (parent_slot, parent_hash)) in newly_certified {
                    assert_eq!(slot % SLOTS_PER_WINDOW, 0);
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

    /// Adds a new vote to the pool. Checks validity of the vote.
    ///
    /// # Errors
    ///
    /// - Returns [`PoolError::SlotOutOfBounds`] if the slot is too old or too far in the future.
    /// - Returns [`PoolError::InvalidSignature`] if the vote's signature is invalid.
    /// - Returns [`PoolError::Slashable`] if the vote constitutes a slashable offence.
    /// - Returns [`PoolError::Duplicate`] if the can be ignored as duplicate.
    pub async fn add_vote(&mut self, vote: Vote) -> Result<(), PoolError> {
        // ignore old and far-in-the-future votes
        let slot = vote.slot();
        // TODO: set bounds exactly correctly,
        //       use correct validator set & stake distribution
        if slot < self.highest_finalized_slot
            || slot == self.highest_finalized_slot + 2 * SLOTS_PER_EPOCH
        {
            return Err(PoolError::SlotOutOfBounds);
        }

        // verify signature
        let pk = &self.epoch_info.validator(vote.signer()).voting_pubkey;
        if !vote.check_sig(pk) {
            return Err(PoolError::InvalidSignature);
        }

        // check if vote is valid and should be counted
        let voter = vote.signer();
        let voter_stake = self.epoch_info.validator(voter).stake;
        if let Some(offence) = self.slot_state(slot).check_slashable_offence(&vote) {
            return Err(PoolError::Slashable(offence));
        } else if self.slot_state(slot).should_ignore_vote(&vote) {
            return Err(PoolError::Duplicate);
        }

        // actually add the vote
        trace!("adding vote to pool: {vote:?}");
        let (new_certs, votor_events) = self.slot_state(slot).add_vote(vote, voter_stake);

        // handle any resulting events
        for cert in new_certs {
            self.add_valid_cert(cert).await;
        }
        for event in votor_events {
            self.votor_event_channel.send(event).await.unwrap();
        }
        Ok(())
    }

    /// Registers a new block with its respective parent in the pool.
    ///
    /// This should be called once for every valid block (e.g. directly by blockstore).
    /// Ensures that the parent information is available for safe-to-notar checks.
    pub async fn add_block(&mut self, slot: Slot, block_info: BlockInfo) {
        let BlockInfo {
            hash: block_hash,
            parent_slot,
            parent_hash,
        } = block_info;
        if let Some(parent_state) = self.slot_states.get(&parent_slot) {
            if parent_state.is_notar_fallback(&parent_hash) {
                if let Some(event) = self.slot_state(slot).notify_parent_certified(block_hash) {
                    self.votor_event_channel.send(event).await.unwrap();
                }
            } else {
                self.s2n_waiting_parent_cert
                    .insert((parent_slot, parent_hash), (slot, block_hash));
            }
        }
    }

    /// Triggers a recovery from a standstill.
    ///
    /// Should be called after not seeing any progress for the standstill duration.
    pub async fn recover_from_standstill(&self) {
        let slot = self.highest_finalized_slot;
        let certs = self.get_certs(slot);
        let votes = self.get_own_votes(slot + 1);

        let event = VotorEvent::Standstill(slot, certs, votes);
        self.votor_event_channel.send(event).await.unwrap();
    }

    /// Gives the currently highest finalized (fast or slow) slot.
    pub const fn finalized_slot(&self) -> Slot {
        self.highest_finalized_slot
    }

    /// Gives the current tip of the chain for block production.
    pub const fn get_tip(&self) -> Slot {
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

    /// Returns `true` iff the pool contains a notar(-fallback) certificate for the slot.
    pub fn is_notarized_fallback(&self, slot: Slot) -> bool {
        self.slot_states.get(&slot).is_some_and(|state| {
            state.certificates.notar.is_some() || !state.certificates.notar_fallback.is_empty()
        })
    }

    /// Returns `true` iff the given parent is ready for the given slot.
    ///
    /// This requires that the parent is at least notarized-fallback.
    /// Also, if the parent is in a slot before `slot-1`, then all slots in
    /// `parent+1..slot-1` must be skip-certified.
    pub fn is_parent_ready(&self, slot: Slot, parent: (Slot, Hash)) -> bool {
        self.parent_ready_tracker
            .parents_ready(slot)
            .contains(&parent)
    }

    /// Returns all possible parents for the given slot that are ready.
    pub fn parents_ready(&self, slot: Slot) -> &[(Slot, Hash)] {
        self.parent_ready_tracker.parents_ready(slot)
    }

    /// Returns `true` iff the pool contains a skip certificate for the slot.
    pub fn is_skip_certified(&self, slot: Slot) -> bool {
        self.slot_states
            .get(&slot)
            .is_some_and(|state| state.certificates.skip.is_some())
    }

    /// Cleans up old finalized slots from the pool.
    ///
    /// After this, [`Self::slot_states`] will only contain entries for slots
    /// >= [`Self::highest_finalized_slot`].
    pub fn prune(&mut self) {
        let last_slot = self
            .highest_finalized_slot
            .saturating_sub(PRUNING_OFFSET - 1);
        self.slot_states = self.slot_states.split_off(&last_slot);
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

    fn slot_state(&mut self, slot: Slot) -> &mut SlotState {
        self.slot_states
            .entry(slot)
            .or_insert_with(|| SlotState::new(slot, Arc::clone(&self.epoch_info)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::consensus::SLOTS_PER_WINDOW;
    use crate::consensus::cert::NotarCert;
    use crate::crypto::aggsig::SecretKey;
    use crate::test_utils::generate_validators;

    use tokio::sync::mpsc;

    #[tokio::test]
    async fn handle_invalid_votes() {
        let (_, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        let wrong_sk = SecretKey::new(&mut rand::rng());
        let vote = Vote::new_notar(0, Hash::default(), &wrong_sk, 0);
        assert_eq!(pool.add_vote(vote).await, Err(PoolError::InvalidSignature));
        drop(rx);
    }

    #[tokio::test]
    async fn notarize_block() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // all nodes notarize block in slot 0
        assert!(!pool.is_notarized(0));
        for v in 0..11 {
            let vote = Vote::new_notar(0, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(0));

        // just enough nodes notarize block in slot 1
        assert!(!pool.is_notarized(1));
        for v in 0..7 {
            let vote = Vote::new_notar(1, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));

        // just NOT enough nodes notarize block in slot 2
        assert!(!pool.is_notarized(2));
        for v in 0..6 {
            let vote = Vote::new_notar(2, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_notarized(2));
        drop(rx);
    }

    #[tokio::test]
    async fn skip_block() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // all nodes vote skip on slot 0
        assert!(!pool.is_skip_certified(0));
        for v in 0..11 {
            let vote = Vote::new_skip(0, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_skip_certified(0));

        // just enough nodes vote skip on slot 1
        assert!(!pool.is_skip_certified(1));
        for v in 0..7 {
            let vote = Vote::new_skip(1, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_skip_certified(1));

        // just NOT enough nodes notarize block in slot 2
        assert!(!pool.is_skip_certified(2));
        for v in 0..6 {
            let vote = Vote::new_skip(2, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_skip_certified(2));
        drop(rx);
    }

    #[tokio::test]
    async fn finalize_block() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // all nodes vote finalize on slot 0
        assert!(!pool.is_finalized(0));
        for v in 0..11 {
            let vote = Vote::new_final(0, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(0));
        assert!(pool.highest_finalized_slot == 0);

        // just enough nodes vote finalize on slot 1
        assert!(!pool.is_finalized(1));
        for v in 0..7 {
            let vote = Vote::new_final(1, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(1));
        assert!(pool.highest_finalized_slot == 1);

        // just NOT enough nodes vote finalize on slot 2
        assert!(!pool.is_finalized(2));
        for v in 0..6 {
            let vote = Vote::new_final(2, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_finalized(2));
        assert!(pool.highest_finalized_slot == 1);
        drop(rx);
    }

    #[tokio::test]
    async fn fast_finalize_block() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // all nodes vote notarize on slot 0
        assert!(!pool.is_finalized(0));
        for v in 0..11 {
            let vote = Vote::new_notar(0, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(0));
        assert!(pool.highest_finalized_slot == 0);

        // just enough nodes to fast finalize slot 1
        assert!(!pool.is_finalized(1));
        for v in 0..9 {
            let vote = Vote::new_notar(1, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(1));
        assert!(pool.highest_finalized_slot == 1);

        // just NOT enough nodes to fast finalize slot 2
        assert!(!pool.is_finalized(2));
        for v in 0..8 {
            let vote = Vote::new_notar(2, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_finalized(2));
        assert!(pool.highest_finalized_slot == 1);
        drop(rx);
    }

    #[tokio::test]
    async fn simple_branch_certified() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }
        assert!(pool.is_parent_ready(
            SLOTS_PER_WINDOW,
            (SLOTS_PER_WINDOW - 1, [SLOTS_PER_WINDOW as u8 - 1; 32])
        ));
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_notar_fallback() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // receive mixed notar & notar-fallback votes
        for slot in 0..SLOTS_PER_WINDOW {
            assert!(!pool.is_parent_ready(slot + 1, (slot, [slot as u8; 32])));
            for v in 0..4 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
            for v in 4..7 {
                let vote = Vote::new_notar_fallback(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }
        assert!(pool.is_parent_ready(
            SLOTS_PER_WINDOW,
            (SLOTS_PER_WINDOW - 1, [SLOTS_PER_WINDOW as u8 - 1; 32])
        ));
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_out_of_order() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // first see skip votes for later slots
        assert!(SLOTS_PER_WINDOW > 2);
        for slot in 2..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_skip(slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }
        // no blocks are valid parents yet
        assert!(pool.parents_ready(SLOTS_PER_WINDOW).is_empty());

        // then see notarization votes for slot 1
        for v in 0..7 {
            let vote = Vote::new_notar(1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }

        // branch can only be certified once we saw votes other slots in window
        assert!(pool.is_parent_ready(SLOTS_PER_WINDOW, (1, [1; 32])));
        // no other blocks are valid parents
        assert_eq!(pool.parents_ready(SLOTS_PER_WINDOW).len(), 1);
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_late_cert() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info.clone(), tx);

        // first see skip votes for later slots
        for slot in 2..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_skip(slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }
        // no blocks are valid parents yet
        assert!(pool.parents_ready(SLOTS_PER_WINDOW).is_empty());

        // then receive notarization cert for slot 1
        let mut votes = Vec::new();
        for v in 0..7 {
            votes.push(Vote::new_notar(1, [1; 32], &sks[v as usize], v));
        }
        let cert = NotarCert::try_new(&votes, &epoch_info.validators).unwrap();
        pool.add_cert(Cert::Notar(cert)).await.unwrap();

        // branch can only be certified once we saw votes for parent
        assert!(pool.is_parent_ready(SLOTS_PER_WINDOW, (1, [1; 32])));
        drop(rx);
    }

    #[tokio::test]
    async fn regular_handover() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // notarize all slots of first window
        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        assert!(pool.is_parent_ready(
            SLOTS_PER_WINDOW,
            (SLOTS_PER_WINDOW - 1, [(SLOTS_PER_WINDOW - 1) as u8; 32])
        ));
        drop(rx);
    }

    #[tokio::test]
    async fn one_skip_handover() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // notarize all slots but last one
        for slot in 0..SLOTS_PER_WINDOW - 1 {
            for v in 0..7 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip last slot
        for v in 0..7 {
            let vote = Vote::new_skip(SLOTS_PER_WINDOW - 1, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }

        assert!(pool.is_parent_ready(
            SLOTS_PER_WINDOW,
            (SLOTS_PER_WINDOW - 2, [(SLOTS_PER_WINDOW - 2) as u8; 32])
        ));
        drop(rx);
    }

    #[tokio::test]
    async fn two_skip_handover() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // notarize all slots but last two
        for slot in 0..SLOTS_PER_WINDOW - 2 {
            for v in 0..7 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip last 2 slots
        for v in 0..7 {
            let vote = Vote::new_skip(SLOTS_PER_WINDOW - 2, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        for v in 0..7 {
            let vote = Vote::new_skip(SLOTS_PER_WINDOW - 1, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }

        assert!(pool.is_parent_ready(
            SLOTS_PER_WINDOW,
            (SLOTS_PER_WINDOW - 3, [(SLOTS_PER_WINDOW - 3) as u8; 32])
        ));
        drop(rx);
    }

    #[tokio::test]
    async fn skip_window_handover() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // notarize all slots in first window
        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip all slots in second window
        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..7 {
                let vote = Vote::new_skip(SLOTS_PER_WINDOW + slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        assert!(pool.is_parent_ready(
            2 * SLOTS_PER_WINDOW,
            (SLOTS_PER_WINDOW - 1, [(SLOTS_PER_WINDOW - 1) as u8; 32])
        ));
        drop(rx);
    }

    #[tokio::test]
    async fn pruning() {
        let (sks, epoch_info) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(epoch_info, tx);

        // all nodes vote finalize on [`PRUNING_OFFSET`] slots
        for slot in 0..PRUNING_OFFSET {
            assert!(!pool.is_finalized(slot));
            for v in 0..11 {
                let vote = Vote::new_final(slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
            assert!(pool.is_finalized(slot));
        }
        assert_eq!(pool.highest_finalized_slot, PRUNING_OFFSET - 1);

        // after pruning all slots should still be there
        pool.prune();
        for slot in 0..PRUNING_OFFSET {
            assert!(pool.is_finalized(slot));
            assert!(pool.slot_states.contains_key(&slot));
        }

        // NOT enough nodes vote finalize on next 10 slots
        for s in 0..10 {
            let slot = PRUNING_OFFSET + s;
            for v in 0..6 {
                let vote = Vote::new_final(slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
            assert!(!pool.is_finalized(slot));
        }
        assert_eq!(pool.highest_finalized_slot, PRUNING_OFFSET - 1);

        // first 10 slots should still be there
        for slot in 0..10 {
            assert!(pool.slot_states.contains_key(&slot));
        }

        // add one more vote each to finalize next 10 slots
        for s in 0..10 {
            let slot = PRUNING_OFFSET + s;
            let vote = Vote::new_final(slot, &sks[6], 6);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
            assert!(pool.is_finalized(slot));
        }
        assert_eq!(pool.highest_finalized_slot, PRUNING_OFFSET + 9);

        // NOW first 10 slots should be gone
        for slot in 0..10 {
            assert!(!pool.slot_states.contains_key(&slot));
        }

        // other slots should still be there
        for slot in 10..PRUNING_OFFSET + 10 {
            assert!(pool.slot_states.contains_key(&slot));
        }

        drop(rx);
    }
}
