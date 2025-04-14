// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure handling votes and certificates.
//!
//! Any received votes or certificates are placed into the pool.
//! The pool then tracks status for each slot and sends notification to votor.

mod slot_state;
mod valid_to_root_tracker;

use std::collections::BTreeMap;
use std::sync::Arc;

use log::{error, info, trace};
use thiserror::Error;
use tokio::sync::mpsc::Sender;

use crate::crypto::Hash;
use crate::{Slot, ValidatorId, ValidatorInfo};

use super::votor::VotorEvent;
use super::{Cert, Vote};

use slot_state::SlotState;
use valid_to_root_tracker::ValidToRootTracker;

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
// TODO: prune old state (especially votes)!
pub struct Pool {
    /// State for each slot. Contains all votes and certificates.
    slot_states: BTreeMap<Slot, SlotState>,
    /// Keeps track of which blocks are branch-certified.
    branch_certified_tracker: ValidToRootTracker,
    /// Highest slot that is at least notarized fallabck.
    highest_notarized_fallback_slot: Slot,
    /// Highest slot that was finalized or fast-finalized.
    highest_finalized_slot: Slot,
    /// Highest slot that has a finalization certificate (not fast-finalized).
    highest_slow_finalized_slot: Slot,
    /// Information about all active validators.
    // TODO: replace with EpochInfo
    validators: Arc<Vec<ValidatorInfo>>,
    /// Channel for sending events related to voting logic to Votor.
    votor_event_channel: Sender<VotorEvent>,
}

impl Pool {
    /// Creates a new empty pool with no votes.
    ///
    /// Any events will later be sent on [`Pool::votor_event_channel`].
    pub fn new(validators: Vec<ValidatorInfo>, votor_event_channel: Sender<VotorEvent>) -> Self {
        Self {
            slot_states: BTreeMap::new(),
            branch_certified_tracker: ValidToRootTracker::new(),
            highest_notarized_fallback_slot: 0,
            highest_finalized_slot: 0,
            highest_slow_finalized_slot: 0,
            validators: Arc::new(validators),
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
        // TODO: put epoch length in here
        if slot < self.highest_finalized_slot || slot == self.highest_finalized_slot + 2 * 100_000 {
            return Err(PoolError::SlotOutOfBounds);
        }

        // verify signature
        if !cert.check_sig(&self.validators) {
            return Err(PoolError::InvalidSignature);
        }

        // get `SlotCertificates`, initialize if it doesn't exist yet
        let certs = &mut self.slot_state(slot).certificates;

        // check if the certificate is a duplicate
        let duplicate = match cert {
            Cert::Notar(_) => certs.notar.is_some(),
            Cert::NotarFallback(_) => certs.notar_fallback.is_some(),
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
                let newly_certified = self.branch_certified_tracker.mark_valid((slot, block_hash));
                for (slot, hash) in newly_certified {
                    let event = VotorEvent::BranchCertified(slot, hash);
                    self.votor_event_channel.send(event).await.unwrap();
                    self.slot_state(slot).branch_certified = Some(hash);
                }
                self.highest_notarized_fallback_slot =
                    slot.max(self.highest_notarized_fallback_slot);
            }
            Cert::FastFinal(_) => {
                info!("fast finalized slot {slot}");
                let block_hash = cert.block_hash().unwrap();
                let id = (slot, block_hash);
                let newly_certified = self.branch_certified_tracker.mark_valid(id);
                for (slot, hash) in newly_certified {
                    let event = VotorEvent::BranchCertified(slot, hash);
                    self.votor_event_channel.send(event).await.unwrap();
                    self.slot_state(slot).branch_certified = Some(hash);
                }
                self.highest_finalized_slot = slot.max(self.highest_finalized_slot);
            }
            Cert::Final(_) => {
                info!("slow finalized slot {slot}");
                self.highest_slow_finalized_slot = slot.max(self.highest_slow_finalized_slot);
                self.highest_finalized_slot = slot.max(self.highest_finalized_slot);
            }
            _ => {}
        };

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
        // TODO: put epoch length in here
        if slot < self.highest_finalized_slot || slot == self.highest_finalized_slot + 2 * 100_000 {
            return Err(PoolError::SlotOutOfBounds);
        }

        // verify signature
        let pk = &self.validators[vote.signer() as usize].voting_pubkey;
        if !vote.check_sig(pk) {
            return Err(PoolError::InvalidSignature);
        }

        // check if vote is valid and should be counted
        let voter = vote.signer();
        let voter_stake = self.validators[voter as usize].stake;
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
    /// Ensures that the parent information is available for branch-certified checks.
    pub async fn add_block(
        &mut self,
        slot: Slot,
        block_hash: Hash,
        parent_slot: Slot,
        parent_hash: Hash,
    ) {
        let id = (slot, block_hash);
        let parent = (parent_slot, parent_hash);
        let newly_certified = self.branch_certified_tracker.add_with_parent(id, parent);
        for (slot, hash) in newly_certified {
            let event = VotorEvent::BranchCertified(slot, hash);
            self.votor_event_channel.send(event).await.unwrap();
            self.slot_state(slot).branch_certified = Some(hash);
        }
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
        if let Some(state) = self.slot_states.get(&slot) {
            state.certificates.fast_finalize.is_some() || state.certificates.finalize.is_some()
        } else {
            false
        }
    }

    /// Returns `true` iff the pool contains a notarization certificate for the slot.
    pub fn is_notarized(&self, slot: Slot) -> bool {
        self.slot_states
            .get(&slot)
            .is_some_and(|state| state.certificates.notar.is_some())
    }

    /// Returns `true` iff the pool contains a notar(-fallback) certificate for the slot.
    pub fn is_notarized_fallback(&self, slot: Slot) -> bool {
        if let Some(state) = self.slot_states.get(&slot) {
            state.certificates.notar.is_some() || state.certificates.notar_fallback.is_some()
        } else {
            false
        }
    }

    /// Returns the block hash the pool currently sees as branch certified in this slot, if any.
    pub fn branch_certified_hash(&self, slot: Slot) -> Option<Hash> {
        self.slot_states
            .get(&slot)
            .and_then(|state| state.branch_certified)
    }

    /// Returns `true` iff the pool currently sees this slot as branch certified.
    ///
    /// That is, if the pool contains notar(-fallback) certificates for a block
    /// in the given slot and all its ancestors.
    pub fn is_branch_certified(&self, slot: Slot) -> bool {
        self.branch_certified_hash(slot).is_some()
    }

    /// Returns `true` iff the pool contains a skip certificate for the slot.
    pub fn is_skip_certified(&self, slot: Slot) -> bool {
        self.slot_states
            .get(&slot)
            .is_some_and(|state| state.certificates.skip.is_some())
    }

    /// Cleans up old finalized slots from the certificate pool.
    /// After this `slot_states` only contain entries >= `finalized_slot`.
    pub fn prune(&mut self) {
        self.slot_states = self
            .slot_states
            .split_off(&self.highest_slow_finalized_slot);
    }

    fn slot_state(&mut self, slot: Slot) -> &mut SlotState {
        self.slot_states
            .entry(slot)
            .or_insert_with(|| SlotState::new(Arc::clone(&self.validators)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::consensus::SLOTS_PER_WINDOW;
    use crate::consensus::cert::NotarCert;
    use crate::crypto::aggsig::SecretKey;
    use crate::crypto::signature;

    use tokio::sync::mpsc;

    fn generate_validators(num_validators: u64) -> (Vec<SecretKey>, Vec<ValidatorInfo>) {
        let mut rng = rand::rng();
        let mut sks = Vec::new();
        let mut voting_sks = Vec::new();
        let mut validators = Vec::new();
        for i in 0..num_validators {
            sks.push(signature::SecretKey::new(&mut rng));
            voting_sks.push(SecretKey::new(&mut rng));
            validators.push(ValidatorInfo {
                id: i,
                stake: 1,
                pubkey: sks[i as usize].to_pk(),
                voting_pubkey: voting_sks[i as usize].to_pk(),
                all2all_address: String::new(),
                disseminator_address: String::new(),
                repair_address: String::new(),
            });
        }
        (voting_sks, validators)
    }

    #[tokio::test]
    async fn handle_invalid_votes() {
        let (_, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        let wrong_sk = SecretKey::new(&mut rand::rng());
        let vote = Vote::new_notar(0, Hash::default(), &wrong_sk, 0);
        assert_eq!(pool.add_vote(vote).await, Err(PoolError::InvalidSignature));
        drop(rx);
    }

    #[tokio::test]
    async fn notarize_block() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

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
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

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
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        // all nodes vote finalize on slot 0
        assert!(!pool.is_finalized(0));
        for v in 0..11 {
            let vote = Vote::new_final(0, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(0));
        assert!(pool.highest_slow_finalized_slot == 0);

        // just enough nodes vote finalize on slot 1
        assert!(!pool.is_finalized(1));
        for v in 0..7 {
            let vote = Vote::new_final(1, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(1));
        assert!(pool.highest_slow_finalized_slot == 1);

        // just NOT enough nodes vote finalize on slot 2
        assert!(!pool.is_finalized(2));
        for v in 0..6 {
            let vote = Vote::new_final(2, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_finalized(2));
        assert!(pool.highest_slow_finalized_slot == 1);
        drop(rx);
    }

    #[tokio::test]
    async fn fast_finalize_block() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        pool.add_block(0, Hash::default(), 0, Hash::default()).await;
        pool.add_block(1, Hash::default(), 0, Hash::default()).await;
        pool.add_block(2, Hash::default(), 1, Hash::default()).await;

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
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        pool.add_block(1, [1; 32], 0, [0; 32]).await;
        pool.add_block(2, [2; 32], 1, [1; 32]).await;

        assert!(!pool.is_notarized(1));
        assert!(!pool.is_branch_certified(1));
        for v in 0..7 {
            let vote = Vote::new_notar(1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));
        assert!(pool.is_branch_certified(1));

        assert!(!pool.is_notarized(2));
        assert!(!pool.is_branch_certified(2));
        for v in 0..7 {
            let vote = Vote::new_notar(2, [2; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(2));
        assert!(pool.is_branch_certified(2));
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_notar_fallback() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        pool.add_block(1, [1; 32], 0, [0; 32]).await;
        pool.add_block(2, [2; 32], 1, [1; 32]).await;

        assert!(!pool.is_notarized(1));
        assert!(!pool.is_branch_certified(1));
        for v in 0..7 {
            let vote = Vote::new_notar(1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));
        assert!(pool.is_branch_certified(1));

        // receive mixed notar & notar-fallback votes
        assert!(!pool.is_notarized(2));
        assert!(!pool.is_branch_certified(2));
        for v in 0..4 {
            let vote = Vote::new_notar(2, [2; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        for v in 4..7 {
            let vote = Vote::new_notar_fallback(2, [2; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(!pool.is_notarized(2));
        assert!(pool.is_branch_certified(2));
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_delayed_block() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        pool.add_block(1, [1; 32], 0, [0; 32]).await;

        assert!(!pool.is_notarized(1));
        assert!(!pool.is_branch_certified(1));
        for v in 0..7 {
            let vote = Vote::new_notar(1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));
        assert!(pool.is_branch_certified(1));

        assert!(!pool.is_notarized(2));
        for v in 0..7 {
            let vote = Vote::new_notar(2, [2; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(2));
        assert!(!pool.is_branch_certified(2));

        // branch can only be certified once we know the parent
        pool.add_block(2, [2; 32], 1, [1; 32]).await;
        assert!(pool.is_branch_certified(2));
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_out_of_order() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        // register blocks with their parents
        pool.add_block(1, [1; 32], 0, [0; 32]).await;
        pool.add_block(2, [2; 32], 1, [1; 32]).await;

        // receive votes out of order
        assert!(!pool.is_notarized(2));
        for v in 0..7 {
            let vote = Vote::new_notar(2, [2; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(2));
        assert!(!pool.is_branch_certified(2));

        assert!(!pool.is_notarized(1));
        for v in 0..7 {
            let vote = Vote::new_notar(1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));
        assert!(pool.is_branch_certified(1));

        // branch can only be certified once we saw votes for parent
        assert!(pool.is_branch_certified(2));
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_late_cert() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators.clone(), tx);

        // register blocks with their parents
        pool.add_block(1, [1; 32], 0, [0; 32]).await;
        pool.add_block(2, [2; 32], 1, [1; 32]).await;

        // receive votes out of order
        assert!(!pool.is_notarized(2));
        for v in 0..7 {
            let vote = Vote::new_notar(2, [2; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(2));
        assert!(!pool.is_branch_certified(2));

        // receive late cert
        assert!(!pool.is_notarized(1));
        assert!(!pool.is_branch_certified(1));
        let mut votes = Vec::new();
        for v in 0..7 {
            votes.push(Vote::new_notar(1, [1; 32], &sks[v as usize], v));
        }
        let cert = NotarCert::try_new(&votes, &validators).unwrap();
        pool.add_cert(Cert::Notar(cert)).await.unwrap();
        assert!(pool.is_notarized(1));
        assert!(pool.is_branch_certified(1));

        // branch can only be certified once we saw votes for parent
        assert!(pool.is_branch_certified(2));
        drop(rx);
    }

    #[tokio::test]
    async fn regular_handover() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        // register blocks with their parents
        for slot in 0..SLOTS_PER_WINDOW + 1 {
            let parent_slot = slot.saturating_sub(1);
            pool.add_block(slot, [slot as u8; 32], parent_slot, [parent_slot as u8; 32])
                .await;
        }

        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..11 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        assert!(!pool.is_notarized(SLOTS_PER_WINDOW));
        for v in 0..11 {
            let vote = Vote::new_notar(
                SLOTS_PER_WINDOW,
                [SLOTS_PER_WINDOW as u8; 32],
                &sks[v as usize],
                v,
            );
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(SLOTS_PER_WINDOW));
        assert!(pool.is_branch_certified(SLOTS_PER_WINDOW));
        drop(rx);
    }

    #[tokio::test]
    async fn one_skip_handover() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        // register blocks with their parents
        for slot in 0..SLOTS_PER_WINDOW {
            let parent_slot = slot.saturating_sub(1);
            pool.add_block(slot, [slot as u8; 32], parent_slot, [parent_slot as u8; 32])
                .await;
        }
        let parent_slot = SLOTS_PER_WINDOW - 2;
        pool.add_block(
            SLOTS_PER_WINDOW,
            [SLOTS_PER_WINDOW as u8; 32],
            parent_slot,
            [parent_slot as u8; 32],
        )
        .await;

        // notarize all slots but last one
        for slot in 0..SLOTS_PER_WINDOW - 1 {
            for v in 0..11 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip last slot
        for v in 0..11 {
            let vote = Vote::new_skip(SLOTS_PER_WINDOW - 1, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }

        // notarize first slot of next window
        assert!(!pool.is_notarized(SLOTS_PER_WINDOW));
        for v in 0..11 {
            let vote = Vote::new_notar(
                SLOTS_PER_WINDOW,
                [SLOTS_PER_WINDOW as u8; 32],
                &sks[v as usize],
                v,
            );
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(SLOTS_PER_WINDOW));
        assert!(pool.is_branch_certified(SLOTS_PER_WINDOW));
        drop(rx);
    }

    #[tokio::test]
    async fn two_skip_handover() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        // register blocks with their parents
        for slot in 0..SLOTS_PER_WINDOW {
            let parent_slot = slot.saturating_sub(1);
            pool.add_block(slot, [slot as u8; 32], parent_slot, [parent_slot as u8; 32])
                .await;
        }
        let parent_slot = SLOTS_PER_WINDOW - 3;
        pool.add_block(
            SLOTS_PER_WINDOW,
            [SLOTS_PER_WINDOW as u8; 32],
            parent_slot,
            [parent_slot as u8; 32],
        )
        .await;

        // notarize all slots but last two
        for slot in 0..SLOTS_PER_WINDOW - 2 {
            for v in 0..11 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip last 2 slots
        for v in 0..11 {
            let vote = Vote::new_skip(SLOTS_PER_WINDOW - 2, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        for v in 0..11 {
            let vote = Vote::new_skip(SLOTS_PER_WINDOW - 1, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }

        // notarize first slot of next window
        assert!(!pool.is_notarized(SLOTS_PER_WINDOW));
        for v in 0..11 {
            let vote = Vote::new_notar(
                SLOTS_PER_WINDOW,
                [SLOTS_PER_WINDOW as u8; 32],
                &sks[v as usize],
                v,
            );
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(SLOTS_PER_WINDOW));
        assert!(pool.is_branch_certified(SLOTS_PER_WINDOW));
        drop(rx);
    }

    #[tokio::test]
    async fn skip_window_handover() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        // register blocks with their parents
        for slot in 0..2 * SLOTS_PER_WINDOW {
            let parent_slot = slot.saturating_sub(1);
            pool.add_block(slot, [slot as u8; 32], parent_slot, [parent_slot as u8; 32])
                .await;
        }
        let parent_slot = SLOTS_PER_WINDOW - 1;
        pool.add_block(
            2 * SLOTS_PER_WINDOW,
            [2 * SLOTS_PER_WINDOW as u8; 32],
            parent_slot,
            [parent_slot as u8; 32],
        )
        .await;

        // notarize all slots in first window
        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..11 {
                let vote = Vote::new_notar(slot, [slot as u8; 32], &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // skip all slots in second window
        for slot in 0..SLOTS_PER_WINDOW {
            for v in 0..11 {
                let vote = Vote::new_skip(SLOTS_PER_WINDOW + slot, &sks[v as usize], v);
                assert_eq!(pool.add_vote(vote).await, Ok(()));
            }
        }

        // notarize first slot of third window
        assert!(!pool.is_notarized(2 * SLOTS_PER_WINDOW));
        for v in 0..11 {
            let vote = Vote::new_notar(
                2 * SLOTS_PER_WINDOW,
                [2 * SLOTS_PER_WINDOW as u8; 32],
                &sks[v as usize],
                v,
            );
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(2 * SLOTS_PER_WINDOW));
        assert!(pool.is_branch_certified(2 * SLOTS_PER_WINDOW));
        drop(rx);
    }

    #[tokio::test]
    async fn pruning() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        // all nodes vote notarize on slot 0
        assert!(!pool.is_finalized(0));
        for v in 0..11 {
            let vote = Vote::new_notar(0, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(0));

        // just enough nodes notarize block in slot 1
        assert!(!pool.is_notarized(1));
        for v in 0..7 {
            let vote = Vote::new_notar(1, Hash::default(), &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));

        // after pruning both slots should still be there
        pool.prune();
        assert!(pool.is_finalized(0));
        assert!(pool.is_notarized(1));
        assert!(pool.slot_states.contains_key(&0));
        assert!(pool.slot_states.contains_key(&1));

        // just enough nodes vote finalize on slot 2
        assert!(!pool.is_finalized(2));
        for v in 0..7 {
            let vote = Vote::new_final(2, &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_finalized(2));

        // after pruning NOW slots 0 and 1 should be gone
        pool.prune();
        assert!(!pool.slot_states.contains_key(&0));
        assert!(!pool.slot_states.contains_key(&1));
        drop(rx);
    }
}
