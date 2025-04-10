// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure handling votes and certificates.
//!
//!

use std::collections::BTreeMap;
use std::sync::Arc;

use smallvec::SmallVec;
use thiserror::Error;
use tokio::sync::mpsc::Sender;
use tracing::{debug, error, info, trace};

use crate::crypto::Hash;
use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

use super::cert::{FastFinalCert, FinalCert, NotarCert, NotarFallbackCert, SkipCert};
use super::vote::VoteKind;
use super::votor::VotorEvent;
use super::{Cert, Vote};

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
    /// Map from block (slot, hash) to parent block (slot, hash).
    parents: BTreeMap<(Slot, Hash), (Slot, Hash)>,
    /// Map from parent block (slot, hash) to block (slot, hash) waiting on
    /// branch certified status of its parent.
    pending_branch_certified: BTreeMap<(Slot, Hash), (Slot, Hash)>,
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

struct SlotState {
    /// Votes for this slot, contains all vote types and validators.
    votes: SlotVotes,
    /// Running stake totals for different types of votes.
    voted_stakes: SlotVotedStake,
    /// Certificates for this slot, contains all certificate types and validators.
    certificates: SlotCertificates,
    /// Indicates if a block hash in this slot is branch certified, that is,
    /// it and all its ancestors are notarized(-fallback).
    branch_certified: Option<Hash>,
    /// Information about all validators active in this slot.
    validators: Arc<Vec<ValidatorInfo>>,
    /// Total amount of stake active for this slot.
    total_stake: Stake,
}

// PERF: replace storing Votes (50% size overhead) with storing only signatures?
struct SlotVotes {
    notar: Vec<Option<(Hash, Vote)>>,
    notar_fallback: Vec<Vec<(Hash, Vote)>>,
    skip: Vec<Option<Vote>>,
    skip_fallback: Vec<Option<Vote>>,
    finalize: Vec<Option<Vote>>,
}

#[derive(Default)]
struct SlotVotedStake {
    notar: BTreeMap<Hash, Stake>,
    notar_fallback: BTreeMap<Hash, Stake>,
    skip: Stake,
    finalize: Stake,
    /// Amount of stake for which we have either notar or skip vote.
    notar_or_skip: Stake,
    /// Maximum amount of stake that voted notar on the same block.
    top_notar: Stake,
}

#[derive(Default)]
struct SlotCertificates {
    notar: Option<NotarCert>,
    notar_fallback: Option<NotarFallbackCert>,
    skip: Option<SkipCert>,
    fast_finalize: Option<FastFinalCert>,
    finalize: Option<FinalCert>,
}

impl Pool {
    /// Creates a new empty pool with no votes.
    ///
    /// Any events will later be sent on [`Pool::votor_event_channel`].
    pub fn new(validators: Vec<ValidatorInfo>, votor_event_channel: Sender<VotorEvent>) -> Self {
        Self {
            slot_states: BTreeMap::new(),
            parents: BTreeMap::new(),
            pending_branch_certified: BTreeMap::new(),
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

        // initilize slot state if it doesn't exist yet
        let slot_state = self
            .slot_states
            .entry(cert.slot())
            .or_insert_with(|| SlotState::new(self.validators.clone()));
        let certs = &mut slot_state.certificates;

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
        let slot_state = self
            .slot_states
            .entry(slot)
            .or_insert_with(|| SlotState::new(self.validators.clone()));

        // actually add certificate
        trace!("adding cert to pool: {:?}", cert);
        slot_state.add_cert(cert.clone());

        // handle resulting state updates
        match &cert {
            Cert::Notar(_) | Cert::NotarFallback(_) => {
                let block_hash = cert.block_hash().unwrap();
                self.check_branch_certified(cert.slot(), block_hash).await;
                self.highest_notarized_fallback_slot =
                    slot.max(self.highest_notarized_fallback_slot);
            }
            Cert::FastFinal(_) => {
                info!("fast finalized slot {slot}");
                let block_hash = cert.block_hash().unwrap();
                self.check_branch_certified(cert.slot(), block_hash).await;
                if self.branch_certified_hash(slot) == Some(block_hash) {
                    self.highest_finalized_slot = slot.max(self.highest_finalized_slot);
                }
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

    /// Recursively checks if branch and its ancestors are certified.
    /// Sends [`VotorEvent::BranchCertified`] for each newly certified block.
    async fn check_branch_certified(&mut self, slot: Slot, block_hash: Hash) {
        let newly_certified = self.check_branch_certified_internal(slot, block_hash, Vec::new());

        for (slot, block_hash) in newly_certified {
            self.votor_event_channel
                .send(VotorEvent::BranchCertified(slot, block_hash))
                .await
                .unwrap();
        }
    }

    /// Performs actual checking and recursion over ancestors.
    ///
    /// Ancestors are checked only if the branch-certified status changed.
    /// This separation circumvents the difficulties of recursive async functions,
    /// by keeping access to the async channel only in `check_branch_certified`.
    fn check_branch_certified_internal(
        &mut self,
        slot: Slot,
        block_hash: Hash,
        mut certified_so_far: Vec<(Slot, Hash)>,
    ) -> Vec<(Slot, Hash)> {
        debug!(slot, "check_branch_certified");
        let hash = &hex::encode(block_hash)[..8];

        let Some((parent_slot, parent_hash)) = self.parents.get(&(slot, block_hash)) else {
            debug!("no parent: {slot} {hash}");
            return certified_so_far;
        };

        if !self.is_notarized_fallback(slot) && !self.is_notarized(slot) {
            debug!("not notarized: {slot} {hash}");
            return certified_so_far;
        }

        let parent_certified =
            slot == 0 || self.branch_certified_hash(*parent_slot) == Some(*parent_hash);
        if !parent_certified {
            debug!("parent not certified: {slot} {hash}");
            self.pending_branch_certified
                .insert((*parent_slot, *parent_hash), (slot, block_hash));
            return certified_so_far;
        }

        let slot_state = self
            .slot_states
            .entry(slot)
            .or_insert_with(|| SlotState::new(self.validators.clone()));
        if slot_state.branch_certified.is_some() {
            debug!("already certified: {slot} {hash}");
            return certified_so_far;
        }

        debug!("newly certified: {slot} {hash}");
        slot_state.branch_certified = Some(block_hash);
        certified_so_far.push((slot, block_hash));
        let pending = self.pending_branch_certified.remove(&(slot, block_hash));
        if let Some((pending_slot, pending_hash)) = pending {
            debug!("now checking ancestors");
            self.check_branch_certified_internal(pending_slot, pending_hash, certified_so_far)
        } else {
            certified_so_far
        }
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

        // initilize slot state if it doesn't exist yet
        let slot_state = self
            .slot_states
            .entry(slot)
            .or_insert_with(|| SlotState::new(Arc::clone(&self.validators)));

        // check if vote is valid and should be counted
        let voter = vote.signer();
        let voter_stake = self.validators[voter as usize].stake;
        if let Some(offence) = slot_state.check_slashable_offence(&vote) {
            return Err(PoolError::Slashable(offence));
        } else if slot_state.should_ignore_vote(&vote) {
            return Err(PoolError::Duplicate);
        }

        // actually add the vote
        trace!("adding vote to pool: {:?}", vote);
        let (new_certs, votor_events) = slot_state.add_vote(vote, voter_stake);

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
        if self.parents.contains_key(&(slot, block_hash)) {
            let hash = &hex::encode(block_hash)[..8];
            error!("pool: block already added: {slot} {hash}");
            return;
        }
        let hash = &hex::encode(block_hash)[..8];
        let hash2 = &hex::encode(parent_hash)[..8];
        debug!("pool: added block {slot} {hash} with parent {parent_slot} {hash2}");
        self.parents
            .insert((slot, block_hash), (parent_slot, parent_hash));
        self.check_branch_certified(slot, block_hash).await;
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

    /// Returns the block hash the pool currently sees as branch certified for this slot, if any.
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
}

impl SlotState {
    fn new(validators: Arc<Vec<ValidatorInfo>>) -> Self {
        let total_stake = validators.iter().map(|v| v.stake).sum();
        Self {
            votes: SlotVotes::new(validators.len()),
            voted_stakes: SlotVotedStake::default(),
            certificates: SlotCertificates::default(),
            branch_certified: None,
            validators,
            total_stake,
        }
    }

    fn add_cert(&mut self, cert: Cert) {
        match cert {
            Cert::Notar(n) => self.certificates.notar = Some(n),
            Cert::NotarFallback(n) => self.certificates.notar_fallback = Some(n),
            Cert::Skip(s) => self.certificates.skip = Some(s),
            Cert::FastFinal(s) => self.certificates.fast_finalize = Some(s),
            Cert::Final(f) => self.certificates.finalize = Some(f),
        }
    }

    fn add_vote(
        &mut self,
        vote: Vote,
        voter_stake: Stake,
    ) -> (SmallVec<[Cert; 2]>, SmallVec<[VotorEvent; 2]>) {
        let slot = vote.slot();
        let voter = vote.signer();
        let v = voter as usize;
        match vote.kind() {
            VoteKind::Notar(_, _) => {
                let block_hash = vote.block_hash().unwrap();
                self.votes.notar[v] = Some((block_hash, vote));
                self.count_notar_stake(slot, &block_hash, voter_stake)
            }
            VoteKind::NotarFallback(_, _) => {
                let block_hash = vote.block_hash().unwrap();
                self.votes.notar_fallback[v].push((block_hash, vote));
                self.count_notar_fallback_stake(&block_hash, voter_stake)
            }
            VoteKind::Skip(_) => {
                self.votes.skip[v] = Some(vote);
                self.voted_stakes.notar_or_skip += voter_stake;
                self.count_skip_stake(slot, voter_stake)
            }
            VoteKind::SkipFallback(_) => {
                self.votes.skip_fallback[v] = Some(vote);
                self.count_skip_stake(slot, voter_stake)
            }
            VoteKind::Final(_) => {
                self.votes.finalize[v] = Some(vote);
                self.count_finalize_stake(voter_stake)
            }
        }
    }

    const fn is_weak_quorum(&self, stake: Stake) -> bool {
        stake >= (self.total_stake * 2).div_ceil(5)
    }

    const fn is_quorum(&self, stake: Stake) -> bool {
        stake >= (self.total_stake * 3).div_ceil(5)
    }

    const fn is_strong_quorum(&self, stake: Stake) -> bool {
        stake >= (self.total_stake * 4).div_ceil(5)
    }

    /// Adds a given amount of `stake` to notarization counter for `block_hash`.
    /// Then, checks if a new notarization certificate can be created.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    fn count_notar_stake(
        &mut self,
        slot: Slot,
        block_hash: &Hash,
        stake: Stake,
    ) -> (SmallVec<[Cert; 2]>, SmallVec<[VotorEvent; 2]>) {
        let mut new_certs = SmallVec::new();
        let mut votor_events = SmallVec::new();

        // increment stake
        let notar_stake = self.voted_stakes.notar.entry(*block_hash).or_insert(0);
        *notar_stake += stake;
        self.voted_stakes.notar_or_skip += stake;
        let notar_stake = *notar_stake;

        // check quorums
        if notar_stake > self.voted_stakes.top_notar {
            self.voted_stakes.top_notar = notar_stake;
        }
        if self.is_weak_quorum(notar_stake) {
            // if self.votes.notar.get(self. {
            votor_events.push(VotorEvent::SafeToNotar(slot, *block_hash));
            // } else {
            //     unimplemented!()
            //     }
        }
        if self.is_weak_quorum(self.voted_stakes.notar_or_skip - self.voted_stakes.top_notar) {
            votor_events.push(VotorEvent::SafeToSkip(slot));
        }
        if self.is_quorum(notar_stake) && self.certificates.notar.is_none() {
            let votes = self.votes.notar_votes(block_hash);
            let cert = NotarCert::new_unchecked(&votes, &self.validators);
            new_certs.push(Cert::Notar(cert));
        }
        if self.is_strong_quorum(notar_stake) && self.certificates.fast_finalize.is_none() {
            let votes = self.votes.notar_votes(block_hash);
            let cert = FastFinalCert::new_unchecked(&votes, &self.validators);
            new_certs.push(Cert::FastFinal(cert));
        }

        (new_certs, votor_events)
    }

    /// Adds a given amount of `stake` to notar-fallback counter for `block_hash`.
    /// Then, checks if a new notar-fallback certificate can be created.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    fn count_notar_fallback_stake(
        &mut self,
        block_hash: &Hash,
        stake: Stake,
    ) -> (SmallVec<[Cert; 2]>, SmallVec<[VotorEvent; 2]>) {
        let mut new_certs = SmallVec::new();
        let nf_stake = self
            .voted_stakes
            .notar_fallback
            .entry(*block_hash)
            .or_insert(0);
        *nf_stake += stake;
        let nf_stake = *nf_stake;
        let notar_stake = *self.voted_stakes.notar.get(block_hash).unwrap_or(&0);
        if self.is_quorum(nf_stake + notar_stake) && self.certificates.notar_fallback.is_none() {
            let mut votes = self.votes.notar_votes(block_hash);
            votes.extend(self.votes.notar_fallback_votes(block_hash));
            let cert = NotarFallbackCert::new_unchecked(&votes, &self.validators);
            new_certs.push(Cert::NotarFallback(cert));
        }
        (new_certs, SmallVec::new())
    }

    /// Adds a given amount of `stake` to skip counter for `slot`.
    /// Then, checks if a new skip certificate can be created.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    fn count_skip_stake(
        &mut self,
        slot: Slot,
        stake: Stake,
    ) -> (SmallVec<[Cert; 2]>, SmallVec<[VotorEvent; 2]>) {
        let mut new_certs = SmallVec::new();
        let mut votor_events = SmallVec::new();
        self.voted_stakes.skip += stake;
        if self.is_quorum(self.voted_stakes.skip) && self.certificates.skip.is_none() {
            let mut votes = self.votes.skip_votes();
            votes.extend(self.votes.skip_fallback_votes());
            let cert = SkipCert::new_unchecked(&votes, &self.validators);
            new_certs.push(Cert::Skip(cert));
            votor_events.push(VotorEvent::SkipCertified(slot));
        }
        if self.is_weak_quorum(self.voted_stakes.notar_or_skip - self.voted_stakes.top_notar) {
            votor_events.push(VotorEvent::SafeToSkip(slot));
        }
        (new_certs, votor_events)
    }

    /// Adds a given amount of `stake` to finalization counter for `slot`.
    /// Then, checks if a new finalization certificate can be created.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    fn count_finalize_stake(
        &mut self,
        stake: Stake,
    ) -> (SmallVec<[Cert; 2]>, SmallVec<[VotorEvent; 2]>) {
        let mut new_certs = SmallVec::new();
        self.voted_stakes.finalize += stake;
        if self.is_quorum(self.voted_stakes.finalize) && self.certificates.finalize.is_none() {
            let votes: Vec<_> = self.votes.final_votes();
            let cert = FinalCert::new_unchecked(&votes, &self.validators);
            new_certs.push(Cert::Final(cert));
        }
        (new_certs, SmallVec::new())
    }

    /// Checks whether the given vote constitutes a slashable offence.
    ///
    /// This has to be called before dismissing potential duplicates, as
    /// according to `should_ignore_vote()`.
    fn check_slashable_offence(&self, vote: &Vote) -> Option<SlashableOffence> {
        let slot = vote.slot();
        let voter = vote.signer();
        let v = voter as usize;
        match vote.kind() {
            VoteKind::Notar(_, _) => {
                let block_hash = vote.block_hash().unwrap();
                if self.votes.skip[v].is_some() {
                    return Some(SlashableOffence::SkipAndNotarize(voter, slot));
                }
                if let Some((old_hash, _)) = self.votes.notar[v] {
                    if block_hash != old_hash {
                        return Some(SlashableOffence::NotarDifferentHash(voter, slot));
                    }
                }
            }
            VoteKind::NotarFallback(_, _) => {
                if self.votes.finalize[v].is_some() {
                    return Some(SlashableOffence::NotarFallbackAndFinalize(voter, slot));
                }
            }
            VoteKind::Skip(_) => {
                if self.votes.finalize[v].is_some() {
                    return Some(SlashableOffence::SkipAndFinalize(voter, slot));
                } else if self.votes.notar[v].is_some() {
                    return Some(SlashableOffence::SkipAndNotarize(voter, slot));
                }
            }
            VoteKind::SkipFallback(_) => {
                if self.votes.finalize[v].is_some() {
                    return Some(SlashableOffence::SkipAndFinalize(voter, slot));
                }
            }
            VoteKind::Final(_) => {
                if self.votes.skip[v].is_some() || self.votes.skip_fallback[v].is_some() {
                    return Some(SlashableOffence::SkipAndFinalize(voter, slot));
                } else if !self.votes.notar_fallback[v].is_empty() {
                    return Some(SlashableOffence::NotarFallbackAndFinalize(voter, slot));
                }
            }
        }
        None
    }

    /// Checks whether the given vote should be ignored as a duplicate.
    ///
    /// Votes for which this returns `true` should never be counted.
    /// Doing so could lead to double counting.
    fn should_ignore_vote(&self, vote: &Vote) -> bool {
        let v = vote.signer() as usize;
        match vote.kind() {
            VoteKind::Notar(_, _) => self.votes.notar[v].is_some(),
            VoteKind::NotarFallback(_, _) => self.votes.notar_fallback[v]
                .iter()
                .any(|(hash, _)| hash == vote.block_hash().as_ref().unwrap()),
            VoteKind::Skip(_) | VoteKind::SkipFallback(_) => {
                self.votes.skip[v].is_some() || self.votes.skip_fallback[v].is_some()
            }
            VoteKind::Final(_) => self.votes.finalize[v].is_some(),
        }
    }
}

impl SlotVotes {
    fn new(num_validators: usize) -> Self {
        Self {
            notar: vec![None; num_validators],
            notar_fallback: vec![Vec::new(); num_validators],
            skip: vec![None; num_validators],
            skip_fallback: vec![None; num_validators],
            finalize: vec![None; num_validators],
        }
    }

    fn notar_votes(&self, block_hash: &Hash) -> Vec<Vote> {
        self.notar
            .iter()
            .filter(|o| o.is_some() && &o.as_ref().unwrap().0 == block_hash)
            .map(|o| o.as_ref().unwrap().1.clone())
            .collect()
    }

    fn notar_fallback_votes(&self, block_hash: &Hash) -> Vec<Vote> {
        self.notar_fallback
            .iter()
            .flatten()
            .filter(|(h, _)| *h == *block_hash)
            .map(|(_, s)| s.clone())
            .collect()
    }

    fn skip_votes(&self) -> Vec<Vote> {
        self.skip.iter().filter_map(|o| o.clone()).collect()
    }

    fn skip_fallback_votes(&self) -> Vec<Vote> {
        self.skip_fallback
            .iter()
            .filter_map(|o| o.clone())
            .collect()
    }

    fn final_votes(&self) -> Vec<Vote> {
        self.finalize.iter().filter_map(|x| x.clone()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::consensus::SLOTS_PER_WINDOW;
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

        pool.add_block(0, [0; 32], 0, Hash::default()).await;
        pool.add_block(1, [1; 32], 0, [0; 32]).await;

        assert!(!pool.is_notarized(0));
        assert!(!pool.is_branch_certified(0));
        for v in 0..11 {
            let vote = Vote::new_notar(0, [0; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(0));
        assert!(pool.is_branch_certified(0));

        assert!(!pool.is_notarized(1));
        assert!(!pool.is_branch_certified(1));
        for v in 0..11 {
            let vote = Vote::new_notar(1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));
        assert!(pool.is_branch_certified(1));
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_delayed_block() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        pool.add_block(0, [0; 32], 0, Hash::default()).await;

        assert!(!pool.is_notarized(0));
        assert!(!pool.is_branch_certified(0));
        for v in 0..11 {
            let vote = Vote::new_notar(0, [0; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(0));
        assert!(pool.is_branch_certified(0));

        assert!(!pool.is_notarized(1));
        for v in 0..11 {
            let vote = Vote::new_notar(1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));
        assert!(!pool.is_branch_certified(1));

        // branch can only be certified once we know the parent
        pool.add_block(1, [1; 32], 0, [0; 32]).await;
        assert!(pool.is_branch_certified(1));
        drop(rx);
    }

    #[tokio::test]
    async fn branch_certified_out_of_order() {
        let (sks, validators) = generate_validators(11);
        let (tx, rx) = mpsc::channel(1024);
        let mut pool = Pool::new(validators, tx);

        // register blocks with their parents
        pool.add_block(0, [0; 32], 0, Hash::default()).await;
        pool.add_block(1, [1; 32], 0, [0; 32]).await;

        // receive votes out of order
        assert!(!pool.is_notarized(1));
        for v in 0..11 {
            let vote = Vote::new_notar(1, [1; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(1));
        assert!(!pool.is_branch_certified(1));

        assert!(!pool.is_notarized(0));
        for v in 0..11 {
            let vote = Vote::new_notar(0, [0; 32], &sks[v as usize], v);
            assert_eq!(pool.add_vote(vote).await, Ok(()));
        }
        assert!(pool.is_notarized(0));
        assert!(pool.is_branch_certified(0));

        // branch can only be certified once we saw votes for parent
        assert!(pool.is_branch_certified(1));
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
