// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structures handling votes and certificates for a single slot.
//!
//! The main data structure defined here is [`SlotState`], which has components:
//! - [`SlotVotes`] for all votes in a single slot.
//! - [`SlotVotedStake`] for all running stake totals in a single slot.
//! - [`SlotCertificates`] for all certificates in a single slot.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use either::Either;
use smallvec::SmallVec;

use super::SlashableOffence;
use crate::consensus::cert::{FastFinalCert, FinalCert, NotarCert, NotarFallbackCert, SkipCert};
use crate::consensus::vote::VoteKind;
use crate::consensus::votor::VotorEvent;
use crate::consensus::{Cert, EpochInfo, Vote};
use crate::crypto::merkle::BlockHash;
use crate::{BlockId, Slot, Stake};

/// Data structure holding pool state for a single slot.
pub struct SlotState {
    /// Votes for this slot, contains all vote types and validators.
    pub(super) votes: SlotVotes,
    /// Running stake totals for different types of votes.
    pub(super) voted_stakes: SlotVotedStake,
    /// Certificates for this slot, contains all certificate types and validators.
    pub(super) certificates: SlotCertificates,
    /// Indicates blocks for which we already know their parents.
    parents: BTreeMap<BlockHash, ParentStatus>,
    /// Hashes of blocks that have reached the necessary votes for safe-to-notar
    /// and are only waiting for our only vote to arrive.
    pending_safe_to_notar: BTreeSet<BlockHash>,
    /// Hashes of blocks for which safe-to-notar has already been reached.
    sent_safe_to_notar: BTreeSet<BlockHash>,
    /// Indicates if safe-to-skip has already been sent for this slot.
    sent_safe_to_skip: bool,

    /// The slot this state is for.
    slot: Slot,
    /// Information about all validators active in this slot.
    pub(super) epoch_info: Arc<EpochInfo>,
}

// PERF: replace storing Votes (50% size overhead) with storing only signatures?
pub struct SlotVotes {
    /// Notarization votes for all validators (indexed by `ValidatorId`).
    pub(super) notar: Vec<Option<Vote>>,
    /// Notar-fallback votes for all validators (indexed by `ValidatorId`).
    pub(super) notar_fallback: Vec<BTreeMap<BlockHash, Vote>>,
    /// Skip votes for all validators (indexed by `ValidatorId`).
    pub(super) skip: Vec<Option<Vote>>,
    /// Skip-fallback votes for all validators (indexed by `ValidatorId`).
    pub(super) skip_fallback: Vec<Option<Vote>>,
    /// Finalization votes for all validators (indexed by `ValidatorId`).
    pub(super) finalize: Vec<Option<Vote>>,
}

#[derive(Default)]
pub struct SlotVotedStake {
    /// Amount of stake for each block has for which we have a notarization vote.
    pub(super) notar: BTreeMap<BlockHash, Stake>,
    /// Amount of stake for each block hash for which we have a notar-fallback vote.
    pub(super) notar_fallback: BTreeMap<BlockHash, Stake>,
    /// Amount of stake for which we have a skip vote.
    pub(super) skip: Stake,
    /// Amount of stake for which we have a skip-fallback vote.
    pub(super) skip_fallback: Stake,
    /// Amount of stake for which we have a finalization vote.
    pub(super) finalize: Stake,
    /// Amount of stake for which we have either notar or skip vote.
    pub(super) notar_or_skip: Stake,
    /// Maximum amount of stake that voted notar on the same block.
    pub(super) top_notar: Stake,
}

#[derive(Default)]
pub struct SlotCertificates {
    /// Notarization certificate for this slot, if it exists.
    pub(super) notar: Option<NotarCert>,
    /// Notar-fallback certificates for this slot, if any.
    pub(super) notar_fallback: Vec<NotarFallbackCert>,
    /// Skip certificate for this slot, if it exists.
    pub(super) skip: Option<SkipCert>,
    /// Fast finalization certificate for this slot, if it exists.
    pub(super) fast_finalize: Option<FastFinalCert>,
    /// Finalization certificate for this slot, if it exists.
    pub(super) finalize: Option<FinalCert>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParentStatus {
    Known,
    Certified,
}

/// Possible states for the safe-to-notar check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SafeToNotarStatus {
    SafeToNotar,
    MissingBlock,
    AwaitingVotes,
}

type SlotStateOutputs = (
    SmallVec<[Cert; 2]>,
    SmallVec<[VotorEvent; 2]>,
    SmallVec<[(Slot, BlockHash); 1]>,
);

impl SlotState {
    /// Creates a new container for votes and certificates for a single slot.
    ///
    /// Initially, it is completely empty.
    pub fn new(slot: Slot, epoch_info: Arc<EpochInfo>) -> Self {
        Self {
            votes: SlotVotes::new(epoch_info.validators.len()),
            voted_stakes: SlotVotedStake::default(),
            certificates: SlotCertificates::default(),
            parents: BTreeMap::new(),
            pending_safe_to_notar: BTreeSet::new(),
            sent_safe_to_notar: BTreeSet::new(),
            sent_safe_to_skip: false,

            slot,
            epoch_info,
        }
    }

    /// Adds a certificate to this slot.
    pub fn add_cert(&mut self, cert: Cert) {
        match cert {
            Cert::Notar(n) => self.certificates.notar = Some(n),
            Cert::NotarFallback(n) => {
                if !self.is_notar_fallback(n.block_hash()) {
                    self.certificates.notar_fallback.push(n);
                }
            }
            Cert::Skip(s) => self.certificates.skip = Some(s),
            Cert::FastFinal(s) => self.certificates.fast_finalize = Some(s),
            Cert::Final(f) => self.certificates.finalize = Some(f),
        }
    }

    /// Adds a vote to this slot.
    ///
    /// Handles updating the corresponding running stake totals, creating any
    /// new certificates and checking other conditions, like safe-to-notar.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    pub fn add_vote(&mut self, vote: Vote, voter_stake: Stake) -> SlotStateOutputs {
        let slot = vote.slot();
        let voter = vote.signer();
        let v = voter as usize;

        let (certs_created, mut votor_events, mut blocks_to_repair) = match vote.kind() {
            VoteKind::Notar(_, block_hash) => {
                let outputs = self.count_notar_stake(slot, block_hash, voter_stake);
                self.votes.notar[v] = Some(vote);
                outputs
            }
            VoteKind::NotarFallback(_, block_hash) => {
                let outputs = self.count_notar_fallback_stake(block_hash, voter_stake);
                let res = self.votes.notar_fallback[v].insert(block_hash.clone(), vote);
                assert!(res.is_none());
                outputs
            }
            VoteKind::Skip(_) => {
                self.votes.skip[v] = Some(vote);
                self.voted_stakes.notar_or_skip += voter_stake;
                self.count_skip_stake(slot, voter_stake, false)
            }
            VoteKind::SkipFallback(_) => {
                self.votes.skip_fallback[v] = Some(vote);
                self.count_skip_stake(slot, voter_stake, true)
            }
            VoteKind::Final(_) => {
                self.votes.finalize[v] = Some(vote);
                self.count_finalize_stake(voter_stake)
            }
        };

        // own vote might have made a block safe-to-notar
        if voter == self.epoch_info.own_id {
            for hash in self.pending_safe_to_notar.clone() {
                if self.sent_safe_to_notar.contains(&hash) {
                    continue;
                }
                match self.check_safe_to_notar(hash.clone()) {
                    SafeToNotarStatus::SafeToNotar => {
                        votor_events.push(VotorEvent::SafeToNotar(slot, hash));
                    }
                    SafeToNotarStatus::MissingBlock => blocks_to_repair.push((slot, hash)),
                    SafeToNotarStatus::AwaitingVotes => {}
                }
            }
        }

        (certs_created, votor_events, blocks_to_repair)
    }

    /// Mark the parent of the block given by `hash` as known (in Blokstor).
    pub fn notify_parent_known(&mut self, hash: BlockHash) {
        self.parents.entry(hash).or_insert(ParentStatus::Known);
    }

    /// Mark the parent of the block given by `hash` as notarized-fallback.
    ///
    /// # Panics
    ///
    /// If [`SlotState::notify_parent_known`] has not yet been called for this block.
    pub fn notify_parent_certified(
        &mut self,
        hash: BlockHash,
    ) -> Option<Either<VotorEvent, BlockId>> {
        let Some(parent_info) = self.parents.get_mut(&hash) else {
            panic!("parent not known")
        };
        *parent_info = ParentStatus::Certified;

        // potentially emit safe-to-notar
        if self.sent_safe_to_notar.contains(&hash) {
            return None;
        }
        match self.check_safe_to_notar(hash.clone()) {
            SafeToNotarStatus::SafeToNotar => {
                Some(Either::Left(VotorEvent::SafeToNotar(self.slot, hash)))
            }
            SafeToNotarStatus::MissingBlock => Some(Either::Right((self.slot, hash))),
            SafeToNotarStatus::AwaitingVotes => None,
        }
    }

    fn is_weakest_quorum(&self, stake: Stake) -> bool {
        stake >= (self.epoch_info.total_stake()).div_ceil(5)
    }

    fn is_weak_quorum(&self, stake: Stake) -> bool {
        stake >= (self.epoch_info.total_stake() * 2).div_ceil(5)
    }

    fn is_quorum(&self, stake: Stake) -> bool {
        stake >= (self.epoch_info.total_stake() * 3).div_ceil(5)
    }

    fn is_strong_quorum(&self, stake: Stake) -> bool {
        stake >= (self.epoch_info.total_stake() * 4).div_ceil(5)
    }

    /// Adds a given amount of `stake` to notarization counter for `block_hash`.
    /// Then, checks if a new notarization certificate can be created.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    fn count_notar_stake(
        &mut self,
        slot: Slot,
        block_hash: &BlockHash,
        stake: Stake,
    ) -> SlotStateOutputs {
        let mut new_certs = SmallVec::new();
        let mut votor_events = SmallVec::new();
        let mut blocks_to_repair = SmallVec::new();

        // increment stake
        let notar_stake = self
            .voted_stakes
            .notar
            .entry(block_hash.clone())
            .or_insert(0);
        *notar_stake += stake;
        self.voted_stakes.notar_or_skip += stake;
        let notar_stake = *notar_stake;
        self.voted_stakes.top_notar = notar_stake.max(self.voted_stakes.top_notar);

        // check quorums
        if !self.sent_safe_to_notar.contains(block_hash) {
            match self.check_safe_to_notar(block_hash.clone()) {
                SafeToNotarStatus::SafeToNotar => {
                    votor_events.push(VotorEvent::SafeToNotar(slot, block_hash.clone()));
                }
                SafeToNotarStatus::MissingBlock => {
                    blocks_to_repair.push((slot, block_hash.clone()));
                }
                SafeToNotarStatus::AwaitingVotes => {}
            }
        }
        if !self.sent_safe_to_skip
            && self.is_weak_quorum(self.voted_stakes.notar_or_skip - self.voted_stakes.top_notar)
            && self.votes.notar[self.epoch_info.own_id as usize].is_some()
        {
            votor_events.push(VotorEvent::SafeToSkip(slot));
            self.sent_safe_to_skip = true;
        }
        let nf_stake = *self
            .voted_stakes
            .notar_fallback
            .get(block_hash)
            .unwrap_or(&0);
        if self.is_quorum(nf_stake + notar_stake) && !self.is_notar_fallback(block_hash) {
            let mut votes = self.votes.notar_votes(block_hash);
            votes.extend(self.votes.notar_fallback_votes(block_hash));
            let cert = NotarFallbackCert::new_unchecked(&votes, &self.epoch_info.validators);
            new_certs.push(Cert::NotarFallback(cert));
        }
        if self.is_quorum(notar_stake) && self.certificates.notar.is_none() {
            let votes = self.votes.notar_votes(block_hash);
            let cert = NotarCert::new_unchecked(&votes, &self.epoch_info.validators);
            new_certs.push(Cert::Notar(cert));
        }
        if self.is_strong_quorum(notar_stake) && self.certificates.fast_finalize.is_none() {
            let votes = self.votes.notar_votes(block_hash);
            let cert = FastFinalCert::new_unchecked(&votes, &self.epoch_info.validators);
            new_certs.push(Cert::FastFinal(cert));
        }

        (new_certs, votor_events, blocks_to_repair)
    }

    /// Adds a given amount of `stake` to notar-fallback counter for `block_hash`.
    /// Then, checks if a new notar-fallback certificate can be created.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    fn count_notar_fallback_stake(
        &mut self,
        block_hash: &BlockHash,
        stake: Stake,
    ) -> SlotStateOutputs {
        let mut new_certs = SmallVec::new();
        let nf_stakes = &mut self.voted_stakes.notar_fallback;
        let nf_stake = nf_stakes.entry(block_hash.clone()).or_insert(0);
        *nf_stake += stake;
        let nf_stake = *nf_stake;
        let notar_stake = *self.voted_stakes.notar.get(block_hash).unwrap_or(&0);
        if self.is_quorum(nf_stake + notar_stake) && !self.is_notar_fallback(block_hash) {
            let mut votes = self.votes.notar_votes(block_hash);
            votes.extend(self.votes.notar_fallback_votes(block_hash));
            let cert = NotarFallbackCert::new_unchecked(&votes, &self.epoch_info.validators);
            new_certs.push(Cert::NotarFallback(cert));
        }
        (new_certs, SmallVec::new(), SmallVec::new())
    }

    /// Adds a given amount of `stake` to skip counter for `slot`.
    /// Then, checks if a new skip certificate can be created.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    fn count_skip_stake(&mut self, slot: Slot, stake: Stake, fallback: bool) -> SlotStateOutputs {
        let mut new_certs = SmallVec::new();
        let mut votor_events = SmallVec::new();
        let mut blocks_to_repair = SmallVec::new();
        if fallback {
            self.voted_stakes.skip_fallback += stake;
        } else {
            self.voted_stakes.skip += stake;
        }
        // PERF: clone on every skip vote
        for hash in self.pending_safe_to_notar.clone() {
            if self.sent_safe_to_notar.contains(&hash) {
                continue;
            }
            match self.check_safe_to_notar(hash.clone()) {
                SafeToNotarStatus::SafeToNotar => {
                    votor_events.push(VotorEvent::SafeToNotar(slot, hash));
                }
                SafeToNotarStatus::MissingBlock => blocks_to_repair.push((slot, hash)),
                SafeToNotarStatus::AwaitingVotes => {}
            }
        }
        let total_skip_stake = self.voted_stakes.skip + self.voted_stakes.skip_fallback;
        if self.is_quorum(total_skip_stake) && self.certificates.skip.is_none() {
            let mut votes = self.votes.skip_votes();
            votes.extend(self.votes.skip_fallback_votes());
            let cert = SkipCert::new_unchecked(&votes, &self.epoch_info.validators);
            new_certs.push(Cert::Skip(cert));
        }
        if !self.sent_safe_to_skip
            && self.is_weak_quorum(self.voted_stakes.notar_or_skip - self.voted_stakes.top_notar)
            && self.votes.notar[self.epoch_info.own_id as usize].is_some()
        {
            votor_events.push(VotorEvent::SafeToSkip(slot));
            self.sent_safe_to_skip = true;
        }
        (new_certs, votor_events, blocks_to_repair)
    }

    /// Adds a given amount of `stake` to finalization counter for `slot`.
    /// Then, checks if a new finalization certificate can be created.
    ///
    /// Returns potentially created certificates and newly emitted votor events.
    fn count_finalize_stake(&mut self, stake: Stake) -> SlotStateOutputs {
        let mut new_certs = SmallVec::new();
        self.voted_stakes.finalize += stake;
        if self.is_quorum(self.voted_stakes.finalize) && self.certificates.finalize.is_none() {
            let votes: Vec<_> = self.votes.final_votes();
            let cert = FinalCert::new_unchecked(&votes, &self.epoch_info.validators);
            new_certs.push(Cert::Final(cert));
        }
        (new_certs, SmallVec::new(), SmallVec::new())
    }

    /// Checks whether the given vote constitutes a slashable offence.
    ///
    /// This has to be called before dismissing potential duplicates, as
    /// according to `should_ignore_vote()`.
    pub fn check_slashable_offence(&self, vote: &Vote) -> Option<SlashableOffence> {
        let slot = vote.slot();
        let voter = vote.signer();
        let v = voter as usize;
        match vote.kind() {
            VoteKind::Notar(_, block_hash) => {
                if self.votes.skip[v].is_some() {
                    return Some(SlashableOffence::SkipAndNotarize(voter, slot));
                }
                if let Some(notar_vote) = &self.votes.notar[v]
                    && block_hash != notar_vote.block_hash().unwrap()
                {
                    return Some(SlashableOffence::NotarDifferentHash(voter, slot));
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
    pub fn should_ignore_vote(&self, vote: &Vote) -> bool {
        let v = vote.signer() as usize;
        match vote.kind() {
            VoteKind::Notar(_, _) => self.votes.notar[v].is_some(),
            VoteKind::NotarFallback(_, block_hash) => {
                self.votes.notar_fallback[v].contains_key(block_hash)
            }
            VoteKind::Skip(_) | VoteKind::SkipFallback(_) => {
                self.votes.skip[v].is_some() || self.votes.skip_fallback[v].is_some()
            }
            VoteKind::Final(_) => self.votes.finalize[v].is_some(),
        }
    }

    fn check_safe_to_notar(&mut self, block_hash: BlockHash) -> SafeToNotarStatus {
        // check general voted stake conditions
        let notar_stake = *self.voted_stakes.notar.get(&block_hash).unwrap_or(&0);
        let skip_stake = self.voted_stakes.skip;
        if !self.is_weakest_quorum(notar_stake) {
            return SafeToNotarStatus::AwaitingVotes;
        }
        if !self.is_weak_quorum(notar_stake) && !self.is_quorum(notar_stake + skip_stake) {
            self.pending_safe_to_notar.insert(block_hash);
            return SafeToNotarStatus::AwaitingVotes;
        }

        // check parent condition
        match self.parents.entry(block_hash.clone()) {
            Entry::Vacant(_) => return SafeToNotarStatus::MissingBlock,
            Entry::Occupied(entry) => {
                if entry.get() != &ParentStatus::Certified {
                    return SafeToNotarStatus::AwaitingVotes;
                }
            }
        }

        // check own vote
        let own_id = self.epoch_info.own_id;
        let skip = &self.votes.skip[own_id as usize];
        let notar = &self.votes.notar[own_id as usize];

        match (skip, notar) {
            (Some(_), _) => {
                self.pending_safe_to_notar.remove(&block_hash);
                self.sent_safe_to_notar.insert(block_hash);
                SafeToNotarStatus::SafeToNotar
            }
            (_, Some(n)) => {
                if n.block_hash().unwrap() != &block_hash {
                    self.pending_safe_to_notar.remove(&block_hash);
                    self.sent_safe_to_notar.insert(block_hash);
                    SafeToNotarStatus::SafeToNotar
                } else {
                    SafeToNotarStatus::AwaitingVotes
                }
            }
            (None, None) => {
                self.pending_safe_to_notar.insert(block_hash);
                SafeToNotarStatus::AwaitingVotes
            }
        }
    }

    /// Checks whether the given block hash has a notar-fallback cert in this slot.
    pub fn is_notar_fallback(&self, block_hash: &BlockHash) -> bool {
        self.certificates
            .notar_fallback
            .iter()
            .any(|n| n.block_hash() == block_hash)
    }
}

impl SlotVotes {
    /// Creates a new container for votes for the given number of validators.
    ///
    /// Initially, it contains no votes.
    pub fn new(num_validators: usize) -> Self {
        Self {
            notar: vec![None; num_validators],
            notar_fallback: vec![BTreeMap::new(); num_validators],
            skip: vec![None; num_validators],
            skip_fallback: vec![None; num_validators],
            finalize: vec![None; num_validators],
        }
    }

    /// Returns all notarization votes for the given block hash.
    // PERF: return iterators here (to avoid memory allocation)?
    pub fn notar_votes(&self, block_hash: &BlockHash) -> Vec<Vote> {
        self.notar
            .iter()
            .filter_map(|vote| {
                vote.as_ref()
                    .and_then(|vote| (vote.block_hash().unwrap() == block_hash).then_some(vote))
            })
            .cloned()
            .collect()
    }

    /// Returns all notar-fallback votes for the given block hash.
    // PERF: return iterators here (to avoid memory allocation)?
    pub fn notar_fallback_votes(&self, block_hash: &BlockHash) -> Vec<Vote> {
        self.notar_fallback
            .iter()
            .filter_map(|m| m.get(block_hash).cloned())
            .collect()
    }

    /// Returns all skip votes for this slot.
    // PERF: return iterators here (to avoid memory allocation)?
    pub fn skip_votes(&self) -> Vec<Vote> {
        self.skip.iter().filter_map(Clone::clone).collect()
    }

    /// Returns all skip-fallback votes for this slot.
    // PERF: return iterators here (to avoid memory allocation)?
    pub fn skip_fallback_votes(&self) -> Vec<Vote> {
        self.skip_fallback.iter().filter_map(Clone::clone).collect()
    }

    /// Returns all finalization votes for this slot.
    // PERF: return iterators here (to avoid memory allocation)?
    pub fn final_votes(&self) -> Vec<Vote> {
        self.finalize.iter().filter_map(Clone::clone).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ValidatorId;
    use crate::crypto::Hash;
    use crate::test_utils::generate_validators;

    #[test]
    fn quorums() {
        let (_, epoch_info) = generate_validators(6);
        let slot_state = SlotState::new(Slot::new(0), epoch_info);
        assert!(slot_state.is_weak_quorum(3));
        assert!(!slot_state.is_quorum(3));
        assert!(slot_state.is_quorum(4));
        assert!(!slot_state.is_strong_quorum(4));
        assert!(slot_state.is_strong_quorum(5));

        let (_, epoch_info) = generate_validators(11);
        let slot_state = SlotState::new(Slot::new(0), epoch_info);
        assert!(slot_state.is_weak_quorum(5));
        assert!(!slot_state.is_quorum(5));
        assert!(slot_state.is_quorum(7));
        assert!(!slot_state.is_strong_quorum(7));
        assert!(slot_state.is_strong_quorum(9));
    }

    #[test]
    fn add_cert() {
        let (sks, epoch_info) = generate_validators(11);
        let (slot, hash): BlockId = (Slot::new(1), Hash::random_for_test().into());
        let mut slot_state = SlotState::new(slot, epoch_info.clone());
        let votes: Vec<_> = sks
            .iter()
            .enumerate()
            .map(|(i, sk)| Vote::new_notar(slot, hash.clone(), sk, i as ValidatorId))
            .collect();
        let cert = NotarCert::try_new(&votes, &epoch_info.validators).unwrap();
        assert!(slot_state.certificates.notar.is_none());
        slot_state.add_cert(Cert::Notar(cert));
        assert!(slot_state.certificates.notar.is_some());
    }

    #[test]
    fn add_vote() {
        let (sks, epoch_info) = generate_validators(11);
        let (slot, hash): BlockId = (Slot::new(1), Hash::random_for_test().into());
        let mut slot_state = SlotState::new(slot, epoch_info.clone());
        for (i, sk) in sks.iter().enumerate() {
            let vote = Vote::new_notar(slot, hash.clone(), sk, i as ValidatorId);
            let voter_stake = epoch_info.validator(i as ValidatorId).stake;
            assert!(slot_state.votes.notar[i].is_none());
            slot_state.add_vote(vote.clone(), voter_stake);
            let notar_vote = &slot_state.votes.notar[i];
            assert!(notar_vote.is_some());
            assert_eq!(
                slot_state.voted_stakes.notar.get(&hash),
                Some(&((i + 1) as Stake))
            );
            assert_eq!(slot_state.voted_stakes.notar_or_skip, (i + 1) as Stake);
        }
    }

    #[test]
    fn safe_to_notar() {
        let (sks, epoch_info) = generate_validators(3);
        let (slot, hash): BlockId = (Slot::new(1), Hash::random_for_test().into());
        let mut slot_state = SlotState::new(slot, epoch_info.clone());

        // mark parent as notarized(-fallback)
        slot_state.notify_parent_known(hash.clone());
        slot_state.notify_parent_certified(hash.clone());

        // 33% notar alone has no effect
        let vote = Vote::new_notar(slot, hash.clone(), &sks[1], 1);
        let voter_stake = epoch_info.validator(1).stake;
        let (certs, events, blocks) = slot_state.add_vote(vote.clone(), voter_stake);
        assert!(certs.is_empty());
        assert!(events.is_empty());
        assert!(blocks.is_empty());

        // additional 33% skip should lead to safe-to-notar
        let vote = Vote::new_skip(slot, &sks[0], 0);
        let voter_stake = epoch_info.validator(0).stake;
        let (certs, events, blocks) = slot_state.add_vote(vote.clone(), voter_stake);
        assert!(certs.is_empty());
        assert_eq!(events.len(), 1);
        assert!(blocks.is_empty());
        match &events[0] {
            VotorEvent::SafeToNotar(s, h) => {
                assert_eq!(*s, slot);
                assert_eq!(*h, hash);
            }
            _ => unreachable!(),
        }
    }
}
