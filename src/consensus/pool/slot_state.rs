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

use super::{PoolEvent, SlashableOffence};
use crate::consensus::cert::{FastFinalCert, FinalCert, NotarCert, NotarFallbackCert, SkipCert};
use crate::consensus::{
    Cert, FinalVote, NotarFallbackVote, NotarVote, SkipFallbackVote, SkipVote, ValidatorEpochInfo,
    Vote,
};
use crate::crypto::merkle::BlockHash;
use crate::{BlockId, Slot, Stake};

/// Data structure holding pool state for a single slot.
pub(super) struct SlotState {
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
    pub(super) epoch_info: Arc<ValidatorEpochInfo>,
}

// PERF: replace storing Votes (50% size overhead) with storing only signatures?
pub(super) struct SlotVotes {
    /// Notarization votes for all validators (indexed by `ValidatorIndex`).
    pub(super) notar: Vec<Option<NotarVote>>,
    /// Notar-fallback votes for all validators (indexed by `ValidatorIndex`).
    pub(super) notar_fallback: Vec<BTreeMap<BlockHash, NotarFallbackVote>>,
    /// Skip votes for all validators (indexed by `ValidatorIndex`).
    pub(super) skip: Vec<Option<SkipVote>>,
    /// Skip-fallback votes for all validators (indexed by `ValidatorIndex`).
    pub(super) skip_fallback: Vec<Option<SkipFallbackVote>>,
    /// Finalization votes for all validators (indexed by `ValidatorIndex`).
    pub(super) finalize: Vec<Option<FinalVote>>,
}

#[derive(Default)]
pub(super) struct SlotVotedStake {
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
pub(super) struct SlotCertificates {
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
pub(super) enum SafeToNotarStatus {
    SafeToNotar,
    MissingBlock,
    AwaitingVotes,
}

/// Why an incoming vote is dropped without being counted.
///
/// Returned by [`SlotState::should_ignore_vote`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum IgnoreReason {
    /// A plain duplicate of a vote already counted for this validator.
    Duplicate,
    /// A skip and a skip-fallback from the same validator.
    SkipSkipFallback,
    /// A notar and a notar-fallback for the same block from the same validator.
    NotarNotarFallback,
}

type SlotStateOutputs = (
    SmallVec<[Cert; 2]>,
    SmallVec<[PoolEvent; 2]>,
    SmallVec<[BlockId; 1]>,
);

impl SlotState {
    /// Creates a new container for votes and certificates for a single slot.
    ///
    /// Initially, it is completely empty.
    pub(super) fn new(slot: Slot, epoch_info: Arc<ValidatorEpochInfo>) -> Self {
        Self {
            votes: SlotVotes::new(epoch_info.epoch_info().validators().len()),
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
    pub(super) fn add_cert(&mut self, cert: Cert) {
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
    pub(super) fn add_vote(&mut self, vote: Vote, voter_stake: Stake) -> SlotStateOutputs {
        let slot = vote.slot();
        let voter = vote.signer();
        let v = voter.as_usize();

        let (certs_created, mut votor_events, mut blocks_to_repair) = match vote {
            Vote::Notar(notar_vote) => {
                let outputs = self.count_notar_stake(slot, notar_vote.block_hash(), voter_stake);
                self.votes.notar[v] = Some(notar_vote);
                outputs
            }
            Vote::NotarFallback(nf_vote) => {
                let outputs = self.count_notar_fallback_stake(nf_vote.block_hash(), voter_stake);
                let block_hash = nf_vote.block_hash().clone();
                let res = self.votes.notar_fallback[v].insert(block_hash, nf_vote);
                assert!(res.is_none());
                outputs
            }
            Vote::Skip(skip_vote) => {
                self.votes.skip[v] = Some(skip_vote);
                self.voted_stakes.notar_or_skip += voter_stake;
                self.count_skip_stake(slot, voter_stake, false)
            }
            Vote::SkipFallback(sf_vote) => {
                self.votes.skip_fallback[v] = Some(sf_vote);
                self.count_skip_stake(slot, voter_stake, true)
            }
            Vote::Final(final_vote) => {
                self.votes.finalize[v] = Some(final_vote);
                self.count_finalize_stake(voter_stake)
            }
        };

        // own vote might have made a block safe-to-notar
        if voter == self.epoch_info.own_id() {
            for hash in self.pending_safe_to_notar.clone() {
                if self.sent_safe_to_notar.contains(&hash) {
                    continue;
                }
                match self.check_safe_to_notar(hash.clone()) {
                    SafeToNotarStatus::SafeToNotar => {
                        votor_events.push(PoolEvent::SafeToNotar((slot, hash)));
                    }
                    SafeToNotarStatus::MissingBlock => blocks_to_repair.push((slot, hash)),
                    SafeToNotarStatus::AwaitingVotes => {}
                }
            }
        }

        (certs_created, votor_events, blocks_to_repair)
    }

    /// Mark the parent of the block given by `hash` as known (in Blokstor).
    pub(super) fn notify_parent_known(&mut self, hash: BlockHash) {
        self.parents.entry(hash).or_insert(ParentStatus::Known);
    }

    /// Mark the parent of the block given by `hash` as notarized-fallback.
    ///
    /// # Panics
    ///
    /// If [`SlotState::notify_parent_known`] has not yet been called for this block.
    pub(super) fn notify_parent_certified(
        &mut self,
        hash: BlockHash,
    ) -> Option<Either<PoolEvent, BlockId>> {
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
                Some(Either::Left(PoolEvent::SafeToNotar((self.slot, hash))))
            }
            SafeToNotarStatus::MissingBlock => Some(Either::Right((self.slot, hash))),
            SafeToNotarStatus::AwaitingVotes => None,
        }
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
            .or_default();
        *notar_stake += stake;
        self.voted_stakes.notar_or_skip += stake;
        let notar_stake = *notar_stake;
        self.voted_stakes.top_notar = notar_stake.max(self.voted_stakes.top_notar);

        // check quorums
        if !self.sent_safe_to_notar.contains(block_hash) {
            match self.check_safe_to_notar(block_hash.clone()) {
                SafeToNotarStatus::SafeToNotar => {
                    votor_events.push(PoolEvent::SafeToNotar((slot, block_hash.clone())));
                }
                SafeToNotarStatus::MissingBlock => {
                    blocks_to_repair.push((slot, block_hash.clone()));
                }
                SafeToNotarStatus::AwaitingVotes => {}
            }
        }
        if !self.sent_safe_to_skip
            && self
                .epoch_info
                .epoch_info()
                .is_weak_quorum(self.voted_stakes.notar_or_skip - self.voted_stakes.top_notar)
            && self.votes.notar[self.epoch_info.own_id().as_usize()].is_some()
        {
            votor_events.push(PoolEvent::SafeToSkip(slot));
            self.sent_safe_to_skip = true;
        }
        let nf_stake = self
            .voted_stakes
            .notar_fallback
            .get(block_hash)
            .copied()
            .unwrap_or_default();
        if self
            .epoch_info
            .epoch_info()
            .is_quorum(nf_stake + notar_stake)
            && !self.is_notar_fallback(block_hash)
        {
            let notar_votes = self.votes.notar_votes(block_hash);
            let nf_votes = self.votes.notar_fallback_votes(block_hash);
            let cert = NotarFallbackCert::new(
                &notar_votes,
                &nf_votes,
                self.epoch_info.epoch_info().validators(),
            );
            new_certs.push(Cert::NotarFallback(cert));
        }
        if self.epoch_info.epoch_info().is_quorum(notar_stake) && self.certificates.notar.is_none()
        {
            let votes = self.votes.notar_votes(block_hash);
            let cert = NotarCert::new(&votes, self.epoch_info.epoch_info().validators());
            new_certs.push(Cert::Notar(cert));
        }
        if self.epoch_info.epoch_info().is_strong_quorum(notar_stake)
            && self.certificates.fast_finalize.is_none()
        {
            let votes = self.votes.notar_votes(block_hash);
            let cert = FastFinalCert::new(&votes, self.epoch_info.epoch_info().validators());
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
        let nf_stake = nf_stakes.entry(block_hash.clone()).or_default();
        *nf_stake += stake;
        let nf_stake = *nf_stake;
        let notar_stake = self
            .voted_stakes
            .notar
            .get(block_hash)
            .copied()
            .unwrap_or_default();
        if self
            .epoch_info
            .epoch_info()
            .is_quorum(nf_stake + notar_stake)
            && !self.is_notar_fallback(block_hash)
        {
            let notar_votes = self.votes.notar_votes(block_hash);
            let nf_votes = self.votes.notar_fallback_votes(block_hash);
            let cert = NotarFallbackCert::new(
                &notar_votes,
                &nf_votes,
                self.epoch_info.epoch_info().validators(),
            );
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
                    votor_events.push(PoolEvent::SafeToNotar((slot, hash)));
                }
                SafeToNotarStatus::MissingBlock => blocks_to_repair.push((slot, hash)),
                SafeToNotarStatus::AwaitingVotes => {}
            }
        }
        let total_skip_stake = self.voted_stakes.skip + self.voted_stakes.skip_fallback;
        if self.epoch_info.epoch_info().is_quorum(total_skip_stake)
            && self.certificates.skip.is_none()
        {
            let skip_votes = self.votes.skip_votes();
            let sf_votes = self.votes.skip_fallback_votes();
            let cert = SkipCert::new(
                &skip_votes,
                &sf_votes,
                self.epoch_info.epoch_info().validators(),
            );
            new_certs.push(Cert::Skip(cert));
        }
        if !self.sent_safe_to_skip
            && self
                .epoch_info
                .epoch_info()
                .is_weak_quorum(self.voted_stakes.notar_or_skip - self.voted_stakes.top_notar)
            && self.votes.notar[self.epoch_info.own_id().as_usize()].is_some()
        {
            votor_events.push(PoolEvent::SafeToSkip(slot));
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
        if self
            .epoch_info
            .epoch_info()
            .is_quorum(self.voted_stakes.finalize)
            && self.certificates.finalize.is_none()
        {
            let votes: Vec<_> = self.votes.final_votes();
            let cert = FinalCert::new(&votes, self.epoch_info.epoch_info().validators());
            new_certs.push(Cert::Final(cert));
        }
        (new_certs, SmallVec::new(), SmallVec::new())
    }

    /// Checks whether the given vote constitutes a slashable offence.
    ///
    /// This has to be called before dismissing potential duplicates,
    /// as according to `should_ignore_vote()`.
    // NOTE: Some benign vote combinations, that are provably non-honest,
    // are intentionally not slashable, see also `should_ignore_vote`.
    // They is surfaced via a log instead (see `add_vote` in `pool.rs`).
    pub(super) fn check_slashable_offence(&self, vote: &Vote) -> Option<SlashableOffence> {
        let slot = vote.slot();
        let voter = vote.signer();
        let v = voter.as_usize();
        match vote {
            Vote::Notar(notar_vote) => {
                if self.votes.skip[v].is_some() {
                    return Some(SlashableOffence::SkipAndNotarize(voter, slot));
                }
                if let Some(existing) = &self.votes.notar[v]
                    && notar_vote.block_hash() != existing.block_hash()
                {
                    return Some(SlashableOffence::NotarDifferentHash(voter, slot));
                }
            }
            Vote::NotarFallback(_) => {
                if self.votes.finalize[v].is_some() {
                    return Some(SlashableOffence::NotarFallbackAndFinalize(voter, slot));
                }
            }
            Vote::Skip(_) => {
                if self.votes.finalize[v].is_some() {
                    return Some(SlashableOffence::SkipAndFinalize(voter, slot));
                } else if self.votes.notar[v].is_some() {
                    return Some(SlashableOffence::SkipAndNotarize(voter, slot));
                }
            }
            Vote::SkipFallback(_) => {
                if self.votes.finalize[v].is_some() {
                    return Some(SlashableOffence::SkipAndFinalize(voter, slot));
                }
            }
            Vote::Final(_) => {
                if self.votes.skip[v].is_some() || self.votes.skip_fallback[v].is_some() {
                    return Some(SlashableOffence::SkipAndFinalize(voter, slot));
                } else if !self.votes.notar_fallback[v].is_empty() {
                    return Some(SlashableOffence::NotarFallbackAndFinalize(voter, slot));
                }
            }
        }
        None
    }

    /// Determines whether the given vote should be ignored, and if so, why.
    ///
    /// Returns `None` if the vote is fresh and should be counted.
    /// Any `Some` value means the vote must never be counted
    /// (doing so could double-count stake).
    /// [`IgnoreReason::Duplicate`] means the vote is an exact duplicate.
    /// The other variants additionally flag a cross-type overlap
    /// (skip + skip-fallback, or notar + notar-fallback for the same block).
    /// An honest node never casts either pair, so this is provably non-honest.
    /// However, it is benign misbehavior (not-slashable),
    /// because it never leads to the creation of additional certificates.
    pub(super) fn should_ignore_vote(&self, vote: &Vote) -> Option<IgnoreReason> {
        let v = vote.signer().as_usize();
        match vote {
            Vote::Notar(n_vote) => {
                if self.votes.notar[v].is_some() {
                    Some(IgnoreReason::Duplicate)
                } else if self.votes.notar_fallback[v].contains_key(n_vote.block_hash()) {
                    Some(IgnoreReason::NotarNotarFallback)
                } else {
                    None
                }
            }
            Vote::NotarFallback(nf_vote) => {
                if self.votes.notar_fallback[v].contains_key(nf_vote.block_hash()) {
                    Some(IgnoreReason::Duplicate)
                } else if self.votes.notar[v]
                    .as_ref()
                    .is_some_and(|existing| existing.block_hash() == nf_vote.block_hash())
                {
                    Some(IgnoreReason::NotarNotarFallback)
                } else {
                    None
                }
            }
            Vote::Skip(_) => {
                if self.votes.skip[v].is_some() {
                    Some(IgnoreReason::Duplicate)
                } else if self.votes.skip_fallback[v].is_some() {
                    Some(IgnoreReason::SkipSkipFallback)
                } else {
                    None
                }
            }
            Vote::SkipFallback(_) => {
                if self.votes.skip_fallback[v].is_some() {
                    Some(IgnoreReason::Duplicate)
                } else if self.votes.skip[v].is_some() {
                    Some(IgnoreReason::SkipSkipFallback)
                } else {
                    None
                }
            }
            Vote::Final(_) => self.votes.finalize[v]
                .is_some()
                .then_some(IgnoreReason::Duplicate),
        }
    }

    fn check_safe_to_notar(&mut self, block_hash: BlockHash) -> SafeToNotarStatus {
        // check general voted stake conditions
        let notar_stake = self
            .voted_stakes
            .notar
            .get(&block_hash)
            .copied()
            .unwrap_or_default();
        let skip_stake = self.voted_stakes.skip;
        if !self.epoch_info.epoch_info().is_weakest_quorum(notar_stake) {
            return SafeToNotarStatus::AwaitingVotes;
        }
        if !self.epoch_info.epoch_info().is_weak_quorum(notar_stake)
            && !self
                .epoch_info
                .epoch_info()
                .is_quorum(notar_stake + skip_stake)
        {
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
        let own_id = self.epoch_info.own_id();
        let skip = &self.votes.skip[own_id.as_usize()];
        let notar = &self.votes.notar[own_id.as_usize()];

        match (skip, notar) {
            (Some(_), _) => {
                self.pending_safe_to_notar.remove(&block_hash);
                self.sent_safe_to_notar.insert(block_hash);
                SafeToNotarStatus::SafeToNotar
            }
            (_, Some(n)) => {
                if n.block_hash() != &block_hash {
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
    pub(super) fn is_notar_fallback(&self, block_hash: &BlockHash) -> bool {
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
    pub(super) fn new(num_validators: usize) -> Self {
        Self {
            notar: vec![None; num_validators],
            notar_fallback: vec![BTreeMap::new(); num_validators],
            skip: vec![None; num_validators],
            skip_fallback: vec![None; num_validators],
            finalize: vec![None; num_validators],
        }
    }

    // NOTE: `Vec` not `impl Iterator` — cert constructors need a multi-pass slice.
    /// Returns all notarization votes for the given block hash.
    pub(super) fn notar_votes(&self, block_hash: &BlockHash) -> Vec<NotarVote> {
        self.notar
            .iter()
            .filter_map(|vote| {
                vote.as_ref()
                    .and_then(|vote| (vote.block_hash() == block_hash).then_some(vote))
            })
            .cloned()
            .collect()
    }

    /// Returns all notar-fallback votes for the given block hash.
    pub(super) fn notar_fallback_votes(&self, block_hash: &BlockHash) -> Vec<NotarFallbackVote> {
        self.notar_fallback
            .iter()
            .filter_map(|m| m.get(block_hash).cloned())
            .collect()
    }

    /// Returns all skip votes for this slot.
    pub(super) fn skip_votes(&self) -> Vec<SkipVote> {
        self.skip.iter().filter_map(Clone::clone).collect()
    }

    /// Returns all skip-fallback votes for this slot.
    pub(super) fn skip_fallback_votes(&self) -> Vec<SkipFallbackVote> {
        self.skip_fallback.iter().filter_map(Clone::clone).collect()
    }

    /// Returns all finalization votes for this slot.
    pub(super) fn final_votes(&self) -> Vec<FinalVote> {
        self.finalize.iter().filter_map(Clone::clone).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ValidatorIndex;
    use crate::consensus::EpochInfo;
    use crate::test_utils::{generate_validators, random_block_id};

    /// Wraps shared `EpochInfo` with a `ValidatorEpochInfo` for validator 0.
    fn wrap_epoch_info(epoch_info: EpochInfo) -> Arc<ValidatorEpochInfo> {
        Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(0), epoch_info))
    }

    /// Adds `vote` to `state`, looking up the voter's stake from the epoch info.
    fn add(state: &mut SlotState, vote: Vote) -> SlotStateOutputs {
        let stake = state.epoch_info.epoch_info().validator(vote.signer()).stake;
        state.add_vote(vote, stake)
    }

    #[test]
    fn add_cert() {
        let (sks, epoch_info) = generate_validators(11);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info.clone());
        let votes: Vec<NotarVote> = sks
            .iter()
            .enumerate()
            .map(|(i, sk)| NotarVote::new(slot, hash.clone(), sk, ValidatorIndex::new(i as u64)))
            .collect();
        let cert = NotarCert::try_new(&votes, epoch_info.epoch_info().validators()).unwrap();
        assert!(state.certificates.notar.is_none());
        state.add_cert(Cert::Notar(cert));
        assert!(state.certificates.notar.is_some());
    }

    #[test]
    fn add_vote() {
        let (sks, epoch_info) = generate_validators(11);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info);
        for (i, sk) in sks.iter().enumerate() {
            let notar_vote = Vote::new_notar(slot, hash.clone(), sk, ValidatorIndex::new(i as u64));
            assert!(state.votes.notar[i].is_none());
            add(&mut state, notar_vote);
            assert!(state.votes.notar[i].is_some());
            assert_eq!(
                state.voted_stakes.notar.get(&hash),
                Some(&Stake::new(i as u64 + 1))
            );
        }
    }

    #[test]
    fn safe_to_notar() {
        let (sks, epoch_info) = generate_validators(3);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info);

        // mark parent as notarized(-fallback)
        state.notify_parent_known(hash.clone());
        state.notify_parent_certified(hash.clone());

        // 33% notar alone has no effect
        let notar_vote = Vote::new_notar(slot, hash.clone(), &sks[1], ValidatorIndex::new(1));
        let (certs, events, blocks) = add(&mut state, notar_vote);
        assert!(certs.is_empty());
        assert!(events.is_empty());
        assert!(blocks.is_empty());

        // additional 33% skip should lead to safe-to-notar
        let skip_vote = Vote::new_skip(slot, &sks[0], ValidatorIndex::new(0));
        let (certs, events, blocks) = add(&mut state, skip_vote);
        assert!(certs.is_empty());
        assert_eq!(events.len(), 1);
        assert!(blocks.is_empty());
        assert_eq!(events[0], PoolEvent::SafeToNotar((slot, hash)));
    }

    #[test]
    fn slashable_skip_and_notarize() {
        let (sks, epoch_info) = generate_validators(6);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info);

        // validator 1 skips first, so a later notarization is slashable
        let v1 = ValidatorIndex::new(1);
        add(&mut state, Vote::new_skip(slot, &sks[1], v1));
        let notar_vote = Vote::new_notar(slot, hash.clone(), &sks[1], v1);
        assert_eq!(
            state.check_slashable_offence(&notar_vote),
            Some(SlashableOffence::SkipAndNotarize(v1, slot))
        );

        // validator 2 notarizes first, so a later skip is slashable
        let v2 = ValidatorIndex::new(2);
        add(&mut state, Vote::new_notar(slot, hash, &sks[2], v2));
        let skip_vote = Vote::new_skip(slot, &sks[2], v2);
        assert_eq!(
            state.check_slashable_offence(&skip_vote),
            Some(SlashableOffence::SkipAndNotarize(v2, slot))
        );
    }

    #[test]
    fn slashable_notar_different_hash() {
        let (sks, epoch_info) = generate_validators(6);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash_a) = random_block_id(Slot::new(1));
        let hash_b = random_block_id(Slot::new(1)).1;
        let mut state = SlotState::new(slot, epoch_info);
        let v = ValidatorIndex::new(1);

        let notar_a = Vote::new_notar(slot, hash_a, &sks[1], v);
        add(&mut state, notar_a.clone());

        // notarizing a different hash for the same slot is slashable
        let notar_b = Vote::new_notar(slot, hash_b, &sks[1], v);
        assert_eq!(
            state.check_slashable_offence(&notar_b),
            Some(SlashableOffence::NotarDifferentHash(v, slot))
        );

        // re-notarizing the same hash is a benign duplicate, not slashable
        assert!(state.check_slashable_offence(&notar_a).is_none());
    }

    #[test]
    fn slashable_skip_and_finalize() {
        let (sks, epoch_info) = generate_validators(6);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, _) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info);

        // finalize first, then skip / skip-fallback are slashable
        let v1 = ValidatorIndex::new(1);
        add(&mut state, Vote::new_final(slot, &sks[1], v1));
        assert_eq!(
            state.check_slashable_offence(&Vote::new_skip(slot, &sks[1], v1)),
            Some(SlashableOffence::SkipAndFinalize(v1, slot))
        );
        assert_eq!(
            state.check_slashable_offence(&Vote::new_skip_fallback(slot, &sks[1], v1)),
            Some(SlashableOffence::SkipAndFinalize(v1, slot))
        );

        // skip first, then finalize is slashable
        let v2 = ValidatorIndex::new(2);
        add(&mut state, Vote::new_skip(slot, &sks[2], v2));
        assert_eq!(
            state.check_slashable_offence(&Vote::new_final(slot, &sks[2], v2)),
            Some(SlashableOffence::SkipAndFinalize(v2, slot))
        );

        // skip-fallback first, then finalize is slashable
        let v3 = ValidatorIndex::new(3);
        add(&mut state, Vote::new_skip_fallback(slot, &sks[3], v3));
        assert_eq!(
            state.check_slashable_offence(&Vote::new_final(slot, &sks[3], v3)),
            Some(SlashableOffence::SkipAndFinalize(v3, slot))
        );
    }

    #[test]
    fn slashable_notar_fallback_and_finalize() {
        let (sks, epoch_info) = generate_validators(6);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info);

        // finalize first, then a notar-fallback is slashable
        let v1 = ValidatorIndex::new(1);
        add(&mut state, Vote::new_final(slot, &sks[1], v1));
        let nf_vote_1 = Vote::new_notar_fallback(slot, hash.clone(), &sks[1], v1);
        assert_eq!(
            state.check_slashable_offence(&nf_vote_1),
            Some(SlashableOffence::NotarFallbackAndFinalize(v1, slot))
        );

        // notar-fallback first, then finalize is slashable
        let v2 = ValidatorIndex::new(2);
        let nf_vote_2 = Vote::new_notar_fallback(slot, hash, &sks[2], v2);
        add(&mut state, nf_vote_2);
        assert_eq!(
            state.check_slashable_offence(&Vote::new_final(slot, &sks[2], v2)),
            Some(SlashableOffence::NotarFallbackAndFinalize(v2, slot))
        );
    }

    #[test]
    fn slashable_offence_none() {
        let (sks, epoch_info) = generate_validators(6);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info);
        let sk = &sks[1];
        let v = ValidatorIndex::new(1);

        // no prior votes -> nothing is slashable
        let notar_vote = Vote::new_notar(slot, hash, sk, v);
        let skip_vote = Vote::new_skip(slot, sk, v);
        let final_vote = Vote::new_final(slot, sk, v);
        assert!(state.check_slashable_offence(&notar_vote).is_none());
        assert!(state.check_slashable_offence(&skip_vote).is_none());
        assert!(state.check_slashable_offence(&final_vote).is_none());

        // notarizing then finalizing the same block is the happy path, not slashable
        add(&mut state, notar_vote);
        assert!(state.check_slashable_offence(&final_vote).is_none());
    }

    #[test]
    fn should_ignore_duplicate_votes() {
        let (sks, epoch_info) = generate_validators(6);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let other_hash = random_block_id(Slot::new(1)).1;
        let mut state = SlotState::new(slot, epoch_info);

        // fresh validator: nothing to ignore
        let v1 = ValidatorIndex::new(1);
        assert!(
            state
                .should_ignore_vote(&Vote::new_notar(slot, hash.clone(), &sks[1], v1))
                .is_none()
        );

        // only one notar vote per validator counts, regardless of the hash
        add(&mut state, Vote::new_notar(slot, hash.clone(), &sks[1], v1));
        assert_eq!(
            state.should_ignore_vote(&Vote::new_notar(slot, hash.clone(), &sks[1], v1)),
            Some(IgnoreReason::Duplicate)
        );
        assert_eq!(
            state.should_ignore_vote(&Vote::new_notar(slot, other_hash.clone(), &sks[1], v1)),
            Some(IgnoreReason::Duplicate)
        );

        // should ignore skip and skip-fallback after skip
        let v2 = ValidatorIndex::new(2);
        add(&mut state, Vote::new_skip(slot, &sks[2], v2));
        assert_eq!(
            state.should_ignore_vote(&Vote::new_skip(slot, &sks[2], v2)),
            Some(IgnoreReason::Duplicate)
        );
        assert_eq!(
            state.should_ignore_vote(&Vote::new_skip_fallback(slot, &sks[2], v2)),
            Some(IgnoreReason::SkipSkipFallback)
        );

        // ignore duplicate finalization votes
        let v3 = ValidatorIndex::new(3);
        add(&mut state, Vote::new_final(slot, &sks[3], v3));
        assert_eq!(
            state.should_ignore_vote(&Vote::new_final(slot, &sks[3], v3)),
            Some(IgnoreReason::Duplicate)
        );

        // notar-fallback is tracked per (validator, hash)
        let v4 = ValidatorIndex::new(4);
        let nf_vote_1 = Vote::new_notar_fallback(slot, hash, &sks[4], v4);
        add(&mut state, nf_vote_1.clone());
        assert_eq!(
            state.should_ignore_vote(&nf_vote_1),
            Some(IgnoreReason::Duplicate)
        );
        let nf_vote_2 = Vote::new_notar_fallback(slot, other_hash, &sks[4], v4);
        assert!(state.should_ignore_vote(&nf_vote_2).is_none());
    }

    #[test]
    fn count_finalize_creates_cert_at_quorum() {
        let (sks, epoch_info) = generate_validators(6);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, _) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info);

        // 3/6 final votes, below 60% quorum, no cert yet
        for (i, sk) in sks.iter().enumerate().skip(1).take(3) {
            let final_vote = Vote::new_final(slot, sk, ValidatorIndex::new(i as u64));
            let (certs, events, blocks) = add(&mut state, final_vote);
            assert!(certs.is_empty());
            assert!(events.is_empty());
            assert!(blocks.is_empty());
        }
        assert_eq!(state.voted_stakes.finalize, Stake::new(3));

        // 4/6 final votes, quorum reached, produce final cert
        let final_vote = Vote::new_final(slot, &sks[4], ValidatorIndex::new(4));
        let (certs, _, _) = add(&mut state, final_vote);
        assert_eq!(certs.len(), 1);
        let cert = certs.into_iter().next().unwrap();
        assert!(matches!(cert, Cert::Final(_)));

        // more final votes do not emit new cert
        state.add_cert(cert);
        let final_vote = Vote::new_final(slot, &sks[5], ValidatorIndex::new(5));
        let (certs, _, _) = add(&mut state, final_vote);
        assert!(certs.is_empty());
    }

    #[test]
    fn count_notar_fallback_creates_cert_at_quorum() {
        let (sks, epoch_info) = generate_validators(6);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let mut state = SlotState::new(slot, epoch_info);

        // two notar votes for the block, not enough for any cert
        for (i, sk) in sks.iter().enumerate().skip(1).take(2) {
            let v = ValidatorIndex::new(i as u64);
            let notar_vote = Vote::new_notar(slot, hash.clone(), sk, v);
            let (certs, _, _) = add(&mut state, notar_vote);
            assert!(certs.is_empty());
        }

        // one notar-fallback vote: notar(2) + nf(1) = 3 < quorum(4), still no cert
        let nf_vote = Vote::new_notar_fallback(slot, hash.clone(), &sks[3], ValidatorIndex::new(3));
        let (certs, events, blocks) = add(&mut state, nf_vote);
        assert!(certs.is_empty());
        assert!(events.is_empty());
        assert!(blocks.is_empty());
        assert_eq!(
            state.voted_stakes.notar_fallback.get(&hash),
            Some(&Stake::new(1))
        );

        // second notar-fallback vote: notar(2) + nf(2) = 4 = quorum -> notar-fallback cert
        let nf_vote = Vote::new_notar_fallback(slot, hash.clone(), &sks[4], ValidatorIndex::new(4));
        let (certs, _, _) = add(&mut state, nf_vote);
        assert_eq!(certs.len(), 1);
        let cert = certs.into_iter().next().unwrap();
        assert!(matches!(cert, Cert::NotarFallback(_)));
        assert_eq!(cert.block_hash().unwrap(), &hash);

        // more notar-fallback votes do not emit new cert
        state.add_cert(cert);
        let nf_vote = Vote::new_notar_fallback(slot, hash, &sks[5], ValidatorIndex::new(5));
        let (certs, _, _) = add(&mut state, nf_vote);
        assert!(certs.is_empty());
    }

    #[test]
    fn skip_skip_fallback_conflict() {
        let (sks, epoch_info) = generate_validators(3);
        let epoch_info = wrap_epoch_info(epoch_info);
        let slot = Slot::new(1);
        let mut slot_state = SlotState::new(slot, epoch_info.clone());

        let skip = Vote::new_skip(slot, &sks[0], ValidatorIndex::new(0));
        let skip_fallback = Vote::new_skip_fallback(slot, &sks[0], ValidatorIndex::new(0));
        let voter_stake = epoch_info
            .epoch_info()
            .validator(ValidatorIndex::new(0))
            .stake;

        // neither should be ignored before anything is recorded
        assert!(slot_state.should_ignore_vote(&skip).is_none());
        assert!(slot_state.should_ignore_vote(&skip_fallback).is_none());

        // record a skip vote; the cross-type skip-fallback is now a conflict ...
        slot_state.add_vote(skip.clone(), voter_stake);
        assert_eq!(
            slot_state.should_ignore_vote(&skip_fallback),
            Some(IgnoreReason::SkipSkipFallback)
        );
        // ... a same-type skip duplicate is just a plain duplicate, ...
        assert_eq!(
            slot_state.should_ignore_vote(&skip),
            Some(IgnoreReason::Duplicate)
        );
        // ... and the conflict remains benign (not slashable), just dropped.
        assert!(slot_state.check_slashable_offence(&skip_fallback).is_none());
    }

    #[test]
    fn notar_notar_fallback_conflict() {
        let (sks, epoch_info) = generate_validators(3);
        let epoch_info = wrap_epoch_info(epoch_info);
        let (slot, hash) = random_block_id(Slot::new(1));
        let other_hash = random_block_id(Slot::new(1)).1;
        let mut slot_state = SlotState::new(slot, epoch_info.clone());

        let v0 = ValidatorIndex::new(0);
        let notar = Vote::new_notar(slot, hash.clone(), &sks[0], v0);
        let notar_fallback = Vote::new_notar_fallback(slot, hash, &sks[0], v0);
        let nf_other = Vote::new_notar_fallback(slot, other_hash, &sks[0], v0);
        let voter_stake = epoch_info.epoch_info().validator(v0).stake;

        // nothing recorded yet: neither vote is ignored
        assert!(slot_state.should_ignore_vote(&notar).is_none());
        assert!(slot_state.should_ignore_vote(&notar_fallback).is_none());

        // record a notar vote; a notar-fallback for the *same* block is now a
        // cross-type conflict ...
        slot_state.add_vote(notar.clone(), voter_stake);
        assert_eq!(
            slot_state.should_ignore_vote(&notar_fallback),
            Some(IgnoreReason::NotarNotarFallback)
        );
        // ... a second notar is just a plain duplicate, ...
        assert_eq!(
            slot_state.should_ignore_vote(&notar),
            Some(IgnoreReason::Duplicate)
        );
        // ... a notar-fallback for a *different* block is honest and still counts, ...
        assert!(slot_state.should_ignore_vote(&nf_other).is_none());
        // ... and the same-block conflict is benign (not slashable), just dropped.
        assert!(
            slot_state
                .check_slashable_offence(&notar_fallback)
                .is_none()
        );

        // the conflict is symmetric: notar-fallback recorded first, then notar.
        let mut slot_state = SlotState::new(slot, epoch_info);
        slot_state.add_vote(notar_fallback, voter_stake);
        assert_eq!(
            slot_state.should_ignore_vote(&notar),
            Some(IgnoreReason::NotarNotarFallback)
        );
    }
}
