// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure handling votes and certificates for a single slot.
//!
//!

use std::collections::BTreeMap;
use std::sync::Arc;

use smallvec::SmallVec;

use crate::consensus::cert::{FastFinalCert, FinalCert, NotarCert, NotarFallbackCert, SkipCert};
use crate::consensus::vote::VoteKind;
use crate::consensus::votor::VotorEvent;
use crate::consensus::{Cert, EpochInfo, Vote};
use crate::crypto::Hash;
use crate::{Slot, Stake};

use super::SlashableOffence;

pub struct SlotState {
    /// Votes for this slot, contains all vote types and validators.
    pub(super) votes: SlotVotes,
    /// Running stake totals for different types of votes.
    pub(super) voted_stakes: SlotVotedStake,
    /// Certificates for this slot, contains all certificate types and validators.
    pub(super) certificates: SlotCertificates,
    /// Indicates if a block hash in this slot is branch certified, that is,
    /// it and all its ancestors are notarized(-fallback).
    pub(super) branch_certified: Option<Hash>,
    /// Information about all validators active in this slot.
    pub(super) epoch_info: Arc<EpochInfo>,
}

// PERF: replace storing Votes (50% size overhead) with storing only signatures?
pub struct SlotVotes {
    /// Notarization votes for all validators (indexed by `ValidatorId`).
    pub(super) notar: Vec<Option<(Hash, Vote)>>,
    /// Notar-fallback votes for all validators (indexed by `ValidatorId`).
    pub(super) notar_fallback: Vec<Vec<(Hash, Vote)>>,
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
    pub(super) notar: BTreeMap<Hash, Stake>,
    /// Amount of stake for each block hash for which we have a notar-fallback vote.
    pub(super) notar_fallback: BTreeMap<Hash, Stake>,
    /// Amount of stake for which we have a skip(-fallback) vote.
    pub(super) skip: Stake,
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
    /// Notar-fallback certificate for this slot, if it exists.
    pub(super) notar_fallback: Option<NotarFallbackCert>,
    /// Skip certificate for this slot, if it exists.
    pub(super) skip: Option<SkipCert>,
    /// Fast finalization certificate for this slot, if it exists.
    pub(super) fast_finalize: Option<FastFinalCert>,
    /// Finalization certificate for this slot, if it exists.
    pub(super) finalize: Option<FinalCert>,
}

impl SlotState {
    pub fn new(epoch_info: Arc<EpochInfo>) -> Self {
        Self {
            votes: SlotVotes::new(epoch_info.validators.len()),
            voted_stakes: SlotVotedStake::default(),
            certificates: SlotCertificates::default(),
            branch_certified: None,
            epoch_info,
        }
    }

    pub fn add_cert(&mut self, cert: Cert) {
        match cert {
            Cert::Notar(n) => self.certificates.notar = Some(n),
            Cert::NotarFallback(n) => self.certificates.notar_fallback = Some(n),
            Cert::Skip(s) => self.certificates.skip = Some(s),
            Cert::FastFinal(s) => self.certificates.fast_finalize = Some(s),
            Cert::Final(f) => self.certificates.finalize = Some(f),
        }
    }

    pub fn add_vote(
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
            let cert = NotarCert::new_unchecked(&votes, &self.epoch_info.validators);
            new_certs.push(Cert::Notar(cert));
        }
        if self.is_strong_quorum(notar_stake) && self.certificates.fast_finalize.is_none() {
            let votes = self.votes.notar_votes(block_hash);
            let cert = FastFinalCert::new_unchecked(&votes, &self.epoch_info.validators);
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
        let nf_stakes = &mut self.voted_stakes.notar_fallback;
        let nf_stake = nf_stakes.entry(*block_hash).or_insert(0);
        *nf_stake += stake;
        let nf_stake = *nf_stake;
        let notar_stake = *self.voted_stakes.notar.get(block_hash).unwrap_or(&0);
        if self.is_quorum(nf_stake + notar_stake) && self.certificates.notar_fallback.is_none() {
            let mut votes = self.votes.notar_votes(block_hash);
            votes.extend(self.votes.notar_fallback_votes(block_hash));
            let cert = NotarFallbackCert::new_unchecked(&votes, &self.epoch_info.validators);
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
            let cert = SkipCert::new_unchecked(&votes, &self.epoch_info.validators);
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
            let cert = FinalCert::new_unchecked(&votes, &self.epoch_info.validators);
            new_certs.push(Cert::Final(cert));
        }
        (new_certs, SmallVec::new())
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
    pub fn should_ignore_vote(&self, vote: &Vote) -> bool {
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
    pub fn new(num_validators: usize) -> Self {
        Self {
            notar: vec![None; num_validators],
            notar_fallback: vec![Vec::new(); num_validators],
            skip: vec![None; num_validators],
            skip_fallback: vec![None; num_validators],
            finalize: vec![None; num_validators],
        }
    }

    // PERF: return iterators here (to avoid memory allocation)?
    pub fn notar_votes(&self, block_hash: &Hash) -> Vec<Vote> {
        self.notar
            .iter()
            .filter(|o| o.is_some() && &o.as_ref().unwrap().0 == block_hash)
            .map(|o| o.as_ref().unwrap().1.clone())
            .collect()
    }

    pub fn notar_fallback_votes(&self, block_hash: &Hash) -> Vec<Vote> {
        self.notar_fallback
            .iter()
            .flatten()
            .filter(|(h, _)| *h == *block_hash)
            .map(|(_, s)| s.clone())
            .collect()
    }

    pub fn skip_votes(&self) -> Vec<Vote> {
        self.skip.iter().filter_map(|o| o.clone()).collect()
    }

    pub fn skip_fallback_votes(&self) -> Vec<Vote> {
        self.skip_fallback
            .iter()
            .filter_map(|o| o.clone())
            .collect()
    }

    pub fn final_votes(&self) -> Vec<Vote> {
        self.finalize.iter().filter_map(|x| x.clone()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ValidatorInfo;
    use crate::crypto::aggsig::SecretKey;
    use crate::crypto::signature;

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
    async fn basic() {
        let (_, _) = generate_validators(11);
    }
}
