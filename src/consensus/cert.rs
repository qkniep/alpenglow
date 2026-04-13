// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Certificate types used for the consensus protocol.
//!
//!

use thiserror::Error;
use wincode::{SchemaRead, SchemaWrite};

use super::vote::{
    FinalVote, NotarFallbackVote, NotarVote, SignedVote, SkipFallbackVote, SkipVote, VoteKind,
};
use crate::consensus::EpochInfo;
use crate::crypto::merkle::BlockHash;
use crate::crypto::{AggregateSignature, Signable};
use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

/// Errors that can occur during certificate aggregation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum CertError {
    #[error("votes for different slots found during aggregation")]
    SlotMismatch,
    #[error("votes for different block hashes found during aggregation")]
    BlockHashMismatch,
}

/// Certificate types used for the consensus protocol.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub enum Cert {
    Notar(NotarCert),
    NotarFallback(NotarFallbackCert),
    Skip(SkipCert),
    FastFinal(FastFinalCert),
    Final(FinalCert),
}

impl Cert {
    /// Checks that the stake threshold is met.
    #[must_use]
    pub fn check_threshold(&self, epoch_info: &EpochInfo) -> bool {
        match self {
            Self::Notar(n) => n.check_threshold(epoch_info),
            Self::NotarFallback(n) => n.check_threshold(epoch_info),
            Self::Skip(s) => s.check_threshold(epoch_info),
            Self::FastFinal(f) => f.check_threshold(epoch_info),
            Self::Final(f) => f.check_threshold(epoch_info),
        }
    }

    /// Checks that the aggregated signatures are valid.
    #[must_use]
    pub fn check_sig(&self, validators: &[ValidatorInfo]) -> bool {
        match self {
            Self::Notar(n) => n.check_sig(validators),
            Self::NotarFallback(n) => n.check_sig(validators),
            Self::Skip(s) => s.check_sig(validators),
            Self::FastFinal(f) => f.check_sig(validators),
            Self::Final(f) => f.check_sig(validators),
        }
    }

    /// Gives the slot number this certificate is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        match self {
            Self::Notar(n) => n.slot,
            Self::NotarFallback(n) => n.slot,
            Self::Skip(s) => s.slot,
            Self::FastFinal(s) => s.slot,
            Self::Final(f) => f.slot,
        }
    }

    /// Returns the block hash this certificate corresponds to, if any.
    ///
    /// Returns `None` if this is a skip or finalization certificates.
    #[must_use]
    pub const fn block_hash(&self) -> Option<&BlockHash> {
        match self {
            Self::Notar(n) => Some(&n.block_hash),
            Self::NotarFallback(n) => Some(&n.block_hash),
            Self::FastFinal(f) => Some(&f.block_hash),
            Self::Skip(_) | Self::Final(_) => None,
        }
    }

    /// Checks if the given validator is a signer of this certificate.
    #[must_use]
    pub fn is_signer(&self, v: ValidatorId) -> bool {
        match self {
            Self::Notar(n) => n.agg_sig.is_signer(v),
            Self::NotarFallback(n) => {
                let is_sig1_signer = n.agg_sig_notar.as_ref().is_some_and(|s| s.is_signer(v));
                let is_sig2_signer = n
                    .agg_sig_notar_fallback
                    .as_ref()
                    .is_some_and(|s| s.is_signer(v));
                is_sig1_signer || is_sig2_signer
            }
            Self::Skip(s) => {
                let is_sig1_signer = s.agg_sig_skip.as_ref().is_some_and(|s| s.is_signer(v));
                let is_sig2_signer = s
                    .agg_sig_skip_fallback
                    .as_ref()
                    .is_some_and(|s| s.is_signer(v));
                is_sig1_signer || is_sig2_signer
            }
            Self::FastFinal(f) => f.agg_sig.is_signer(v),
            Self::Final(f) => f.agg_sig.is_signer(v),
        }
    }

    /// Iterates over the signers of this certificate, yielding their IDs.
    #[must_use]
    pub fn signers(&self) -> Box<dyn Iterator<Item = ValidatorId> + '_> {
        match self {
            Self::Notar(n) => Box::new(n.agg_sig.signers()),
            Self::NotarFallback(n) => Box::new(
                n.agg_sig_notar
                    .as_ref()
                    .map(AggregateSignature::signers)
                    .into_iter()
                    .flatten()
                    .chain(
                        n.agg_sig_notar_fallback
                            .as_ref()
                            .map(AggregateSignature::signers)
                            .into_iter()
                            .flatten(),
                    ),
            ),
            Self::Skip(s) => Box::new(
                s.agg_sig_skip
                    .as_ref()
                    .map(AggregateSignature::signers)
                    .into_iter()
                    .flatten()
                    .chain(
                        s.agg_sig_skip_fallback
                            .as_ref()
                            .map(AggregateSignature::signers)
                            .into_iter()
                            .flatten(),
                    ),
            ),
            Self::FastFinal(f) => Box::new(f.agg_sig.signers()),
            Self::Final(f) => Box::new(f.agg_sig.signers()),
        }
    }

    /// Gives the combined stake of the validators who signed this certificate.
    #[must_use]
    pub const fn stake(&self) -> Stake {
        match self {
            Self::Notar(n) => n.stake,
            Self::NotarFallback(n) => n.stake,
            Self::Skip(s) => s.stake,
            Self::FastFinal(s) => s.stake,
            Self::Final(f) => f.stake,
        }
    }
}

/// A notarization certificate is an aggregate of a quorum of notar votes.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct NotarCert {
    slot: Slot,
    block_hash: BlockHash,
    agg_sig: AggregateSignature,
    stake: Stake,
}

impl NotarCert {
    /// Tries to create a new notarization certificate.
    ///
    /// # Errors
    ///
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    /// - [`CertError::BlockHashMismatch`] if the votes have different block hashes.
    ///
    /// # Panics
    ///
    /// - Panics if `votes` is empty.
    /// - Panics if a signer of a vote is missing from `validators`.
    pub fn try_new(votes: &[NotarVote], validators: &[ValidatorInfo]) -> Result<Self, CertError> {
        let slot = votes[0].slot();
        let block_hash = votes[0].block_hash().clone();

        for vote in votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if vote.block_hash() != &block_hash {
                return Err(CertError::BlockHashMismatch);
            }
        }

        let agg_sig = aggsig_from_votes(votes, validators);
        let stake: Stake = votes
            .iter()
            .map(|v| validators[v.signer().as_index()].stake)
            .sum();

        Ok(Self {
            slot,
            block_hash,
            agg_sig,
            stake,
        })
    }

    /// Creates a new notarization certificate.
    ///
    /// # Panics
    ///
    /// Panics if `try_new` returns an error.
    pub fn new_unchecked(votes: &[NotarVote], validators: &[ValidatorInfo]) -> Self {
        Self::try_new(votes, validators).unwrap()
    }

    /// Checks that the stake threshold is met.
    ///
    /// The threshold for [`NotarCert`] is >= 60% of the total stake.
    #[must_use]
    pub fn check_threshold(&self, epoch_info: &EpochInfo) -> bool {
        let stake: Stake = epoch_info
            .validators()
            .iter()
            .filter(|v| self.agg_sig.is_signer(v.id))
            .map(|v| v.stake)
            .sum();

        epoch_info.is_quorum(stake)
    }

    /// Checks that the aggregated signature is valid.
    #[must_use]
    pub fn check_sig(&self, validators: &[ValidatorInfo]) -> bool {
        let pks: Vec<_> = validators.iter().map(|v| v.voting_pubkey).collect();
        let vote_bytes = VoteKind::Notar(self.slot, self.block_hash.clone()).bytes_to_sign();
        self.agg_sig.verify(&vote_bytes, &pks)
    }

    /// Returns the block hash of the notarized block.
    pub const fn block_hash(&self) -> &BlockHash {
        &self.block_hash
    }
}

/// A notar-fallback certificate is an aggregate of a quorum of notar(-fallback) votes.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct NotarFallbackCert {
    slot: Slot,
    block_hash: BlockHash,
    agg_sig_notar: Option<AggregateSignature>,
    agg_sig_notar_fallback: Option<AggregateSignature>,
    stake: Stake,
}

impl NotarFallbackCert {
    /// Tries to create a new notar-fallback certificate.
    ///
    /// Accepts a mix of notarization and notar-fallback votes, passed as separate slices.
    /// At least one vote must be provided across both slices.
    ///
    /// # Errors
    ///
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    /// - [`CertError::BlockHashMismatch`] if the votes have different block hashes.
    ///
    /// # Panics
    ///
    /// - Panics if both `notar_votes` and `nf_votes` are empty.
    /// - Panics if a signer of a vote is missing from `validators`.
    pub fn try_new(
        notar_votes: &[NotarVote],
        nf_votes: &[NotarFallbackVote],
        validators: &[ValidatorInfo],
    ) -> Result<Self, CertError> {
        let (slot, block_hash) = if let Some(v) = notar_votes.first() {
            (v.slot(), v.block_hash().clone())
        } else {
            let v = nf_votes.first().expect("at least one vote required");
            (v.slot(), v.block_hash().clone())
        };

        for vote in notar_votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if vote.block_hash() != &block_hash {
                return Err(CertError::BlockHashMismatch);
            }
        }
        for vote in nf_votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if vote.block_hash() != &block_hash {
                return Err(CertError::BlockHashMismatch);
            }
        }

        let stake: Stake = notar_votes
            .iter()
            .map(|v| validators[v.signer().as_index()].stake)
            .chain(
                nf_votes
                    .iter()
                    .map(|v| validators[v.signer().as_index()].stake),
            )
            .sum();

        let agg_sig_notar = if notar_votes.is_empty() {
            None
        } else {
            Some(aggsig_from_votes(notar_votes, validators))
        };

        let agg_sig_notar_fallback = if nf_votes.is_empty() {
            None
        } else {
            Some(aggsig_from_votes(nf_votes, validators))
        };

        Ok(Self {
            slot,
            block_hash,
            agg_sig_notar,
            agg_sig_notar_fallback,
            stake,
        })
    }

    /// Creates a new notar-fallback certificate.
    ///
    /// # Panics
    ///
    /// Panics if `try_new` returns an error.
    pub fn new_unchecked(
        notar_votes: &[NotarVote],
        nf_votes: &[NotarFallbackVote],
        validators: &[ValidatorInfo],
    ) -> Self {
        Self::try_new(notar_votes, nf_votes, validators).unwrap()
    }

    /// Checks that the stake threshold is met.
    ///
    /// The threshold for [`NotarFallbackCert`] is >= 60% of the total stake.
    /// Each validator is counted only once, even if notar and notar-fallback are included for them.
    #[must_use]
    pub fn check_threshold(&self, epoch_info: &EpochInfo) -> bool {
        let stake: Stake = epoch_info
            .validators()
            .iter()
            .filter(|v| {
                self.agg_sig_notar
                    .as_ref()
                    .is_some_and(|s| s.is_signer(v.id))
                    || self
                        .agg_sig_notar_fallback
                        .as_ref()
                        .is_some_and(|s| s.is_signer(v.id))
            })
            .map(|v| v.stake)
            .sum();

        epoch_info.is_quorum(stake)
    }

    /// Checks that the aggregated signatures are valid.
    #[must_use]
    pub fn check_sig(&self, validators: &[ValidatorInfo]) -> bool {
        let pks: Vec<_> = validators.iter().map(|v| v.voting_pubkey).collect();

        let vote_bytes = VoteKind::Notar(self.slot, self.block_hash.clone()).bytes_to_sign();
        let sig1_valid = self
            .agg_sig_notar
            .as_ref()
            .is_none_or(|s| s.verify(&vote_bytes, &pks));

        let vote_bytes =
            VoteKind::NotarFallback(self.slot, self.block_hash.clone()).bytes_to_sign();
        let sig2_valid = self
            .agg_sig_notar_fallback
            .as_ref()
            .is_none_or(|s| s.verify(&vote_bytes, &pks));

        sig1_valid && sig2_valid
    }

    /// Returns the block hash of the notarized-fallback block.
    pub const fn block_hash(&self) -> &BlockHash {
        &self.block_hash
    }
}

/// A skip certificate is an aggregate of a quorum of skip(-fallback) votes.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct SkipCert {
    slot: Slot,
    agg_sig_skip: Option<AggregateSignature>,
    agg_sig_skip_fallback: Option<AggregateSignature>,
    stake: Stake,
}

impl SkipCert {
    /// Tries to create a new skip certificate.
    ///
    /// Accepts a mix of skip and skip-fallback votes, passed as separate slices.
    /// At least one vote must be provided across both slices.
    ///
    /// # Errors
    ///
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    ///
    /// # Panics
    ///
    /// - Panics if both `skip_votes` and `sf_votes` are empty.
    /// - Panics if a signer of a vote is missing from `validators`.
    pub fn try_new(
        skip_votes: &[SkipVote],
        sf_votes: &[SkipFallbackVote],
        validators: &[ValidatorInfo],
    ) -> Result<Self, CertError> {
        let slot = if let Some(v) = skip_votes.first() {
            v.slot()
        } else {
            sf_votes.first().expect("at least one vote required").slot()
        };

        for vote in skip_votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            }
        }
        for vote in sf_votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            }
        }

        let stake: Stake = skip_votes
            .iter()
            .map(|v| validators[v.signer().as_index()].stake)
            .chain(
                sf_votes
                    .iter()
                    .map(|v| validators[v.signer().as_index()].stake),
            )
            .sum();

        let agg_sig_skip = if skip_votes.is_empty() {
            None
        } else {
            Some(aggsig_from_votes(skip_votes, validators))
        };

        let agg_sig_skip_fallback = if sf_votes.is_empty() {
            None
        } else {
            Some(aggsig_from_votes(sf_votes, validators))
        };

        Ok(Self {
            slot,
            agg_sig_skip,
            agg_sig_skip_fallback,
            stake,
        })
    }

    /// Creates a new skip certificate.
    ///
    /// # Panics
    ///
    /// Panics if `try_new` returns an error.
    pub fn new_unchecked(
        skip_votes: &[SkipVote],
        sf_votes: &[SkipFallbackVote],
        validators: &[ValidatorInfo],
    ) -> Self {
        Self::try_new(skip_votes, sf_votes, validators).unwrap()
    }

    /// Checks that the stake threshold is met.
    ///
    /// The threshold for [`SkipCert`] is >= 60% of the total stake.
    /// Each validator is counted only once, even if skip and skip-fallback are included for them.
    #[must_use]
    pub fn check_threshold(&self, epoch_info: &EpochInfo) -> bool {
        let stake: Stake = epoch_info
            .validators()
            .iter()
            .filter(|v| {
                self.agg_sig_skip
                    .as_ref()
                    .is_some_and(|s| s.is_signer(v.id))
                    || self
                        .agg_sig_skip_fallback
                        .as_ref()
                        .is_some_and(|s| s.is_signer(v.id))
            })
            .map(|v| v.stake)
            .sum();

        epoch_info.is_quorum(stake)
    }

    /// Checks that the aggregated signatures are valid.
    #[must_use]
    pub fn check_sig(&self, validators: &[ValidatorInfo]) -> bool {
        let pks: Vec<_> = validators.iter().map(|v| v.voting_pubkey).collect();

        let vote_bytes = VoteKind::Skip(self.slot).bytes_to_sign();
        let sig1_valid = self
            .agg_sig_skip
            .as_ref()
            .is_none_or(|s| s.verify(&vote_bytes, &pks));

        let vote_bytes = VoteKind::SkipFallback(self.slot).bytes_to_sign();
        let sig2_valid = self
            .agg_sig_skip_fallback
            .as_ref()
            .is_none_or(|s| s.verify(&vote_bytes, &pks));

        sig1_valid && sig2_valid
    }
}

/// A fast finalization certificate is an aggregate of a strong quorun of notar votes.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct FastFinalCert {
    slot: Slot,
    block_hash: BlockHash,
    agg_sig: AggregateSignature,
    stake: Stake,
}

impl FastFinalCert {
    /// Tries to create a new fast finalization certificate.
    ///
    /// # Errors
    ///
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    /// - [`CertError::BlockHashMismatch`] if the votes have different block hashes.
    ///
    /// # Panics
    ///
    /// - Panics if `votes` is empty.
    /// - Panics if a signer of a vote is missing from `validators`.
    pub fn try_new(votes: &[NotarVote], validators: &[ValidatorInfo]) -> Result<Self, CertError> {
        let slot = votes[0].slot();
        let block_hash = votes[0].block_hash().clone();

        for vote in votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if vote.block_hash() != &block_hash {
                return Err(CertError::BlockHashMismatch);
            }
        }

        let agg_sig = aggsig_from_votes(votes, validators);
        let stake: Stake = votes
            .iter()
            .map(|v| validators[v.signer().as_index()].stake)
            .sum();

        Ok(Self {
            slot,
            block_hash,
            agg_sig,
            stake,
        })
    }

    /// Creates a new fast finalization certificate.
    ///
    /// # Panics
    ///
    /// Panics if `try_new` returns an error.
    pub fn new_unchecked(votes: &[NotarVote], validators: &[ValidatorInfo]) -> Self {
        Self::try_new(votes, validators).unwrap()
    }

    /// Checks that the stake threshold is met.
    ///
    /// The threshold for [`FastFinalCert`] is >= 80% of the total stake.
    #[must_use]
    pub fn check_threshold(&self, epoch_info: &EpochInfo) -> bool {
        let stake: Stake = epoch_info
            .validators()
            .iter()
            .filter(|v| self.agg_sig.is_signer(v.id))
            .map(|v| v.stake)
            .sum();

        epoch_info.is_strong_quorum(stake)
    }

    /// Checks that the aggregated signatures are valid.
    #[must_use]
    pub fn check_sig(&self, validators: &[ValidatorInfo]) -> bool {
        let pks: Vec<_> = validators.iter().map(|v| v.voting_pubkey).collect();
        let vote_bytes = VoteKind::Notar(self.slot, self.block_hash.clone()).bytes_to_sign();
        self.agg_sig.verify(&vote_bytes, &pks)
    }

    /// Returns the block hash of the fast-finalized block.
    pub const fn block_hash(&self) -> &BlockHash {
        &self.block_hash
    }
}

/// A finalization certificate is an aggregate of a quorum of finalization votes.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct FinalCert {
    slot: Slot,
    agg_sig: AggregateSignature,
    stake: Stake,
}

impl FinalCert {
    /// Tries to create a new finalization certificate.
    ///
    /// # Errors
    ///
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    ///
    /// # Panics
    ///
    /// - Panics if `votes` is empty.
    /// - Panics if a signer of a vote is missing from `validators`.
    pub fn try_new(votes: &[FinalVote], validators: &[ValidatorInfo]) -> Result<Self, CertError> {
        let slot = votes[0].slot();

        for vote in votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            }
        }

        let agg_sig = aggsig_from_votes(votes, validators);
        let stake: Stake = votes
            .iter()
            .map(|v| validators[v.signer().as_index()].stake)
            .sum();

        Ok(Self {
            slot,
            agg_sig,
            stake,
        })
    }

    /// Creates a new finalization certificate.
    ///
    /// # Panics
    ///
    /// Panics if `try_new` returns an error.
    pub fn new_unchecked(votes: &[FinalVote], validators: &[ValidatorInfo]) -> Self {
        Self::try_new(votes, validators).unwrap()
    }

    /// Checks that the stake threshold is met.
    ///
    /// The threshold for [`FinalCert`] is >= 60% of the total stake.
    #[must_use]
    pub fn check_threshold(&self, epoch_info: &EpochInfo) -> bool {
        let stake: Stake = epoch_info
            .validators()
            .iter()
            .filter(|v| self.agg_sig.is_signer(v.id))
            .map(|v| v.stake)
            .sum();

        epoch_info.is_quorum(stake)
    }

    /// Checks that the aggregated signatures are valid.
    #[must_use]
    pub fn check_sig(&self, validators: &[ValidatorInfo]) -> bool {
        let pks: Vec<_> = validators.iter().map(|v| v.voting_pubkey).collect();
        let vote_bytes = VoteKind::Final(self.slot).bytes_to_sign();
        self.agg_sig.verify(&vote_bytes, &pks)
    }
}

fn aggsig_from_votes<V: SignedVote>(
    votes: &[V],
    validators: &[ValidatorInfo],
) -> AggregateSignature {
    let sigs = votes.iter().map(SignedVote::sig);
    let indices = votes.iter().map(SignedVote::signer);
    AggregateSignature::new(sigs, indices, validators.len())
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::crypto::aggsig::SecretKey;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::crypto::{Hash, signature};
    use crate::network::dontcare_sockaddr;

    fn create_signers(signers: u64) -> (Vec<SecretKey>, Vec<ValidatorInfo>) {
        let mut sks = Vec::new();
        let mut voting_sks = Vec::new();
        let mut info = Vec::new();

        for i in 0..signers {
            sks.push(signature::SecretKey::new(&mut rand::rng()));
            voting_sks.push(SecretKey::new(&mut rand::rng()));
            info.push(ValidatorInfo {
                id: ValidatorId::new(i),
                stake: Stake::new(1),
                pubkey: sks.last().unwrap().to_pk(),
                voting_pubkey: voting_sks.last().unwrap().to_pk(),
                all2all_address: dontcare_sockaddr(),
                disseminator_address: dontcare_sockaddr(),
                repair_request_address: dontcare_sockaddr(),
                repair_response_address: dontcare_sockaddr(),
            });
        }

        (voting_sks, info)
    }

    fn create_notar_votes(
        slot: Slot,
        hash: &BlockHash,
        sks: &[SecretKey],
        id_offset: usize,
    ) -> Vec<NotarVote> {
        sks.iter()
            .enumerate()
            .map(|(i, sk)| {
                let v = ValidatorId::new((i + id_offset) as u64);
                NotarVote::new(slot, hash.clone(), sk, v)
            })
            .collect()
    }

    fn create_nf_votes(
        slot: Slot,
        hash: &BlockHash,
        sks: &[SecretKey],
        id_offset: usize,
    ) -> Vec<NotarFallbackVote> {
        sks.iter()
            .enumerate()
            .map(|(i, sk)| {
                let v = ValidatorId::new((i + id_offset) as u64);
                NotarFallbackVote::new(slot, hash.clone(), sk, v)
            })
            .collect()
    }

    fn create_skip_votes(slot: Slot, sks: &[SecretKey], id_offset: usize) -> Vec<SkipVote> {
        sks.iter()
            .enumerate()
            .map(|(i, sk)| SkipVote::new(slot, sk, ValidatorId::new((i + id_offset) as u64)))
            .collect()
    }

    fn create_final_votes(slot: Slot, sks: &[SecretKey], id_offset: usize) -> Vec<FinalVote> {
        sks.iter()
            .enumerate()
            .map(|(i, sk)| FinalVote::new(slot, sk, ValidatorId::new((i + id_offset) as u64)))
            .collect()
    }

    fn check_full_cert(cert: Cert, info: &[ValidatorInfo]) {
        let total_stake: Stake = info.iter().map(|v| v.stake).sum();
        assert!(cert.check_sig(info));
        assert_eq!(cert.stake(), total_stake);
        let signers: HashSet<_> = cert.signers().collect();
        for v in info {
            assert!(cert.is_signer(v.id));
            assert!(signers.contains(&v.id));
        }
    }

    #[test]
    fn create() {
        let (sks, info) = create_signers(100);

        let votes = create_notar_votes(Slot::genesis(), &GENESIS_BLOCK_HASH, &sks, 0);
        let res = NotarCert::try_new(&votes, &info);
        assert!(res.is_ok());
        check_full_cert(Cert::Notar(res.unwrap()), &info);

        let nf_votes = create_nf_votes(Slot::genesis(), &GENESIS_BLOCK_HASH, &sks, 0);
        let res = NotarFallbackCert::try_new(&[], &nf_votes, &info);
        assert!(res.is_ok());
        check_full_cert(Cert::NotarFallback(res.unwrap()), &info);

        let skip_votes = create_skip_votes(Slot::genesis(), &sks, 0);
        let res = SkipCert::try_new(&skip_votes, &[], &info);
        assert!(res.is_ok());
        check_full_cert(Cert::Skip(res.unwrap()), &info);

        let votes = create_notar_votes(Slot::genesis(), &GENESIS_BLOCK_HASH, &sks, 0);
        let res = FastFinalCert::try_new(&votes, &info);
        assert!(res.is_ok());
        check_full_cert(Cert::FastFinal(res.unwrap()), &info);

        let votes = create_final_votes(Slot::genesis(), &sks, 0);
        let res = FinalCert::try_new(&votes, &info);
        assert!(res.is_ok());
        check_full_cert(Cert::Final(res.unwrap()), &info);
    }

    #[test]
    fn mixed_notar_fallback() {
        let (sks, info) = create_signers(2);

        // one notar + one notar-fallback
        let notar_votes = vec![NotarVote::new(
            Slot::genesis(),
            GENESIS_BLOCK_HASH,
            &sks[0],
            ValidatorId::new(0),
        )];
        let nf_votes = vec![NotarFallbackVote::new(
            Slot::genesis(),
            GENESIS_BLOCK_HASH,
            &sks[1],
            ValidatorId::new(1),
        )];
        let res = NotarFallbackCert::try_new(&notar_votes, &nf_votes, &info);
        assert!(res.is_ok());
        let cert = Cert::NotarFallback(res.unwrap());
        check_full_cert(cert, &info);
    }

    #[test]
    fn mixed_skip() {
        let (sks, info) = create_signers(2);

        // one skip + one skip-fallback
        let skip_votes = vec![SkipVote::new(Slot::genesis(), &sks[0], ValidatorId::new(0))];
        let sf_votes = vec![SkipFallbackVote::new(
            Slot::genesis(),
            &sks[1],
            ValidatorId::new(1),
        )];
        let res = SkipCert::try_new(&skip_votes, &sf_votes, &info);
        assert!(res.is_ok());
        let cert = Cert::Skip(res.unwrap());
        check_full_cert(cert, &info);
    }

    #[test]
    fn notar_failure_cases() {
        let (sks, info) = create_signers(2);
        let hash: BlockHash = Hash::random_for_test().into();

        // slot mismatch
        let vote1 = NotarVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let vote2 = NotarVote::new(Slot::new(2), hash.clone(), &sks[1], ValidatorId::new(1));
        let res = NotarCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // block hash mismatch
        let vote1 = NotarVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let vote2 = NotarVote::new(
            Slot::new(1),
            Hash::random_for_test().into(),
            &sks[1],
            ValidatorId::new(1),
        );
        let res = NotarCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::BlockHashMismatch));
    }

    #[test]
    fn notar_fallback_failure_cases() {
        let (sks, info) = create_signers(2);
        let hash: BlockHash = Hash::random_for_test().into();

        // slot mismatch in notar-fallback votes
        let vote1 =
            NotarFallbackVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let vote2 =
            NotarFallbackVote::new(Slot::new(2), hash.clone(), &sks[1], ValidatorId::new(1));
        let res = NotarFallbackCert::try_new(&[], &[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // slot mismatch: notar vote in different slot than notar-fallback
        let nv = NotarVote::new(Slot::new(2), hash.clone(), &sks[0], ValidatorId::new(0));
        let nfv = NotarFallbackVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(1));
        let res = NotarFallbackCert::try_new(&[nv], &[nfv], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // block hash mismatch in notar-fallback votes
        let vote1 =
            NotarFallbackVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let vote2 = NotarFallbackVote::new(
            Slot::new(1),
            Hash::random_for_test().into(),
            &sks[1],
            ValidatorId::new(1),
        );
        let res = NotarFallbackCert::try_new(&[], &[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::BlockHashMismatch));
    }

    #[test]
    fn skip_failure_cases() {
        let (sks, info) = create_signers(2);

        // slot mismatch in skip votes
        let vote1 = SkipVote::new(Slot::new(1), &sks[0], ValidatorId::new(0));
        let vote2 = SkipVote::new(Slot::new(2), &sks[1], ValidatorId::new(1));
        let res = SkipCert::try_new(&[vote1, vote2], &[], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // slot mismatch: skip-fallback in different slot than skip
        let sv = SkipVote::new(Slot::new(2), &sks[0], ValidatorId::new(0));
        let sfv = SkipFallbackVote::new(Slot::new(1), &sks[1], ValidatorId::new(1));
        let res = SkipCert::try_new(&[sv], &[sfv], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));
    }

    #[test]
    fn fast_final_failure_cases() {
        let (sks, info) = create_signers(2);
        let hash: BlockHash = Hash::random_for_test().into();

        // slot mismatch
        let vote1 = NotarVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let vote2 = NotarVote::new(Slot::new(2), hash.clone(), &sks[1], ValidatorId::new(1));
        let res = FastFinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // block hash mismatch
        let vote1 = NotarVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let vote2 = NotarVote::new(
            Slot::new(1),
            Hash::random_for_test().into(),
            &sks[1],
            ValidatorId::new(1),
        );
        let res = FastFinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::BlockHashMismatch));
    }

    #[test]
    fn final_failure_cases() {
        let (sks, info) = create_signers(2);

        // slot mismatch
        let vote1 = FinalVote::new(Slot::new(1), &sks[0], ValidatorId::new(0));
        let vote2 = FinalVote::new(Slot::new(2), &sks[1], ValidatorId::new(1));
        let res = FinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));
    }

    #[test]
    fn notar_stake_threshold() {
        let (sks, info) = create_signers(11);
        let epoch = EpochInfo::new(info.clone());
        let hash: BlockHash = Hash::random_for_test().into();

        // 7/11 enough for 60% threshold
        let votes = create_notar_votes(Slot::new(1), &hash, &sks[..7], 0);
        let cert = NotarCert::try_new(&votes, &info).unwrap();
        assert!(cert.check_threshold(&epoch));

        // 6/11 NOT enough for 60% threshold
        let votes = create_notar_votes(Slot::new(1), &hash, &sks[..6], 0);
        let cert = NotarCert::try_new(&votes, &info).unwrap();
        assert!(!cert.check_threshold(&epoch));
    }

    #[test]
    fn notar_fallback_stake_threshold() {
        let (sks, info) = create_signers(11);
        let epoch = EpochInfo::new(info.clone());
        let hash: BlockHash = Hash::random_for_test().into();

        // 7/11 enough for 60% threshold (mixed notar + notar-fallback)
        let notar_votes = create_notar_votes(Slot::new(1), &hash, &sks[..4], 0);
        let nf_votes = create_nf_votes(Slot::new(1), &hash, &sks[4..7], 4);
        let cert = NotarFallbackCert::try_new(&notar_votes, &nf_votes, &info).unwrap();
        assert!(cert.check_threshold(&epoch));

        // 6/11 NOT enough for 60% threshold
        let notar_votes = create_notar_votes(Slot::new(1), &hash, &sks[..3], 0);
        let nf_votes = create_nf_votes(Slot::new(1), &hash, &sks[3..6], 3);
        let cert = NotarFallbackCert::try_new(&notar_votes, &nf_votes, &info).unwrap();
        assert!(!cert.check_threshold(&epoch));
    }

    #[test]
    fn skip_stake_threshold() {
        let (sks, info) = create_signers(11);
        let epoch = EpochInfo::new(info.clone());

        // 7/11 enough for 60% threshold
        let votes = create_skip_votes(Slot::new(1), &sks[..7], 0);
        let cert = SkipCert::try_new(&votes, &[], &info).unwrap();
        assert!(cert.check_threshold(&epoch));

        // 6/11 NOT enough for 60% threshold
        let votes = create_skip_votes(Slot::new(1), &sks[..6], 0);
        let cert = SkipCert::try_new(&votes, &[], &info).unwrap();
        assert!(!cert.check_threshold(&epoch));
    }

    #[test]
    fn final_stake_threshold() {
        let (sks, info) = create_signers(11);
        let epoch = EpochInfo::new(info.clone());

        // 7/11 enough for 60% threshold
        let votes = create_final_votes(Slot::new(1), &sks[..7], 0);
        let cert = FinalCert::try_new(&votes, &info).unwrap();
        assert!(cert.check_threshold(&epoch));

        // 6/11 NOT enough for 60% threshold
        let votes = create_final_votes(Slot::new(1), &sks[..6], 0);
        let cert = FinalCert::try_new(&votes, &info).unwrap();
        assert!(!cert.check_threshold(&epoch));
    }

    #[test]
    fn fast_final_stake_threshold() {
        let (sks, info) = create_signers(11);
        let epoch = EpochInfo::new(info.clone());
        let hash: BlockHash = Hash::random_for_test().into();

        // 9/11 enough for 80% threshold
        let votes = create_notar_votes(Slot::new(1), &hash, &sks[..9], 0);
        let cert = FastFinalCert::try_new(&votes, &info).unwrap();
        assert!(cert.check_threshold(&epoch));

        // 8/11 NOT enough for 80% threshold
        let votes = create_notar_votes(Slot::new(1), &hash, &sks[..8], 0);
        let cert = FastFinalCert::try_new(&votes, &info).unwrap();
        assert!(!cert.check_threshold(&epoch));
    }

    #[test]
    fn notar_sig_validity() {
        let (sks, info) = create_signers(2);
        let hash: BlockHash = Hash::random_for_test().into();

        // valid sig
        let vote1 = NotarVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let vote2 = NotarVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(1));
        let cert = NotarCert::try_new(&[vote1, vote2], &info).unwrap();
        assert!(cert.check_sig(&info));

        // invalid sig (wrong key for validator 0)
        let vote1 = NotarVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(0));
        let vote2 = NotarVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(1));
        let cert = NotarCert::try_new(&[vote1, vote2], &info).unwrap();
        assert!(!cert.check_sig(&info));
    }

    #[test]
    fn notar_fallback_sig_validity() {
        let (sks, info) = create_signers(2);
        let hash: BlockHash = Hash::random_for_test().into();

        // valid sig
        let nv = NotarVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let nfv = NotarFallbackVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(1));
        let cert = NotarFallbackCert::try_new(&[nv], &[nfv], &info).unwrap();
        assert!(cert.check_sig(&info));

        // invalid sig (wrong key for validator 0)
        let nv = NotarVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(0));
        let nfv = NotarFallbackVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(1));
        let cert = NotarFallbackCert::try_new(&[nv], &[nfv], &info).unwrap();
        assert!(!cert.check_sig(&info));
    }

    #[test]
    fn skip_sig_validity() {
        let (sks, info) = create_signers(2);

        // valid sig
        let vote1 = SkipVote::new(Slot::new(1), &sks[0], ValidatorId::new(0));
        let vote2 = SkipVote::new(Slot::new(1), &sks[1], ValidatorId::new(1));
        let cert = SkipCert::try_new(&[vote1, vote2], &[], &info).unwrap();
        assert!(cert.check_sig(&info));

        // invalid sig (wrong key for validator 0)
        let vote1 = SkipVote::new(Slot::new(1), &sks[1], ValidatorId::new(0));
        let vote2 = SkipVote::new(Slot::new(1), &sks[1], ValidatorId::new(1));
        let cert = SkipCert::try_new(&[vote1, vote2], &[], &info).unwrap();
        assert!(!cert.check_sig(&info));
    }

    #[test]
    fn final_sig_validity() {
        let (sks, info) = create_signers(2);

        // valid sig
        let vote1 = FinalVote::new(Slot::new(1), &sks[0], ValidatorId::new(0));
        let vote2 = FinalVote::new(Slot::new(1), &sks[1], ValidatorId::new(1));
        let cert = FinalCert::try_new(&[vote1, vote2], &info).unwrap();
        assert!(cert.check_sig(&info));

        // invalid sig (wrong key for validator 0)
        let vote1 = FinalVote::new(Slot::new(1), &sks[1], ValidatorId::new(0));
        let vote2 = FinalVote::new(Slot::new(1), &sks[1], ValidatorId::new(1));
        let cert = FinalCert::try_new(&[vote1, vote2], &info).unwrap();
        assert!(!cert.check_sig(&info));
    }

    #[test]
    fn fast_final_sig_validity() {
        let (sks, info) = create_signers(2);
        let hash: BlockHash = Hash::random_for_test().into();

        // valid sig
        let vote1 = NotarVote::new(Slot::new(1), hash.clone(), &sks[0], ValidatorId::new(0));
        let vote2 = NotarVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(1));
        let cert = FastFinalCert::try_new(&[vote1, vote2], &info).unwrap();
        assert!(cert.check_sig(&info));

        // invalid sig (wrong key for validator 0)
        let vote1 = NotarVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(0));
        let vote2 = NotarVote::new(Slot::new(1), hash.clone(), &sks[1], ValidatorId::new(1));
        let cert = FastFinalCert::try_new(&[vote1, vote2], &info).unwrap();
        assert!(!cert.check_sig(&info));
    }
}
