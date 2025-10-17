// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Certificate types used for the consensus protocol.
//!
//!

use thiserror::Error;
use wincode::{SchemaRead, SchemaWrite};

use super::Vote;
use super::vote::VoteKind;
use crate::crypto::merkle::BlockHash;
use crate::crypto::{AggregateSignature, Signable};
use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

/// Errors that can occur during certificate aggregation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum CertError {
    #[error("wrong vote type found during aggregation")]
    WrongVoteType,
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
    /// - [`CertError::WrongVoteType`] if any of the votes is not a notarization vote.
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    /// - [`CertError::BlockHashMismatch`] if the votes have different block hashes.
    pub fn try_new(votes: &[Vote], validators: &[ValidatorInfo]) -> Result<Self, CertError> {
        if !votes[0].is_notar() {
            return Err(CertError::WrongVoteType);
        }
        let slot = votes[0].slot();
        let block_hash = votes[0].block_hash().unwrap().clone();

        for vote in votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if !vote.is_notar() {
                return Err(CertError::WrongVoteType);
            } else if vote.block_hash() != Some(&block_hash) {
                return Err(CertError::BlockHashMismatch);
            }
        }

        let agg_sig = aggsig_from_votes(votes, validators);
        let stake: Stake = votes
            .iter()
            .map(|v| validators[v.signer() as usize].stake)
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
    pub fn new_unchecked(votes: &[Vote], validators: &[ValidatorInfo]) -> Self {
        Self::try_new(votes, validators).unwrap()
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
    /// # Errors
    ///
    /// - [`CertError::WrongVoteType`] if any of the votes is not a notar(-fallback) vote.
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    /// - [`CertError::BlockHashMismatch`] if the votes have different block hashes.
    pub fn try_new(votes: &[Vote], validators: &[ValidatorInfo]) -> Result<Self, CertError> {
        if !votes[0].is_notar() && !votes[0].is_notar_fallback() {
            return Err(CertError::WrongVoteType);
        };
        let slot = votes[0].slot();
        let block_hash = votes[0].block_hash().unwrap().clone();

        for vote in votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if !vote.is_notar() && !vote.is_notar_fallback() {
                return Err(CertError::WrongVoteType);
            } else if vote.block_hash() != Some(&block_hash) {
                return Err(CertError::BlockHashMismatch);
            }
        }

        let stake: Stake = votes
            .iter()
            .map(|v| validators[v.signer() as usize].stake)
            .sum();

        let mut notar_votes = votes.iter().filter(|v| v.is_notar()).peekable();
        let mut nf_votes = votes.iter().filter(|v| v.is_notar_fallback()).peekable();

        let agg_sig_notar = if notar_votes.peek().is_none() {
            None
        } else {
            Some(aggsig_from_votes_iter(notar_votes, validators))
        };

        let agg_sig_notar_fallback = if nf_votes.peek().is_none() {
            None
        } else {
            Some(aggsig_from_votes_iter(nf_votes, validators))
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
    pub fn new_unchecked(votes: &[Vote], validators: &[ValidatorInfo]) -> Self {
        Self::try_new(votes, validators).unwrap()
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
    /// # Errors
    ///
    /// - [`CertError::WrongVoteType`] if any of the votes is not a skip(-fallback) vote.
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    pub fn try_new(votes: &[Vote], validators: &[ValidatorInfo]) -> Result<Self, CertError> {
        if !votes[0].is_skip() && !votes[0].is_skip_fallback() {
            return Err(CertError::WrongVoteType);
        }
        let slot = votes[0].slot();

        for vote in votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if !vote.is_skip() && !vote.is_skip_fallback() {
                return Err(CertError::WrongVoteType);
            }
        }

        let stake: Stake = votes
            .iter()
            .map(|v| validators[v.signer() as usize].stake)
            .sum();

        let mut skip_votes = votes.iter().filter(|v| v.is_skip()).peekable();
        let mut sf_votes = votes.iter().filter(|v| v.is_skip_fallback()).peekable();

        let agg_sig_skip = if skip_votes.peek().is_none() {
            None
        } else {
            Some(aggsig_from_votes_iter(skip_votes, validators))
        };

        let agg_sig_skip_fallback = if sf_votes.peek().is_none() {
            None
        } else {
            Some(aggsig_from_votes_iter(sf_votes, validators))
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
    pub fn new_unchecked(votes: &[Vote], validators: &[ValidatorInfo]) -> Self {
        Self::try_new(votes, validators).unwrap()
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
    /// - [`CertError::WrongVoteType`] if any of the votes is not a notarization vote.
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    /// - [`CertError::BlockHashMismatch`] if the votes have different block hashes.
    pub fn try_new(votes: &[Vote], validators: &[ValidatorInfo]) -> Result<Self, CertError> {
        if !votes[0].is_notar() {
            return Err(CertError::WrongVoteType);
        }
        let slot = votes[0].slot();
        let block_hash = votes[0].block_hash().unwrap().clone();

        for vote in votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if !vote.is_notar() {
                return Err(CertError::WrongVoteType);
            } else if vote.block_hash() != Some(&block_hash) {
                return Err(CertError::BlockHashMismatch);
            }
        }

        let agg_sig = aggsig_from_votes(votes, validators);
        let stake: Stake = votes
            .iter()
            .map(|v| validators[v.signer() as usize].stake)
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
    pub fn new_unchecked(votes: &[Vote], validators: &[ValidatorInfo]) -> Self {
        Self::try_new(votes, validators).unwrap()
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
    /// - [`CertError::WrongVoteType`] if any of the votes is not a finalization vote.
    /// - [`CertError::SlotMismatch`] if the votes have different slots.
    pub fn try_new(votes: &[Vote], validators: &[ValidatorInfo]) -> Result<Self, CertError> {
        if !votes[0].is_final() {
            return Err(CertError::WrongVoteType);
        }
        let slot = votes[0].slot();

        for vote in votes {
            if vote.slot() != slot {
                return Err(CertError::SlotMismatch);
            } else if !vote.is_final() {
                return Err(CertError::WrongVoteType);
            }
        }

        let agg_sig = aggsig_from_votes(votes, validators);
        let stake: Stake = votes
            .iter()
            .map(|v| validators[v.signer() as usize].stake)
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
    pub fn new_unchecked(votes: &[Vote], validators: &[ValidatorInfo]) -> Self {
        Self::try_new(votes, validators).unwrap()
    }

    /// Checks that the aggregated signatures are valid.
    #[must_use]
    pub fn check_sig(&self, validators: &[ValidatorInfo]) -> bool {
        let pks: Vec<_> = validators.iter().map(|v| v.voting_pubkey).collect();
        let vote_bytes = VoteKind::Final(self.slot).bytes_to_sign();
        self.agg_sig.verify(&vote_bytes, &pks)
    }
}

fn aggsig_from_votes(votes: &[Vote], validators: &[ValidatorInfo]) -> AggregateSignature {
    let sigs = votes.iter().map(Vote::sig);
    let indices = votes.iter().map(Vote::signer);
    AggregateSignature::new(sigs, indices, validators.len())
}

fn aggsig_from_votes_iter<'a>(
    votes: impl IntoIterator<Item = &'a Vote> + Clone,
    validators: &[ValidatorInfo],
) -> AggregateSignature {
    let sigs = votes.clone().into_iter().map(Vote::sig);
    let indices = votes.into_iter().map(Vote::signer);
    AggregateSignature::new(sigs, indices, validators.len())
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::crypto::aggsig::SecretKey;
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
                id: i,
                stake: 1,
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

    fn create_votes(kind: VoteKind, sks: &[SecretKey]) -> Vec<Vote> {
        sks.iter()
            .enumerate()
            .map(|(i, sk)| Vote::new(kind.clone(), sk, i as ValidatorId))
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

        // notar cert
        let votes = create_votes(VoteKind::Notar(Slot::new(0), Hash::default().into()), &sks);
        let res = NotarCert::try_new(&votes, &info);
        assert!(res.is_ok());
        let cert = Cert::Notar(res.unwrap());
        check_full_cert(cert, &info);

        // notar-fallback cert
        let votes = create_votes(
            VoteKind::NotarFallback(Slot::new(0), Hash::default().into()),
            &sks,
        );
        let res = NotarFallbackCert::try_new(&votes, &info);
        assert!(res.is_ok());
        let cert = Cert::NotarFallback(res.unwrap());
        check_full_cert(cert, &info);

        // skip cert
        let votes = create_votes(VoteKind::Skip(Slot::new(0)), &sks);
        let res = SkipCert::try_new(&votes, &info);
        assert!(res.is_ok());
        let cert = Cert::Skip(res.unwrap());
        check_full_cert(cert, &info);

        // fast finalization cert
        let votes = create_votes(VoteKind::Notar(Slot::new(0), Hash::default().into()), &sks);
        let res = FastFinalCert::try_new(&votes, &info);
        assert!(res.is_ok());
        let cert = Cert::FastFinal(res.unwrap());
        check_full_cert(cert, &info);

        // finalization cert
        let votes = create_votes(VoteKind::Final(Slot::new(0)), &sks);
        let res = FinalCert::try_new(&votes, &info);
        assert!(res.is_ok());
        let cert = Cert::Final(res.unwrap());
        check_full_cert(cert, &info);
    }

    #[test]
    fn mixed_notar_fallback() {
        let (sks, info) = create_signers(2);

        // notar + notar-fallback
        let vote1 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[1], 1);
        let res = NotarFallbackCert::try_new(&[vote1, vote2], &info);
        assert!(res.is_ok());
        let cert = Cert::NotarFallback(res.unwrap());
        check_full_cert(cert, &info);

        // notar-fallback + notar
        let vote1 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[1], 1);
        let res = NotarFallbackCert::try_new(&[vote1, vote2], &info);
        assert!(res.is_ok());
        let cert = Cert::NotarFallback(res.unwrap());
        check_full_cert(cert, &info);
    }

    #[test]
    fn mixed_skip() {
        let (sks, info) = create_signers(2);

        // skip + skip-fallback
        let vote1 = Vote::new_skip(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_skip_fallback(Slot::new(0), &sks[1], 1);
        let res = SkipCert::try_new(&[vote1, vote2], &info);
        assert!(res.is_ok());
        let cert = Cert::Skip(res.unwrap());
        check_full_cert(cert, &info);

        // skip-fallback + skip
        let vote1 = Vote::new_skip_fallback(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_skip(Slot::new(0), &sks[1], 1);
        let res = SkipCert::try_new(&[vote1, vote2], &info);
        assert!(res.is_ok());
        let cert = Cert::Skip(res.unwrap());
        check_full_cert(cert, &info);
    }

    #[test]
    fn notar_failure_cases() {
        let (sks, info) = create_signers(2);

        // slot mismatch
        let vote1 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar(Slot::new(1), Hash::default().into(), &sks[1], 1);
        let res = NotarCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // block hash mismatch
        let vote1 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar(Slot::new(0), [42; 32].into(), &sks[1], 1);
        let res = NotarCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::BlockHashMismatch));

        // different vote types
        let vote1 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[1], 1);
        let res = NotarCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));

        // wrong vote type for cert
        let vote1 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[1], 1);
        let res = NotarCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));
    }

    #[test]
    fn notar_fallback_failure_cases() {
        let (sks, info) = create_signers(2);

        // slot mismatch
        let vote1 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar_fallback(Slot::new(1), Hash::default().into(), &sks[1], 1);
        let res = NotarFallbackCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // block hash mismatch
        let vote1 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar_fallback(Slot::new(0), [42; 32].into(), &sks[1], 1);
        let res = NotarFallbackCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::BlockHashMismatch));

        // wrong vote types for cert
        let vote1 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_final(Slot::new(0), &sks[1], 1);
        let res = NotarFallbackCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));

        // wrong vote type for cert
        let vote1 = Vote::new_final(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_final(Slot::new(0), &sks[1], 1);
        let res = NotarFallbackCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));
    }

    #[test]
    fn skip_failure_cases() {
        let (sks, info) = create_signers(2);

        // slot mismatch
        let vote1 = Vote::new_skip(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_skip(Slot::new(1), &sks[1], 1);
        let res = SkipCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // wrong vote type for cert
        let vote1 = Vote::new_skip(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_final(Slot::new(0), &sks[1], 1);
        let res = SkipCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));

        // wrong vote type for cert
        let vote1 = Vote::new_final(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_final(Slot::new(0), &sks[1], 1);
        let res = SkipCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));
    }

    #[test]
    fn fast_final_failure_cases() {
        let (sks, info) = create_signers(2);

        // slot mismatch
        let vote1 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar(Slot::new(1), Hash::default().into(), &sks[1], 1);
        let res = FastFinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // block hash mismatch
        let vote1 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar(Slot::new(0), [42; 32].into(), &sks[1], 1);
        let res = FastFinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::BlockHashMismatch));

        // wrong vote type for cert
        let vote1 = Vote::new_notar(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[1], 1);
        let res = FastFinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));

        // wrong vote type for cert
        let vote1 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[0], 0);
        let vote2 = Vote::new_notar_fallback(Slot::new(0), Hash::default().into(), &sks[1], 1);
        let res = FastFinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));
    }

    #[test]
    fn final_failure_cases() {
        let (sks, info) = create_signers(2);

        // slot mismatch
        let vote1 = Vote::new_final(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_final(Slot::new(1), &sks[1], 1);
        let res = FinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::SlotMismatch));

        // wrong vote type for cert
        let vote1 = Vote::new_final(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_skip(Slot::new(0), &sks[1], 1);
        let res = FinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));

        // wrong vote type for cert
        let vote1 = Vote::new_skip(Slot::new(0), &sks[0], 0);
        let vote2 = Vote::new_skip(Slot::new(0), &sks[1], 1);
        let res = FinalCert::try_new(&[vote1, vote2], &info);
        assert_eq!(res.err(), Some(CertError::WrongVoteType));
    }
}
