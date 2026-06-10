// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatedVote`] type.

use thiserror::Error;

use super::{EpochInfo, Vote};
use crate::Slot;

/// Different errors returned from [`ValidatedVote::try_new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum VoteVerifyError {
    /// The signer is not a validator in the current epoch.
    #[error("signer is not a validator in the current epoch")]
    UnknownSigner,
    /// The signature verification failed.
    #[error("invalid signature on the vote")]
    InvalidSignature,
}

/// A verified wrapper around a [`Vote`].
///
/// It uses the new type pattern to encode verification in the type system.
/// The encapsulated [`Vote`] has passed all signature-level checks:
/// - the signer is a known validator in the epoch, and
/// - the signature is valid under that validator's voting key.
///
/// This mirrors [`ValidatedShred`] on the shred path: the expensive BLS
/// verification is performed once, up front, so that downstream consumers
/// (i.e. the [`Pool`]) can merge the vote into per-slot state without holding
/// a lock during signature verification.
///
/// [`ValidatedShred`]: crate::shredder::ValidatedShred
/// [`Pool`]: crate::consensus::Pool
#[derive(Clone, Debug)]
pub struct ValidatedVote {
    vote: Vote,
}

impl ValidatedVote {
    /// Verifies the signer and signature of `vote`, returning a [`ValidatedVote`] on success.
    ///
    /// # Errors
    ///
    /// Returns [`VoteVerifyError`] if the [`Vote`] does not pass all verification checks.
    #[hotpath::measure]
    pub fn try_new(vote: Vote, epoch_info: &EpochInfo) -> Result<Self, VoteVerifyError> {
        // reject votes from validators outside the current epoch's set,
        // otherwise `validator()` indexing below would panic on byzantine input
        if vote.signer().inner() >= epoch_info.validators().len() as u64 {
            return Err(VoteVerifyError::UnknownSigner);
        }

        // verify the signature under the signer's voting key
        let pk = &epoch_info.validator(vote.signer()).voting_pubkey;
        if !vote.check_sig(pk) {
            return Err(VoteVerifyError::InvalidSignature);
        }

        Ok(Self { vote })
    }

    /// Returns the slot this vote is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        self.vote.slot()
    }

    /// Consumes `self`, returning the inner [`Vote`].
    #[must_use]
    pub fn into_vote(self) -> Vote {
        self.vote
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ValidatorIndex;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::test_utils::generate_validators;

    #[test]
    fn valid_vote() {
        let (sks, epoch_info) = generate_validators(11);
        let signer = ValidatorIndex::new(0);
        let vote = Vote::new_notar(Slot::new(0), GENESIS_BLOCK_HASH, &sks[0], signer);
        let validated = ValidatedVote::try_new(vote.clone(), &epoch_info).unwrap();
        assert_eq!(validated.into_vote(), vote);
    }

    #[test]
    fn invalid_signature() {
        let (sks, epoch_info) = generate_validators(11);
        // sign with validator 1's key but claim to be validator 0
        let vote = Vote::new_notar(
            Slot::new(0),
            GENESIS_BLOCK_HASH,
            &sks[1],
            ValidatorIndex::new(0),
        );
        assert!(matches!(
            ValidatedVote::try_new(vote, &epoch_info),
            Err(VoteVerifyError::InvalidSignature)
        ));
    }

    #[test]
    fn unknown_signer() {
        let (sks, epoch_info) = generate_validators(11);
        let num_validators = epoch_info.validators().len() as u64;

        // claim a `signer` out-of-bounds for the validator set
        let vote = Vote::new_notar(
            Slot::new(0),
            GENESIS_BLOCK_HASH,
            &sks[0],
            ValidatorIndex::new(num_validators),
        );
        assert!(matches!(
            ValidatedVote::try_new(vote, &epoch_info),
            Err(VoteVerifyError::UnknownSigner)
        ));

        let vote = Vote::new_skip(Slot::new(0), &sks[0], ValidatorIndex::new(u64::MAX));
        assert!(matches!(
            ValidatedVote::try_new(vote, &epoch_info),
            Err(VoteVerifyError::UnknownSigner)
        ));
    }
}
