// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatedVote`] type.

use thiserror::Error;

use super::{EpochInfo, Vote};
use crate::Slot;

/// Different errors returned from [`ValidatedVote::try_new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum VoteValidationError {
    /// The signer is not a validator in the current epoch.
    #[error("signer is not a validator in the current epoch")]
    UnknownSigner,
    /// The signature verification failed.
    #[error("invalid signature on the vote")]
    InvalidSignature,
}

/// A validated wrapper around a [`Vote`].
///
/// It uses the new type pattern to encode verification in the type system.
/// The encapsulated [`Vote`] has passed all signature-level checks:
/// - the signer is a known validator in the epoch, and
/// - the signature is valid under that validator's voting key.
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct ValidatedVote {
    vote: Vote,
}

impl ValidatedVote {
    /// Verifies the signer and signature of `vote`.
    ///
    /// Returns a [`ValidatedVote`] on success.
    ///
    /// # Errors
    ///
    /// Returns [`VoteValidationError`] if the [`Vote`] does not pass all verification checks.
    #[hotpath::measure]
    pub fn try_new(vote: Vote, epoch_info: &EpochInfo) -> Result<Self, VoteValidationError> {
        // reject votes from validators outside the current epoch's set,
        // otherwise `validator()` indexing below would panic on byzantine input
        if vote.signer().inner() >= epoch_info.validators().len() as u64 {
            return Err(VoteValidationError::UnknownSigner);
        }

        // verify the signature under the signer's voting key
        let pk = &epoch_info.validator(vote.signer()).voting_pubkey;
        if !vote.check_sig(pk) {
            return Err(VoteValidationError::InvalidSignature);
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
        let v = ValidatorIndex::new(0);
        let vote = Vote::new_notar(Slot::new(0), GENESIS_BLOCK_HASH, &sks[v.as_usize()], v);
        let validated = ValidatedVote::try_new(vote.clone(), &epoch_info).unwrap();
        assert_eq!(validated.into_vote(), vote);
    }

    #[test]
    fn invalid_signature() {
        let (sks, epoch_info) = generate_validators(11);
        // sign with validator 1's key but claim to be validator 0
        let v = ValidatorIndex::new(0);
        let vote = Vote::new_notar(Slot::new(0), GENESIS_BLOCK_HASH, &sks[1], v);
        assert_eq!(
            ValidatedVote::try_new(vote, &epoch_info),
            Err(VoteValidationError::InvalidSignature)
        );
    }

    #[test]
    fn unknown_signer() {
        let (sks, epoch_info) = generate_validators(11);
        let num_validators = epoch_info.validators().len() as u64;

        // claim a `signer` out-of-bounds for the validator set
        let signer = ValidatorIndex::new(num_validators);
        let vote = Vote::new_notar(Slot::new(0), GENESIS_BLOCK_HASH, &sks[0], signer);
        assert_eq!(
            ValidatedVote::try_new(vote, &epoch_info),
            Err(VoteValidationError::UnknownSigner)
        );
    }
}
