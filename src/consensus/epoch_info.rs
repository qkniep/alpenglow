// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use thiserror::Error;

use crate::consensus::{
    QUORUM_THRESHOLD, STRONG_QUORUM_THRESHOLD, WEAK_QUORUM_THRESHOLD, WEAKEST_QUORUM_THRESHOLD,
};
use crate::types::SLOTS_PER_WINDOW;
use crate::{Slot, Stake, ValidatorIndex, ValidatorInfo};

/// Errors that can occur when validating a validator set into an [`EpochInfo`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum EpochInfoError {
    /// A validator's `id` does not match its position in the validator set.
    #[error("validator at index {index} has id {id}, expected {index}")]
    IdIndexMismatch { index: usize, id: ValidatorIndex },
    /// A validator's proof of possession does not verify against its voting key.
    #[error("validator {0} has an invalid BLS proof of possession")]
    InvalidProofOfPossession(ValidatorIndex),
}

/// Shared epoch information, identical across all validators.
///
/// Contains the validator set and derived data for one epoch.
/// Constructed once per epoch and shared via [`std::sync::Arc`].
#[derive(Clone, Debug)]
pub struct EpochInfo {
    validators: Vec<ValidatorInfo>,
    total_stake: Stake,
}

/// Per-validator epoch information, wrapping shared [`EpochInfo`].
///
/// Adds the node's own identity on top of the shared epoch data.
#[derive(Clone, Debug)]
pub struct ValidatorEpochInfo {
    own_id: ValidatorIndex,
    epoch: EpochInfo,
}

impl EpochInfo {
    /// Tries to create a new `EpochInfo` from the given validator set.
    ///
    /// This is the only constructor, which makes it the trust boundary for the
    /// rest of the protocol: it verifies every validator's BLS proof of
    /// possession (`voting_pop`), so downstream code can treat any key reachable
    /// from an `EpochInfo` as PoP-checked. That is what makes
    /// [`AggregateSignature::verify`] sound against the rogue-key attack.
    /// Checking once here, rather than per vote, keeps the hot path cheap.
    ///
    /// # Errors
    ///
    /// - [`EpochInfoError::IdIndexMismatch`] if any validator's `id` does not
    ///   match its index in the vector.
    /// - [`EpochInfoError::InvalidProofOfPossession`] if any validator's
    ///   `voting_pop` fails to verify against its `voting_pubkey`.
    ///
    /// [`AggregateSignature::verify`]: crate::crypto::AggregateSignature::verify
    pub fn try_new(validators: Vec<ValidatorInfo>) -> Result<Self, EpochInfoError> {
        for (index, v) in validators.iter().enumerate() {
            if v.id.as_usize() != index {
                return Err(EpochInfoError::IdIndexMismatch { index, id: v.id });
            }
            if !v.voting_pubkey.verify_pop(&v.voting_pop) {
                return Err(EpochInfoError::InvalidProofOfPossession(v.id));
            }
        }
        let total_stake = validators.iter().map(|v| v.stake).sum();
        Ok(Self {
            validators,
            total_stake,
        })
    }

    /// Returns all validators in this epoch.
    #[must_use]
    pub fn validators(&self) -> &[ValidatorInfo] {
        &self.validators
    }

    /// Gives the validator info for the given validator index.
    ///
    /// # Panics
    ///
    /// Panics if the validator index is out of range.
    #[must_use]
    pub fn validator(&self, id: ValidatorIndex) -> &ValidatorInfo {
        &self.validators[id.as_usize()]
    }

    /// Gives the validator info for the leader for the given slot.
    #[must_use]
    pub fn leader(&self, slot: Slot) -> &ValidatorInfo {
        let window = slot.inner() / SLOTS_PER_WINDOW;
        let leader_id = window % (self.validators.len() as u64);
        self.validator(ValidatorIndex::new(leader_id))
    }

    /// Gives the total stake over all validators.
    #[must_use]
    pub fn total_stake(&self) -> Stake {
        self.total_stake
    }

    /// Returns `true` if `stake` meets the weakest quorum threshold (20%).
    #[must_use]
    pub fn is_weakest_quorum(&self, stake: Stake) -> bool {
        WEAKEST_QUORUM_THRESHOLD.is_met(stake.inner(), self.total_stake().inner())
    }

    /// Returns `true` if `stake` meets the weak quorum threshold (40%).
    #[must_use]
    pub fn is_weak_quorum(&self, stake: Stake) -> bool {
        WEAK_QUORUM_THRESHOLD.is_met(stake.inner(), self.total_stake().inner())
    }

    /// Returns `true` if `stake` meets the standard quorum threshold (60%).
    #[must_use]
    pub fn is_quorum(&self, stake: Stake) -> bool {
        QUORUM_THRESHOLD.is_met(stake.inner(), self.total_stake().inner())
    }

    /// Returns `true` if `stake` meets the strong quorum threshold (80%).
    #[must_use]
    pub fn is_strong_quorum(&self, stake: Stake) -> bool {
        STRONG_QUORUM_THRESHOLD.is_met(stake.inner(), self.total_stake().inner())
    }
}

impl ValidatorEpochInfo {
    /// Creates a per-validator view of the given epoch info.
    ///
    /// # Panics
    ///
    /// Panics if `own_id` is not a valid validator index.
    pub fn new(own_id: ValidatorIndex, epoch: EpochInfo) -> Self {
        assert!(
            own_id.as_usize() < epoch.validators.len(),
            "own_id {own_id} is out of range for {} validators",
            epoch.validators.len()
        );
        Self { own_id, epoch }
    }

    /// Returns our own validator index.
    #[must_use]
    pub fn own_id(&self) -> ValidatorIndex {
        self.own_id
    }

    /// Returns the shared epoch information.
    #[must_use]
    pub fn epoch_info(&self) -> &EpochInfo {
        &self.epoch
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Stake;
    use crate::crypto::aggsig::SecretKey as AggSecretKey;
    use crate::test_utils::generate_validators;

    /// Swapping in a PoP from a different key must be rejected: this is the
    /// trust boundary that gates everything downstream.
    #[test]
    fn rejects_mismatched_pop() {
        let (_, epoch) = generate_validators(2);
        let mut validators = epoch.validators().to_vec();
        // Replace validator 0's PoP with one generated under an unrelated key.
        validators[0].voting_pop = AggSecretKey::new(&mut rand::rng()).sign_pop();
        assert_eq!(
            EpochInfo::try_new(validators).unwrap_err(),
            EpochInfoError::InvalidProofOfPossession(ValidatorIndex::new(0)),
        );
    }

    /// A validator whose `id` disagrees with its index must be rejected too.
    #[test]
    fn rejects_id_index_mismatch() {
        let (_, epoch) = generate_validators(2);
        let mut validators = epoch.validators().to_vec();
        validators[1].id = ValidatorIndex::new(7);
        assert_eq!(
            EpochInfo::try_new(validators).unwrap_err(),
            EpochInfoError::IdIndexMismatch {
                index: 1,
                id: ValidatorIndex::new(7),
            },
        );
    }

    #[test]
    fn quorums() {
        let (_, epoch_info) = generate_validators(6);
        assert!(epoch_info.is_weak_quorum(Stake::new(3)));
        assert!(!epoch_info.is_quorum(Stake::new(3)));
        assert!(epoch_info.is_quorum(Stake::new(4)));
        assert!(!epoch_info.is_strong_quorum(Stake::new(4)));
        assert!(epoch_info.is_strong_quorum(Stake::new(5)));

        let (_, epoch_info) = generate_validators(11);
        assert!(epoch_info.is_weak_quorum(Stake::new(5)));
        assert!(!epoch_info.is_quorum(Stake::new(5)));
        assert!(epoch_info.is_quorum(Stake::new(7)));
        assert!(!epoch_info.is_strong_quorum(Stake::new(7)));
        assert!(epoch_info.is_strong_quorum(Stake::new(9)));
    }
}
