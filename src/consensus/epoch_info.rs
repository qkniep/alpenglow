// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::consensus::{
    QUORUM_THRESHOLD, STRONG_QUORUM_THRESHOLD, WEAK_QUORUM_THRESHOLD, WEAKEST_QUORUM_THRESHOLD,
};
use crate::types::SLOTS_PER_WINDOW;
use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

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
    own_id: ValidatorId,
    epoch: EpochInfo,
}

impl EpochInfo {
    /// Creates a new `EpochInfo` from the given validator set.
    ///
    /// # Panics
    ///
    /// Panics if any validator's `id` does not match its index in the vector.
    pub fn new(validators: Vec<ValidatorInfo>) -> Self {
        for (i, v) in validators.iter().enumerate() {
            assert!(
                v.id.as_index() == i,
                "validator at index {i} has id {}, expected {i}",
                v.id
            );
        }
        let total_stake = validators.iter().map(|v| v.stake).sum();
        Self {
            validators,
            total_stake,
        }
    }

    /// Returns all validators in this epoch.
    #[must_use]
    pub fn validators(&self) -> &[ValidatorInfo] {
        &self.validators
    }

    /// Gives the validator info for the given validator ID.
    ///
    /// # Panics
    ///
    /// Panics if the validator ID is out of range.
    #[must_use]
    pub fn validator(&self, id: ValidatorId) -> &ValidatorInfo {
        &self.validators[id.as_index()]
    }

    /// Gives the validator info for the leader for the given slot.
    #[must_use]
    pub fn leader(&self, slot: Slot) -> &ValidatorInfo {
        let window = slot.inner() / SLOTS_PER_WINDOW;
        let leader_id = window % (self.validators.len() as u64);
        self.validator(ValidatorId::new(leader_id))
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
    pub fn new(own_id: ValidatorId, epoch: EpochInfo) -> Self {
        assert!(
            own_id.as_index() < epoch.validators.len(),
            "own_id {own_id} is out of range for {} validators",
            epoch.validators.len()
        );
        Self { own_id, epoch }
    }

    /// Returns our own validator ID.
    #[must_use]
    pub fn own_id(&self) -> ValidatorId {
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
    use crate::Stake;
    use crate::test_utils::generate_validators;

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
