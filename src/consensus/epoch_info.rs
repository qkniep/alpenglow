// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::consensus::{
    QUORUM_THRESHOLD, STRONG_QUORUM_THRESHOLD, WEAK_QUORUM_THRESHOLD, WEAKEST_QUORUM_THRESHOLD,
};
use crate::types::SLOTS_PER_WINDOW;
use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

/// Epoch-specific validator information.
#[derive(Clone, Debug)]
pub struct EpochInfo {
    pub(crate) own_id: ValidatorId,
    pub(crate) validators: Vec<ValidatorInfo>,
    total_stake: Stake,
}

impl EpochInfo {
    /// Creates a new `EpochInfo` instance with the given validators.
    pub fn new(own_id: ValidatorId, validators: Vec<ValidatorInfo>) -> Self {
        let total_stake = validators.iter().map(|v| v.stake).sum();
        Self {
            own_id,
            validators,
            total_stake,
        }
    }

    /// Gives the validator info for the given validator ID.
    ///
    /// # Panics
    ///
    /// Panics if the validator ID is out of range.
    #[must_use]
    pub fn validator(&self, id: ValidatorId) -> &ValidatorInfo {
        &self.validators[id as usize]
    }

    /// Gives the validator info for the leader for the given slot.
    #[must_use]
    pub fn leader(&self, slot: Slot) -> &ValidatorInfo {
        let window = slot.inner() / SLOTS_PER_WINDOW;
        let leader_id = window % (self.validators.len() as u64);
        self.validator(leader_id)
    }

    /// Gives the total stake over all validators.
    #[must_use]
    pub fn total_stake(&self) -> Stake {
        self.total_stake
    }

    /// Returns `true` if `stake` meets the weakest quorum threshold (20%).
    #[must_use]
    pub fn is_weakest_quorum(&self, stake: Stake) -> bool {
        WEAKEST_QUORUM_THRESHOLD.is_met(stake, self.total_stake())
    }

    /// Returns `true` if `stake` meets the weak quorum threshold (40%).
    #[must_use]
    pub fn is_weak_quorum(&self, stake: Stake) -> bool {
        WEAK_QUORUM_THRESHOLD.is_met(stake, self.total_stake())
    }

    /// Returns `true` if `stake` meets the standard quorum threshold (60%).
    #[must_use]
    pub fn is_quorum(&self, stake: Stake) -> bool {
        QUORUM_THRESHOLD.is_met(stake, self.total_stake())
    }

    /// Returns `true` if `stake` meets the strong quorum threshold (80%).
    #[must_use]
    pub fn is_strong_quorum(&self, stake: Stake) -> bool {
        STRONG_QUORUM_THRESHOLD.is_met(stake, self.total_stake())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::generate_validators;

    #[test]
    fn quorums() {
        let (_, epoch_info) = generate_validators(6);
        assert!(epoch_info.is_weak_quorum(3));
        assert!(!epoch_info.is_quorum(3));
        assert!(epoch_info.is_quorum(4));
        assert!(!epoch_info.is_strong_quorum(4));
        assert!(epoch_info.is_strong_quorum(5));

        let (_, epoch_info) = generate_validators(11);
        assert!(epoch_info.is_weak_quorum(5));
        assert!(!epoch_info.is_quorum(5));
        assert!(epoch_info.is_quorum(7));
        assert!(!epoch_info.is_strong_quorum(7));
        assert!(epoch_info.is_strong_quorum(9));
    }
}
