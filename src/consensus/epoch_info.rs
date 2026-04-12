// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::types::SLOTS_PER_WINDOW;
use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

/// Epoch-specific validator information.
#[derive(Clone, Debug)]
pub struct EpochInfo {
    pub(crate) own_id: ValidatorId,
    pub(crate) validators: Vec<ValidatorInfo>,
}

impl EpochInfo {
    /// Creates a new `EpochInfo` instance with the given validators.
    ///
    /// # Panics
    ///
    /// Panics if `own_id` is not a valid index into `validators`,
    /// or if any validator's `id` does not match its position in the vector.
    pub fn new(own_id: ValidatorId, validators: Vec<ValidatorInfo>) -> Self {
        assert!(
            (own_id as usize) < validators.len(),
            "own_id {own_id} is out of range for {} validators",
            validators.len()
        );
        for (i, v) in validators.iter().enumerate() {
            assert!(
                v.id == i as u64,
                "validator at index {i} has id {}, expected {i}",
                v.id
            );
        }
        Self { own_id, validators }
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
        self.validators.iter().map(|v| v.stake).sum()
    }
}
