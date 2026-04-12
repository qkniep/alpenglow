// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::ops::Deref;

use crate::types::SLOTS_PER_WINDOW;
use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

/// Shared epoch information, identical across all validators.
///
/// Contains the validator set and derived data for one epoch.
/// Constructed once per epoch and shared via [`Arc`].
#[derive(Clone, Debug)]
pub struct EpochInfo {
    pub(crate) validators: Vec<ValidatorInfo>,
    total_stake: Stake,
}

/// Per-validator epoch information, wrapping shared [`EpochInfo`].
///
/// Adds the node's own identity on top of the shared epoch data.
#[derive(Clone, Debug)]
pub struct ValidatorEpochInfo {
    pub(crate) own_id: ValidatorId,
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
                v.id == i as u64,
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
}

impl ValidatorEpochInfo {
    /// Creates a per-validator view of the given epoch info.
    ///
    /// # Panics
    ///
    /// Panics if `own_id` is not a valid validator index.
    pub fn new(own_id: ValidatorId, epoch: EpochInfo) -> Self {
        assert!(
            (own_id as usize) < epoch.validators.len(),
            "own_id {own_id} is out of range for {} validators",
            epoch.validators.len()
        );
        Self { own_id, epoch }
    }
}

impl Deref for ValidatorEpochInfo {
    type Target = EpochInfo;

    fn deref(&self) -> &EpochInfo {
        &self.epoch
    }
}
