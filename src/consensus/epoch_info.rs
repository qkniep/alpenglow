// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::types::SLOTS_PER_WINDOW;
use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

/// Epoch-specfic validator information.
#[derive(Clone, Debug)]
pub struct EpochInfo {
    own_id: ValidatorId,
    validators: Vec<ValidatorInfo>,
}

impl EpochInfo {
    /// Creates a new `EpochInfo` instance with the given validators.
    pub const fn new(own_id: ValidatorId, validators: Vec<ValidatorInfo>) -> Self {
        Self { own_id, validators }
    }

    /// Returns our own validator ID.
    #[must_use]
    pub fn own_id(&self) -> ValidatorId {
        self.own_id
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
