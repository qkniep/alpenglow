// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::{Slot, Stake, ValidatorId, ValidatorInfo};

use super::SLOTS_PER_WINDOW;

///
#[derive(Clone, Debug)]
pub struct EpochInfo {
    pub(crate) validators: Vec<ValidatorInfo>,
}

impl EpochInfo {
    ///
    pub fn new(validators: Vec<ValidatorInfo>) -> Self {
        Self { validators }
    }

    ///
    pub fn validator(&self, id: ValidatorId) -> &ValidatorInfo {
        &self.validators[id as usize]
    }

    ///
    pub fn leader(&self, slot: Slot) -> &ValidatorInfo {
        let window = slot / SLOTS_PER_WINDOW;
        let leader_id = window % (self.validators.len() as u64);
        self.validator(leader_id)
    }

    ///
    pub fn total_stake(&self) -> Stake {
        self.validators.iter().map(|v| v.stake).sum()
    }
}
