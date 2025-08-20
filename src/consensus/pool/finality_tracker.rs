// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks finality of blocks.
//!
//!

use std::collections::{BTreeMap, BTreeSet};

use crate::BlockId;
use crate::consensus::BlockInfo;
use crate::crypto::Hash;
use crate::types::Slot;

///
#[derive(Default)]
pub struct FinalityTracker {
    parents: BTreeMap<BlockId, BlockId>,
    notarized: BTreeMap<Slot, Hash>,
    finalized: BTreeSet<Slot>,

    highest_finalized: Slot,
}

impl FinalityTracker {
    ///
    pub fn add_parent(
        &mut self,
        slot: Slot,
        block_hash: Hash,
        parent: BlockId,
    ) -> Option<(Slot, BlockInfo)> {
        self.parents.insert((slot, block_hash), parent);
        self.check_finalized(slot)
    }

    ///
    pub fn mark_fast_finalized(
        &mut self,
        slot: Slot,
        block_hash: Hash,
    ) -> Option<(Slot, BlockInfo)> {
        self.notarized.insert(slot, block_hash);
        self.finalized.insert(slot);
        self.check_finalized(slot)
    }

    ///
    pub fn mark_notarized(&mut self, slot: Slot, block_hash: Hash) -> Option<(Slot, BlockInfo)> {
        self.notarized.insert(slot, block_hash);
        self.check_finalized(slot)
    }

    ///
    pub fn mark_finalized(&mut self, slot: Slot) -> Option<(Slot, BlockInfo)> {
        self.finalized.insert(slot);
        self.check_finalized(slot)
    }

    ///
    pub fn highest_finalized(&self) -> Slot {
        self.highest_finalized
    }

    ///
    fn check_finalized(&mut self, slot: Slot) -> Option<(Slot, BlockInfo)> {
        if !self.finalized.contains(&slot) {
            return None;
        }
        self.highest_finalized = slot.max(self.highest_finalized);
        let hash = *self.notarized.get(&slot)?;
        let parent = *self.parents.get(&(slot, hash))?;
        Some((slot, BlockInfo { hash, parent }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut tracker = FinalityTracker::default();
    }
}
