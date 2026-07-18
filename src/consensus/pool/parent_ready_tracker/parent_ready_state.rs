// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implements the [`ParentReadyState`] data structure.
//!
//! It holds the necessary state for a given slot to track the parent-ready condition.
//! This is used by the [`super::ParentReadyTracker`].

use smallvec::SmallVec;

use crate::BlockId;
use crate::crypto::merkle::{BlockHash, GENESIS_BLOCK_HASH};

/// Holds the relevant state for a single slot.
#[derive(Default)]
pub(super) struct ParentReadyState {
    /// Whether this slot is skip-certified.
    skip: bool,
    /// Blocks that are notarized-fallback for this slot, if any.
    ///
    /// We can potentially have multiple notar fallbacks per slot,
    /// but we optimize for the common case where there will only be one.
    notar_fallbacks: SmallVec<[BlockHash; 1]>,
    /// Parents ready for this slot.
    ///
    /// We can potentially have multiple parents ready per slot, but we
    /// optimize for the common case where there will only be one.
    ready: SmallVec<[BlockId; 1]>,
}

impl ParentReadyState {
    /// Creates a new [`ParentReadyState`] for the genesis block.
    pub(super) fn genesis() -> Self {
        Self {
            skip: false,
            notar_fallbacks: SmallVec::from([GENESIS_BLOCK_HASH]),
            ready: SmallVec::new(),
        }
    }

    /// Marks this slot as skip-certified.
    ///
    /// Returns `true` iff this slot was not already skip-certified.
    pub(super) fn mark_skip(&mut self) -> bool {
        if self.skip {
            false
        } else {
            self.skip = true;
            true
        }
    }

    /// Returns `true` iff this slot is skip-certified.
    pub(super) fn is_skip_certified(&self) -> bool {
        self.skip
    }

    /// Marks the given block as notarized-fallback.
    ///
    /// Returns `true` iff this block was not already marked as notarized-fallback.
    pub(super) fn mark_notar_fallback(&mut self, hash: BlockHash) -> bool {
        if self.notar_fallbacks.contains(&hash) {
            false
        } else {
            self.notar_fallbacks.push(hash);
            true
        }
    }

    /// Returns an iterator over the notarized-fallback block hashes for this slot.
    pub(super) fn notar_fallback_blocks(&self) -> impl Iterator<Item = BlockHash> {
        self.notar_fallbacks.iter().cloned()
    }

    /// Adds a [`BlockId`] to the parents ready list.
    ///
    /// # Panics
    ///
    /// If the specific parent is already marked ready for this slot.
    pub(super) fn add_to_ready(&mut self, id: BlockId) {
        assert!(!self.ready.contains(&id));
        self.ready.push(id);
    }

    /// Returns the list of currently valid parents for this slot.
    pub(super) fn ready_block_ids(&self) -> &[BlockId] {
        &self.ready
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Slot;
    use crate::test_utils::random_block_id;

    #[test]
    fn ready_parents_are_tracked() {
        let mut state = ParentReadyState::default();
        assert_eq!(state.ready_block_ids().len(), 0);
        let block_id = random_block_id(Slot::new(1));
        state.add_to_ready(block_id.clone());
        assert_eq!(state.ready_block_ids(), &[block_id]);
    }
}
