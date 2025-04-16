// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks if a condition holds for a block and all of its ancestors.
//!
//! This can be used for any kind of chain validity property.
//! Currently, in [`Alpenglow`] this is only used for tracking branch-certified.
//!
//! [`Alpenglow`]: crate::consensus::Alpenglow

use std::collections::HashMap;

use crate::crypto::Hash;

type BlockId = (u64, Hash);

/// Tracks a chain validity property for all blocks.
pub struct ValidToRootTracker(HashMap<BlockId, ValidToRootState>);

/// Holds chain validity state for a single block.
#[derive(Clone, Default)]
struct ValidToRootState {
    valid_to_root: bool,
    valid: bool,
    parent: Option<BlockId>,
    waiting_children: Vec<BlockId>,
}

impl ValidToRootTracker {
    /// Creates a new empty tracker.
    ///
    /// Only the genesis block is considered valid-to-root.
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    /// Creates a tracker with the specified root block marked as valid-to-root.
    pub fn new_with_root(root: BlockId) -> Self {
        let mut tracker = Self::new();
        tracker.0.insert(root, ValidToRootState::new_root());
        tracker
    }

    /// Adds a block with the specified parent.
    ///
    /// If it already has a known parent, nothing happens.
    /// If it was already marked valid, it is stored as waiting for the parent.
    ///
    /// Also, checks this block, and potentially its ancestors, to see if they
    /// are now valid-to-root. Returns a list of blocks that are now valid-to-root.
    pub fn add_with_parent(&mut self, id: BlockId, parent: BlockId) -> Vec<BlockId> {
        let state = self.0.entry(id).or_default();
        if state.parent.is_some() {
            return Vec::new();
        }
        let is_valid = state.valid;
        state.parent = Some(parent);
        let newly_certified = self.check_valid_to_root(id);

        // if block was already valid, we need to wait for parent
        if is_valid && newly_certified.is_empty() {
            let parent_state = self.0.entry(parent).or_default();
            parent_state.waiting_children.push(id);
        }

        newly_certified
    }

    /// Marks the given block as locally fulfilling the validity condition.
    ///
    /// If it was already marked valid, nothing happens.
    /// If it already has a known parent, it is stored as waiting for the parent.
    ///
    /// Also, checks this block, and potentially its ancestors, to see if they
    /// are now valid-to-root. Returns a list of blocks that are now valid-to-root.
    pub fn mark_valid(&mut self, id: BlockId) -> Vec<BlockId> {
        let state = self.0.entry(id).or_default();
        if state.valid {
            return Vec::new();
        }
        let parent = state.parent;
        state.valid = true;
        let newly_certified = self.check_valid_to_root(id);

        // if parent was already known, we need to wait for parent
        if parent.is_some() && newly_certified.is_empty() {
            let parent_state = self.0.entry(parent.unwrap()).or_default();
            parent_state.waiting_children.push(id);
        }

        newly_certified
    }

    /// Returns `true` iff the given block is valid-to-root.
    ///
    /// That is, it is locally valid, and all of its ancestors are valid-to-root.
    pub fn is_valid_to_root(&self, id: BlockId) -> bool {
        match self.0.get(&id) {
            Some(state) => state.valid_to_root,
            None => false,
        }
    }

    /// Checks if the given block is now valid-to-root.
    ///
    /// If the block newly becomes valid-to-root, any waiting children are also checked.
    ///
    /// Returns a list of blocks that are now valid-to-root.
    ///
    /// # Panics
    ///
    /// - Panics if the given block is not registered in the tracker.
    /// - Panics if the block is already marked valid-to-root.
    fn check_valid_to_root(&mut self, id: BlockId) -> Vec<BlockId> {
        let mut newly_certified = Vec::new();
        let state = self.0.get(&id).unwrap();
        assert!(!state.valid_to_root);
        let is_valid = state.valid;
        let parent_state = state.parent.and_then(|p| self.0.get(&p));
        let parent_valid_to_root = parent_state.is_some_and(|s| s.valid_to_root);

        // if block becomes valid-to-root, check waiting children
        if is_valid && (state.parent == Some((0, [0; 32])) || parent_valid_to_root) {
            let state = self.0.get_mut(&id).unwrap();
            state.valid_to_root = true;
            newly_certified.push(id);
            let children: Vec<_> = state.waiting_children.drain(..).collect();
            for child in children {
                self.check_valid_to_root_recursive(child, &mut newly_certified);
            }
        }

        newly_certified
    }

    /// Recursively checks if the given block is now valid-to-root.
    ///
    /// Compared to [`Self::check_valid_to_root`], this does not check the parent.
    /// Instead, it is assumed that the parent is already valid-to-root.
    /// If the block newly becomes valid-to-root, any waiting children are also checked.
    ///
    /// Adds any blocks that are now valid-to-root to `newly_certified`.
    ///
    /// # Panics
    ///
    /// - Panics if the given block is not registered in the tracker.
    /// - Panics if the block is already marked valid-to-root.
    fn check_valid_to_root_recursive(&mut self, id: BlockId, newly_certified: &mut Vec<BlockId>) {
        let state = self.0.get_mut(&id).unwrap();
        assert!(!state.valid_to_root);
        if state.valid {
            state.valid_to_root = true;
            newly_certified.push(id);
            let children: Vec<_> = state.waiting_children.drain(..).collect();
            for child in children {
                self.check_valid_to_root_recursive(child, newly_certified);
            }
        }
    }
}

impl ValidToRootState {
    fn new() -> Self {
        Self::default()
    }

    fn new_root() -> Self {
        ValidToRootState {
            valid_to_root: true,
            valid: true,
            parent: None,
            waiting_children: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_genesis() {
        let mut tracker = ValidToRootTracker::new();
        let genesis = (0, [0; 32]);
        let block0 = (0, [42; 32]);
        let block1 = (1, [1; 32]);
        let block2 = (2, [2; 32]);
        let block3 = (3, [3; 32]);
        tracker.add_with_parent(block0, genesis);
        tracker.add_with_parent(block1, block0);
        tracker.add_with_parent(block2, block1);
        tracker.add_with_parent(block3, block2);
        tracker.mark_valid(block0);
        assert!(tracker.is_valid_to_root(block0));
        tracker.mark_valid(block1);
        assert!(tracker.is_valid_to_root(block1));
        tracker.mark_valid(block2);
        assert!(tracker.is_valid_to_root(block2));
        tracker.mark_valid(block3);
        assert!(tracker.is_valid_to_root(block3));
    }

    #[test]
    fn receive_blocks_first() {
        let mut tracker = ValidToRootTracker::new_with_root((3, [3; 32]));
        let window_blocks = [(4, [4; 32]), (5, [5; 32]), (6, [6; 32]), (7, [7; 32])];
        let parents = [(3, [3; 32]), (4, [4; 32]), (5, [5; 32]), (6, [6; 32])];
        for (i, block) in window_blocks.iter().copied().enumerate() {
            assert_eq!(tracker.add_with_parent(block, parents[i]), vec![]);
        }
        for block in window_blocks {
            assert!(!tracker.is_valid_to_root(block));
        }
        for block in window_blocks {
            assert_eq!(tracker.mark_valid(block), vec![block]);
        }
        for block in window_blocks {
            assert!(tracker.is_valid_to_root(block));
        }
    }

    #[test]
    fn see_notarization_first() {
        let mut tracker = ValidToRootTracker::new_with_root((3, [3; 32]));
        let window_blocks = [(4, [4; 32]), (5, [5; 32]), (6, [6; 32]), (7, [7; 32])];
        let parents = [(3, [3; 32]), (4, [4; 32]), (5, [5; 32]), (6, [6; 32])];
        for block in window_blocks {
            assert_eq!(tracker.mark_valid(block), vec![]);
        }
        for block in window_blocks {
            assert!(!tracker.is_valid_to_root(block));
        }
        for (i, block) in window_blocks.iter().copied().enumerate() {
            assert_eq!(tracker.add_with_parent(block, parents[i]), vec![block]);
        }
        for block in window_blocks {
            assert!(tracker.is_valid_to_root(block));
        }
    }

    #[test]
    fn recursive_blocks_first() {
        let mut tracker = ValidToRootTracker::new_with_root((3, [3; 32]));
        let window_blocks = [(4, [4; 32]), (5, [5; 32]), (6, [6; 32]), (7, [7; 32])];
        let parents = [(3, [3; 32]), (4, [4; 32]), (5, [5; 32]), (6, [6; 32])];
        for (i, block) in window_blocks.iter().copied().enumerate() {
            assert_eq!(tracker.add_with_parent(block, parents[i]), vec![]);
        }
        for block in window_blocks {
            assert!(!tracker.is_valid_to_root(block));
        }
        for block in window_blocks[1..].iter().copied() {
            assert_eq!(tracker.mark_valid(block), vec![]);
        }
        assert_eq!(tracker.mark_valid(window_blocks[0]), window_blocks.to_vec());
        for block in window_blocks {
            assert!(tracker.is_valid_to_root(block));
        }
    }

    #[test]
    fn recurisve_notarization_first() {
        let mut tracker = ValidToRootTracker::new_with_root((3, [3; 32]));
        let window_blocks = [(4, [4; 32]), (5, [5; 32]), (6, [6; 32]), (7, [7; 32])];
        let parents = [(3, [3; 32]), (4, [4; 32]), (5, [5; 32]), (6, [6; 32])];
        for block in window_blocks {
            assert_eq!(tracker.mark_valid(block), vec![]);
        }
        for block in window_blocks {
            assert!(!tracker.is_valid_to_root(block));
        }
        for (i, block) in window_blocks.iter().copied().enumerate().skip(1) {
            assert_eq!(tracker.add_with_parent(block, parents[i]), vec![]);
        }
        assert_eq!(
            tracker.add_with_parent(window_blocks[0], parents[0]),
            window_blocks.to_vec()
        );
        for block in window_blocks {
            assert!(tracker.is_valid_to_root(block));
        }
    }

    #[test]
    fn skips() {
        let mut tracker = ValidToRootTracker::new_with_root((3, [3; 32]));
        assert_eq!(tracker.add_with_parent((4, [4; 32]), (3, [3; 32])), vec![]);
        assert_eq!(tracker.mark_valid((4, [4; 32])), vec![(4, [4; 32])]);
        let window_blocks = [(8, [8; 32]), (9, [9; 32]), (10, [10; 32]), (11, [11; 32])];
        let parents = [(4, [4; 32]), (8, [8; 32]), (9, [9; 32]), (10, [10; 32])];
        for (i, block) in window_blocks.iter().copied().enumerate() {
            assert_eq!(tracker.add_with_parent(block, parents[i]), vec![]);
        }
        for block in window_blocks {
            assert!(!tracker.is_valid_to_root(block));
        }
        for block in window_blocks[1..].iter().copied() {
            assert_eq!(tracker.mark_valid(block), vec![]);
        }
        assert_eq!(tracker.mark_valid(window_blocks[0]), window_blocks.to_vec());
        for block in window_blocks {
            assert!(tracker.is_valid_to_root(block));
        }
    }

    #[test]
    fn out_of_order() {
        let block3 = (3, [3; 32]);
        let mut tracker = ValidToRootTracker::new_with_root(block3);
        let block4 = (4, [4; 32]);
        let block5 = (5, [5; 32]);
        let block6 = (6, [6; 32]);
        let block7 = (7, [7; 32]);
        assert_eq!(tracker.mark_valid(block5), vec![]);
        assert_eq!(tracker.mark_valid(block4), vec![]);
        assert_eq!(tracker.mark_valid(block6), vec![]);
        assert_eq!(tracker.add_with_parent(block6, block5), vec![]);
        assert_eq!(tracker.add_with_parent(block7, block6), vec![]);
        assert_eq!(tracker.add_with_parent(block5, block4), vec![]);

        // registering block 3 as parent of block 4 triggers chain-reaction
        // of blocks 4, 5 and 6 being marked as valid-to-root
        assert_eq!(
            tracker.add_with_parent(block4, block3),
            vec![block4, block5, block6]
        );

        // block 7 only becomes valid-to-root after being marked as valid
        assert_eq!(tracker.mark_valid(block7), vec![block7]);
    }

    #[test]
    fn out_of_order_2() {
        let block3 = (3, [3; 32]);
        let mut tracker = ValidToRootTracker::new_with_root(block3);
        let block4 = (4, [4; 32]);
        let block5 = (5, [5; 32]);
        let block6 = (6, [6; 32]);
        let block7 = (7, [7; 32]);
        assert_eq!(tracker.add_with_parent(block5, block4), vec![]);
        assert_eq!(tracker.add_with_parent(block4, block3), vec![]);
        assert_eq!(tracker.add_with_parent(block6, block5), vec![]);
        assert_eq!(tracker.mark_valid(block6), vec![]);
        assert_eq!(tracker.mark_valid(block7), vec![]);
        assert_eq!(tracker.mark_valid(block5), vec![]);

        // marking block 4 as valid triggers chain-reaction of blocks 4, 5 and 6
        // being marked as valid-to-root
        assert_eq!(tracker.mark_valid(block4), vec![block4, block5, block6]);

        // block 7 only becomes valid-to-root after registering block 6 as its parent
        assert_eq!(tracker.add_with_parent(block7, block6), vec![block7]);
    }
}
