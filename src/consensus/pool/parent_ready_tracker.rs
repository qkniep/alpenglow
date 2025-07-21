// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks the parent-ready condition.
//!
//! The parent-ready condition pertains to a slot `s` and a block hash `hash(b)`,
//! where `s` is the first slot of a leader window and `s > slot(b)`.
//! Specifically, it is defined as the following:
//!   - Block `b` is notarized or notarized-fallback, and
//!   - slots `slot(b) + 1` (inclusive) to `s` (non-inclusive) are skip-certified.
//!
//! Additional restriction on notarization votes ensure that the parent-ready
//! condition holds for a block `b` only if it also holds for all ancestors of `b`.
//! Together this ensures that the block `b` is a valid parent for block
//! production, i.e., under good network conditions an honest leader proposing
//! a block with parent `b` in slot `s` will have their block finalized.

mod parent_ready_state;

use std::collections::HashMap;

use either::Either;
use smallvec::SmallVec;
use tokio::sync::oneshot;

use crate::{BlockId, Slot};

use parent_ready_state::ParentReadyState;

/// Keeps track of the parent-ready condition across slots.
pub struct ParentReadyTracker(HashMap<Slot, ParentReadyState>);

impl Default for ParentReadyTracker {
    /// Creates a new empty tracker.
    ///
    /// Only the genesis block is considered a valid parent for the first leader window.
    fn default() -> Self {
        let genesis_block = (Slot::new(0), [0; 32]);
        let mut map = HashMap::new();
        let genesis_parent_state = ParentReadyState::new([genesis_block]);
        map.insert(Slot::new(0), genesis_parent_state);
        Self(map)
    }
}

impl ParentReadyTracker {
    /// Marks the given block as notar-fallback.
    ///
    /// Returns a list of any newly connected parents.
    /// All of these will have the given block ID as the parent.
    pub fn mark_notar_fallback(&mut self, id: BlockId) -> Vec<(Slot, BlockId)> {
        let (slot, hash) = id;
        let state = self.0.entry(slot).or_default();
        if state.notar_fallbacks.contains(&hash) {
            return Vec::new();
        }
        state.notar_fallbacks.push(hash);

        // add this block as valid parent to any skip-connected future windows
        let mut newly_certified = Vec::new();
        for s in slot.future_slots() {
            let state = self.0.entry(s).or_default();
            if slot.is_start_of_window() {
                state.add_to_ready(id);
                newly_certified.push((s, id));
            }
            if !state.skip {
                break;
            }
        }

        newly_certified
    }

    /// Marks the given slot as skipped.
    ///
    /// Returns a list of any newly connected parents.
    ///
    /// This should only ever be called once for any specific slot.
    pub fn mark_skipped(&mut self, slot: Slot) -> Vec<(Slot, BlockId)> {
        let state = self.0.entry(slot).or_default();
        state.skip = true;

        // get newly connected future windows
        let mut future_windows = SmallVec::<[Slot; 1]>::new();
        for s in slot.future_slots() {
            if slot.is_start_of_window() {
                future_windows.push(s);
            }
            let state = self.0.entry(s).or_default();
            if !state.skip {
                break;
            }
        }

        // find possible parents for future windows
        let mut potential_parents = SmallVec::<[BlockId; 1]>::new();

        for s in slot
            .slots_in_window()
            .into_iter()
            .filter(|s| *s <= slot)
            .rev()
        {
            let state = self.0.entry(s).or_default();
            if s < slot {
                for nf in &state.notar_fallbacks {
                    potential_parents.push((s, *nf));
                }
            }
            if !state.skip {
                break;
            }

            potential_parents.extend_from_slice(state.ready_block_ids());
        }

        // add these as valid parents to future windows
        let mut newly_certified = Vec::new();
        for first_slot in future_windows {
            let state = self.0.entry(first_slot).or_default();
            for p in potential_parents.iter() {
                state.add_to_ready(*p);
            }
            for parent in &potential_parents {
                newly_certified.push((first_slot, *parent));
            }
        }
        newly_certified
    }

    /// Returns list of all valid parents for the given slot, as of now.
    /// The list can be empty.
    pub fn parents_ready(&self, slot: Slot) -> &[BlockId] {
        self.0
            .get(&slot)
            .map_or(&[], |state| state.ready_block_ids())
    }

    /// If the slot has a parent ready, then returns it right away or else
    /// blocks till a parent ready.
    pub fn wait_for_parent_ready(
        &mut self,
        slot: Slot,
    ) -> Either<BlockId, oneshot::Receiver<BlockId>> {
        let state = self.0.entry(slot).or_default();
        state.wait_for_parent_ready()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut tracker = ParentReadyTracker::default();
        for i in 0..2 * SLOTS_PER_WINDOW {
            let next_window_slot = (i / SLOTS_PER_WINDOW + 1) * SLOTS_PER_WINDOW;
            let block = (i, [i as u8 + 1; 32]);
            let new_valid_parents = tracker.mark_notar_fallback(block);
            if i % SLOTS_PER_WINDOW == SLOTS_PER_WINDOW - 1 {
                assert!(new_valid_parents.contains(&(next_window_slot, block)));
            } else {
                assert!(new_valid_parents.is_empty());
            }
        }
    }

    #[test]
    fn genesis() {
        let mut tracker = ParentReadyTracker::default();
        assert!(tracker.mark_skipped(0).is_empty());
        assert!(tracker.mark_skipped(1).is_empty());
        assert!(tracker.mark_skipped(2).is_empty());
        let new_valid_parents = tracker.mark_skipped(3);
        assert!(new_valid_parents.contains(&(4, (0, [0; 32]))));
    }

    #[test]
    fn skips() {
        let mut tracker = ParentReadyTracker::default();
        let block = (0, [1; 32]);
        assert!(tracker.mark_notar_fallback(block).is_empty());
        assert!(tracker.mark_skipped(0).is_empty());
        assert!(tracker.mark_skipped(1).is_empty());
        assert!(tracker.mark_skipped(2).is_empty());
        let new_valid_parents = tracker.mark_skipped(3);
        assert!(new_valid_parents.contains(&(4, block)));
        assert!(new_valid_parents.contains(&(4, (0, [0; 32]))));
    }

    #[test]
    fn out_of_order_skips() {
        let mut tracker = ParentReadyTracker::default();
        let block = (0, [1; 32]);
        assert!(tracker.mark_skipped(3).is_empty());
        assert!(tracker.mark_skipped(1).is_empty());
        assert!(tracker.mark_skipped(2).is_empty());
        assert_eq!(tracker.mark_notar_fallback(block), vec![(4, block)]);
        assert_eq!(tracker.mark_skipped(0), vec![(4, (0, [0; 32]))]);
    }

    #[test]
    fn out_of_order_notars() {
        let mut tracker = ParentReadyTracker::default();
        let block0 = (0, [1; 32]);
        let block1 = (1, [2; 32]);
        let block2 = (2, [3; 32]);
        let block3 = (3, [4; 32]);
        assert!(tracker.mark_notar_fallback(block2).is_empty());
        assert_eq!(tracker.mark_notar_fallback(block3), vec![(4, block3)]);
        assert!(tracker.mark_notar_fallback(block0).is_empty());
        assert!(tracker.mark_notar_fallback(block1).is_empty());
    }

    #[test]
    fn no_double_counting() {
        let mut tracker = ParentReadyTracker::default();
        let block = (0, [1; 32]);
        assert!(tracker.mark_notar_fallback(block).is_empty());
        assert!(tracker.mark_skipped(1).is_empty());
        assert!(tracker.mark_skipped(2).is_empty());
        assert_eq!(tracker.mark_skipped(3), vec![(4, block)]);
        assert!(tracker.mark_skipped(4).is_empty());
        assert!(tracker.mark_skipped(5).is_empty());
        assert!(tracker.mark_skipped(6).is_empty());
        assert_eq!(tracker.mark_skipped(7), vec![(8, block)]);
    }
}
