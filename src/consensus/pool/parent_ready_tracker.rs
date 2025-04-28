// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks if a condition holds for a block and all of its ancestors.
//!
//! This can be used for any kind of chain validity property.
//! Currently, in [`Alpenglow`] this is only used for tracking branch-certified.
//!
//! [`Alpenglow`]: crate::consensus::Alpenglow

use std::collections::HashMap;

use smallvec::SmallVec;

use crate::{Slot, consensus::SLOTS_PER_WINDOW, crypto::Hash};

type BlockId = (u64, Hash);

/// Tracks
pub struct ParentReadyTracker(HashMap<Slot, ParentReadyState>);

/// Holds ... state for a single block.
#[derive(Clone, Default)]
struct ParentReadyState {
    skip: bool,
    // we can potentially have multiple notar fallbacks per slot,
    // but we optimize the common case where there will only be one
    notar_fallbacks: SmallVec<[Hash; 1]>,
    // we can potentiall have multiple parents ready per slot,
    // but we optimize the common case where there will only be one
    parents_ready: SmallVec<[BlockId; 1]>,
}

impl ParentReadyTracker {
    /// Creates a new empty tracker.
    ///
    /// Only the genesis block is considered a ready parent.
    pub fn new() -> Self {
        let genesis = (0, [0; 32]);
        let mut map = HashMap::new();
        map.insert(
            0,
            ParentReadyState {
                skip: false,
                notar_fallbacks: SmallVec::new(),
                parents_ready: [genesis].into(),
            },
        );
        Self(map)
    }

    /// Marks the given block as notar-fallback.
    ///
    /// This should only ever be called once for every block ID.
    pub fn mark_notar_fallback(&mut self, id: BlockId) -> Vec<(Slot, BlockId)> {
        let (slot, hash) = id;
        let state = self.0.entry(slot).or_default();
        if state.notar_fallbacks.contains(&hash) {
            return Vec::new();
        }
        state.notar_fallbacks.push(hash);

        // add this block as valid parent to any skip-connected future windows
        let mut newly_certified = Vec::new();
        for s in slot + 1.. {
            let state = self.0.entry(s).or_default();
            if s % SLOTS_PER_WINDOW == 0 {
                state.parents_ready = [id].into();
                newly_certified.push((s, id));
            }
            if !state.skip {
                break;
            }
        }
        newly_certified
    }

    /// Marka the given slot as skipped.
    ///
    /// This should only ever be called once for every slot.
    pub fn mark_skipped(&mut self, slot: Slot) -> Vec<(Slot, BlockId)> {
        let state = self.0.entry(slot).or_default();
        state.skip = true;

        // get newly connected future windows
        let mut future_windows = SmallVec::<[Slot; 1]>::new();
        for s in slot + 1.. {
            if s % SLOTS_PER_WINDOW == 0 {
                future_windows.push(s);
            }
            let state = self.0.entry(s).or_default();
            if !state.skip {
                break;
            }
        }

        // find possible parents for future windows
        let mut potential_parents = SmallVec::<[BlockId; 1]>::new();
        for s in (0..=slot).rev() {
            let state = self.0.entry(s).or_default();
            if s < slot {
                for nf in &state.notar_fallbacks {
                    potential_parents.push((s, *nf));
                }
            }
            if !state.skip {
                break;
            }
            for parent in &state.parents_ready {
                potential_parents.push(*parent);
            }
        }

        // add these as valid parents to future windows
        let mut newly_certified = Vec::new();
        for first_slot in future_windows {
            let state = self.0.entry(first_slot).or_default();
            state.parents_ready.extend_from_slice(&potential_parents);
            for parent in &potential_parents {
                newly_certified.push((first_slot, *parent));
            }
        }
        newly_certified
    }

    ///
    pub fn parents_ready(&self, slot: Slot) -> &[BlockId] {
        self.0
            .get(&slot)
            .map(|state| state.parents_ready.as_slice())
            .unwrap_or(&[])
    }
}

impl ParentReadyState {
    fn new() -> Self {
        Self::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut tracker = ParentReadyTracker::new();
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
    fn skips() {
        let mut tracker = ParentReadyTracker::new();
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
    fn out_of_order() {
        let mut tracker = ParentReadyTracker::new();
        let block = (0, [1; 32]);
        assert!(tracker.mark_skipped(3).is_empty());
        assert!(tracker.mark_skipped(1).is_empty());
        assert!(tracker.mark_skipped(2).is_empty());
        assert_eq!(tracker.mark_notar_fallback(block), vec![(4, block)]);
        assert_eq!(tracker.mark_skipped(0), vec![(4, (0, [0; 32]))]);
    }
}
