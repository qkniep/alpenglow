// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks the parent-ready condition.
//!
//! The parent-ready condition pertains to a slot `s` and a block hash `hash(b)`,
//! where `s` is the first slot of a leader window and `s > slot(b)`.
//! Specifically, it is defined as the following:
//!   - Block `b` is notarized or notarized-fallback, AND
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

use crate::crypto::Hash;
use crate::{BlockId, Slot};

use parent_ready_state::ParentReadyState;

/// Keeps track of the parent-ready condition across slots.
pub struct ParentReadyTracker(HashMap<Slot, ParentReadyState>);

impl Default for ParentReadyTracker {
    /// Creates a new empty tracker.
    ///
    /// Only the genesis block is considered a valid parent for the first leader window.
    fn default() -> Self {
        let genesis_block = (Slot::genesis(), Hash::default());
        let mut map = HashMap::new();
        let mut genesis_parent_state = ParentReadyState::new([genesis_block]);
        genesis_parent_state.skip = true;
        map.insert(Slot::genesis(), genesis_parent_state);
        Self(map)
    }
}

impl ParentReadyTracker {
    /// Considers the given slot as finalized with the provided parent.
    ///
    /// This implies that (and is treated exactly the same as if):
    /// 1. The parent of the finalized block is notarized-fallback, AND
    /// 2. all slots between the parent and the finalized block are skip-certified.
    ///
    /// Returns a list of any newly connected parents.
    pub fn mark_finalized(&mut self, slot: Slot, parent: BlockId) -> Vec<(Slot, BlockId)> {
        let mut parents_ready = Vec::new();
        parents_ready.extend(self.mark_notar_fallback(parent));
        for s in parent.0.future_slots() {
            if s == slot {
                break;
            }
            parents_ready.extend(self.mark_skipped(s));
        }
        parents_ready
    }

    /// Marks the given block as notarized-fallback.
    ///
    /// Returns a list of any newly connected parents.
    /// All of these will have the given block ID as the parent.
    pub fn mark_notar_fallback(&mut self, id: BlockId) -> Vec<(Slot, BlockId)> {
        let (slot, hash) = id;
        let state = self.slot_state(slot);
        if state.notar_fallbacks.contains(&hash) {
            return Vec::new();
        }
        state.notar_fallbacks.push(hash);

        // add this block as valid parent to any skip-connected future windows
        let mut newly_certified = Vec::new();
        for slot in slot.future_slots() {
            let state = self.slot_state(slot);
            if slot.is_start_of_window() {
                state.add_to_ready(id);
                newly_certified.push((slot, id));
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
    pub fn mark_skipped(&mut self, slot: Slot) -> Vec<(Slot, BlockId)> {
        let state = self.slot_state(slot);
        if state.skip {
            return Vec::new();
        }
        state.skip = true;

        // get newly connected future windows
        let mut future_windows = SmallVec::<[Slot; 1]>::new();
        for slot in slot.future_slots() {
            if slot.is_start_of_window() {
                future_windows.push(slot);
            }
            if !self.slot_state(slot).skip {
                break;
            }
        }

        // find possible parents for future windows
        let mut potential_parents = SmallVec::<[BlockId; 1]>::new();

        for s in slot.slots_in_window().filter(|s| *s <= slot).rev() {
            let state = self.slot_state(s);
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
            let state = self.slot_state(first_slot);
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
    ///
    /// The list can be empty if there are no valid parents yet.
    pub fn parents_ready(&self, slot: Slot) -> &[BlockId] {
        self.0
            .get(&slot)
            .map_or(&[], |state| state.ready_block_ids())
    }

    /// Returns a ready parent if available, otherwise returns a oneshot channel.
    ///
    /// The oneshot channel will receive the first ready parent once it becomes available.
    pub fn wait_for_parent_ready(
        &mut self,
        slot: Slot,
    ) -> Either<BlockId, oneshot::Receiver<BlockId>> {
        let state = self.0.entry(slot).or_default();
        state.wait_for_parent_ready()
    }

    /// Mutably accesses the [`ParentReadyState`] for the given `slot`.
    ///
    /// Initializes the state with [`Default`] if necessary.
    fn slot_state(&mut self, slot: Slot) -> &mut ParentReadyState {
        self.0.entry(slot).or_default()
    }
}

#[cfg(test)]
mod tests {
    use crate::types::SLOTS_PER_WINDOW;

    use super::*;

    #[test]
    fn basic() {
        let mut tracker = ParentReadyTracker::default();

        for s in Slot::genesis()
            .future_slots()
            .take(2 * SLOTS_PER_WINDOW as usize)
        {
            let block = (s, [s.inner() as u8; 32]);
            let new_valid_parents = tracker.mark_notar_fallback(block);
            if s == s.last_slot_in_window() {
                assert!(new_valid_parents.contains(&(s.next(), block)));
            } else {
                assert!(new_valid_parents.is_empty());
            }
        }
    }

    #[test]
    fn genesis() {
        let genesis = (Slot::genesis(), Hash::default());
        let mut tracker = ParentReadyTracker::default();
        for slot in genesis.0.slots_in_window() {
            let new_valid_parents = tracker.mark_skipped(slot);
            if slot == slot.last_slot_in_window() {
                assert!(new_valid_parents.contains(&(slot.next(), genesis)));
            } else {
                assert!(new_valid_parents.is_empty());
            }
        }
    }

    #[test]
    fn skips() {
        let genesis = (Slot::genesis(), Hash::default());
        let slot = Slot::genesis().next();
        let block = (slot, [1; 32]);
        let mut tracker = ParentReadyTracker::default();
        assert!(tracker.mark_notar_fallback(block).is_empty());
        for s in slot.slots_in_window() {
            let new_valid_parents = tracker.mark_skipped(s);
            if s == s.last_slot_in_window() {
                assert!(new_valid_parents.contains(&(s.next(), block)));
                assert!(new_valid_parents.contains(&(s.next(), genesis)));
            } else {
                assert!(new_valid_parents.is_empty());
            }
        }
    }

    #[test]
    fn out_of_order_skips() {
        let genesis = (Slot::genesis(), Hash::default());
        let slot = Slot::genesis().next();
        let block = (slot, [1; 32]);
        let mut tracker = ParentReadyTracker::default();
        assert_eq!(slot.slots_in_window().count(), 4);
        assert!(tracker.mark_skipped(Slot::new(3)).is_empty());
        assert!(tracker.mark_skipped(Slot::new(2)).is_empty());
        assert_eq!(
            tracker.mark_notar_fallback(block),
            vec![(Slot::new(4), block)]
        );
        assert_eq!(tracker.mark_skipped(slot), vec![(Slot::new(4), genesis)]);
    }

    #[test]
    fn out_of_order_notars() {
        assert_eq!(Slot::genesis().slots_in_window().count(), 4);
        let block1 = (Slot::new(1), [1; 32]);
        let block2 = (Slot::new(2), [2; 32]);
        let block3 = (Slot::new(3), [3; 32]);
        let mut tracker = ParentReadyTracker::default();
        assert!(tracker.mark_notar_fallback(block2).is_empty());
        assert_eq!(
            tracker.mark_notar_fallback(block3),
            vec![(Slot::new(4), block3)]
        );
        assert!(tracker.mark_notar_fallback(block1).is_empty());
    }

    #[test]
    fn no_double_counting() {
        assert_eq!(Slot::genesis().slots_in_window().count(), 4);
        let slot = Slot::genesis().next();
        let block = (slot, [1; 32]);
        let mut tracker = ParentReadyTracker::default();
        assert!(tracker.mark_notar_fallback(block).is_empty());
        assert!(tracker.mark_skipped(Slot::new(2)).is_empty());
        assert_eq!(
            tracker.mark_skipped(Slot::new(3)),
            vec![(Slot::new(4), block)]
        );
        assert!(tracker.mark_skipped(Slot::new(4)).is_empty());
        assert!(tracker.mark_skipped(Slot::new(5)).is_empty());
        assert!(tracker.mark_skipped(Slot::new(6)).is_empty());
        assert_eq!(
            tracker.mark_skipped(Slot::new(7)),
            vec![(Slot::new(8), block)]
        );
    }

    #[test]
    fn wait_for_parent_ready() {
        let mut windows = Slot::windows();
        let window1 = windows.next().unwrap();
        let window2 = windows.next().unwrap();
        let window3 = windows.next().unwrap();
        let mut tracker = ParentReadyTracker::default();

        // skip slots in first window
        for slot in window1.slots_in_window() {
            if slot.is_genesis() {
                continue;
            }
            tracker.mark_skipped(slot);
        }

        // genesis should be valid parent for 2nd window
        let res = tracker.wait_for_parent_ready(window2);
        let Either::Left((slot, hash)) = res else {
            panic!("unexpected result {res:?}");
        };
        assert_eq!(slot, Slot::genesis());
        assert_eq!(hash, Hash::default());

        // parent should not yet be ready
        let res = tracker.wait_for_parent_ready(window3);
        let Either::Right(mut rx) = res else {
            panic!("unexpected result {res:?}");
        };
        let Err(oneshot::error::TryRecvError::Empty) = rx.try_recv() else {
            panic!("parent should not yet be ready");
        };

        // skip slots in first window
        for slot in window2.slots_in_window() {
            tracker.mark_skipped(slot);
        }

        // now we should be notified of genesis as valid parent
        assert_eq!(rx.try_recv(), Ok((Slot::genesis(), Hash::default())));
    }

    #[test]
    fn parent_ready_finalized() {
        let mut windows = Slot::windows();
        let window2 = windows.nth(1).unwrap();
        let window3 = windows.nth(2).unwrap();
        let window4 = windows.nth(3).unwrap();
        let window5 = windows.nth(4).unwrap();
        let mut tracker = ParentReadyTracker::default();

        // basic case where finalized slot is first in its window
        let slot = window2.first_slot_in_window();
        let parent = (slot.prev(), [1; 32]);
        let parents = tracker.mark_finalized(slot, parent);
        assert_eq!(parents.len(), 1);
        let parent_ready = parents[0];
        assert_eq!(parent_ready.0, slot);
        assert_eq!(parent_ready.1, parent);

        // case where an entire window is skipped between parent and finalized block
        let slot = window4.first_slot_in_window();
        let parent = (window3.first_slot_in_window().prev(), [2; 32]);
        let parents = tracker.mark_finalized(slot, parent);
        assert_eq!(parents.len(), 1);
        let parent_ready = parents[0];
        assert_eq!(parent_ready.0, slot);
        assert_eq!(parent_ready.1, parent);

        // case where finalized slot is NOT first in its window
        let slot = window5.first_slot_in_window().next();
        let parent = (slot.prev(), [3; 32]);
        let parents = tracker.mark_finalized(slot, parent);
        assert_eq!(parents.len(), 1);
        let parent_ready = parents[0];
        // assert_eq!(parent_ready.0, slot);
        // assert_eq!(parent_ready.1, parent);
    }
}
