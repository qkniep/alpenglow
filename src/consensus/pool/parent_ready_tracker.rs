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

use self::parent_ready_state::ParentReadyState;
use crate::consensus::pool::finality_tracker::FinalizationEvent;
use crate::{BlockId, Slot};

/// Keeps track of the parent-ready condition across slots.
pub struct ParentReadyTracker(HashMap<Slot, ParentReadyState>);

impl ParentReadyTracker {
    /// Marks the given block as notarized-fallback.
    ///
    /// Returns a list of any newly connected parents.
    /// All of these will have the given block ID as the parent.
    pub fn mark_notar_fallback(&mut self, id: &BlockId) -> SmallVec<[(Slot, BlockId); 1]> {
        let (slot, hash) = id.clone();
        let state = self.slot_state(slot);
        if !state.mark_notar_fallback(hash) {
            return SmallVec::new();
        }

        // add this block as valid parent to any skip-connected future windows
        let mut newly_certified = SmallVec::new();
        for slot in slot.future_slots() {
            let state = self.slot_state(slot);
            if slot.is_start_of_window() {
                state.add_to_ready(id.clone());
                newly_certified.push((slot, id.clone()));
            }
            if !state.is_skip_certified() {
                break;
            }
        }
        newly_certified
    }

    /// Marks the given slot as skipped.
    ///
    /// Returns a list of any newly connected parents.
    pub fn mark_skipped(&mut self, marked_slot: Slot) -> SmallVec<[(Slot, BlockId); 1]> {
        let state = self.slot_state(marked_slot);
        if !state.mark_skip() {
            return SmallVec::new();
        }

        // find possible parents for future windows
        let mut potential_parents = SmallVec::<[BlockId; 1]>::new();
        let window_slots = marked_slot.slots_in_window();
        // going back from `marked_slot` find any skip-connected parents
        for slot in window_slots.filter(|s| *s <= marked_slot).rev() {
            let state = self.slot_state(slot);
            // add any notarized-fallback blocks from this slot
            if slot != marked_slot {
                for nf in state.notar_fallback_blocks() {
                    potential_parents.push((slot, nf));
                }
            }
            // stop as soon as we see any non-skipped slot
            if !state.is_skip_certified() {
                break;
            }
            // if the slot is skipped, add its parents as well
            potential_parents.extend(state.ready_block_ids().iter().cloned());
        }

        // add these as valid parents to any skip-connected future windows
        let mut newly_certified = SmallVec::new();
        for slot in marked_slot.future_slots() {
            let state = self.slot_state(slot);
            // add parents to this window
            if slot.is_start_of_window() {
                for parent in &potential_parents {
                    state.add_to_ready(parent.clone());
                    newly_certified.push((slot, parent.clone()));
                }
            }
            // stop as soon as we see any non-skipped slot
            if !state.is_skip_certified() {
                break;
            }
        }
        newly_certified
    }

    /// Handles the given finalization event.
    ///
    /// Marks blocks as notarized-fallback and slots as skipped as appropriate.
    ///
    /// Returns at most one newly ready parent (for the highest slot).
    /// For consistency with other functions it still returns a `Vec`.
    pub fn handle_finalization(
        &mut self,
        event: FinalizationEvent,
    ) -> SmallVec<[(Slot, BlockId); 1]> {
        let mut parents_ready = SmallVec::<[(Slot, BlockId); 1]>::new();
        if let Some(finalized) = &event.finalized {
            parents_ready.extend(self.mark_notar_fallback(finalized));
        }
        for block_id in &event.implicitly_finalized {
            parents_ready.extend(self.mark_notar_fallback(block_id));
        }
        for slot in event.implicitly_skipped {
            parents_ready.extend(self.mark_skipped(slot));
        }

        // keep only highest slot ParentReady
        let maybe_parent = parents_ready.iter().max_by_key(|(slot, _)| slot);
        maybe_parent.into_iter().cloned().collect()
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

impl Default for ParentReadyTracker {
    /// Creates a new empty tracker.
    ///
    /// Initially, only the genesis block is considered notarized-fallback.
    fn default() -> Self {
        let mut map = HashMap::new();
        let genesis_parent_state = ParentReadyState::genesis();
        map.insert(Slot::genesis(), genesis_parent_state);
        Self(map)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::Hash;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::types::SLOTS_PER_WINDOW;

    #[test]
    fn basic() {
        let mut tracker = ParentReadyTracker::default();

        for s in Slot::genesis()
            .future_slots()
            .take(2 * SLOTS_PER_WINDOW as usize)
        {
            let block = (s, Hash::random_for_test().into());
            let new_valid_parents = tracker.mark_notar_fallback(&block);
            if s == s.last_slot_in_window() {
                assert!(new_valid_parents.contains(&(s.next(), block)));
            } else {
                assert!(new_valid_parents.is_empty());
            }
        }
    }

    #[test]
    fn genesis() {
        let genesis = (Slot::genesis(), GENESIS_BLOCK_HASH);
        let mut tracker = ParentReadyTracker::default();
        for slot in genesis.0.slots_in_window() {
            let new_valid_parents = tracker.mark_skipped(slot);
            if slot == slot.last_slot_in_window() {
                assert!(new_valid_parents.contains(&(slot.next(), genesis.clone())));
            } else {
                assert!(new_valid_parents.is_empty());
            }
        }
    }

    #[test]
    fn skips() {
        let genesis = (Slot::genesis(), GENESIS_BLOCK_HASH);
        let slot = Slot::genesis().next();
        let block = (slot, Hash::random_for_test().into());
        let mut tracker = ParentReadyTracker::default();
        assert!(tracker.mark_notar_fallback(&block).is_empty());
        for s in slot.slots_in_window() {
            let new_valid_parents = tracker.mark_skipped(s);
            if s == s.last_slot_in_window() {
                assert!(new_valid_parents.contains(&(s.next(), block.clone())));
                assert!(new_valid_parents.contains(&(s.next(), genesis.clone())));
            } else {
                assert!(new_valid_parents.is_empty());
            }
        }
    }

    #[test]
    fn out_of_order_skips() {
        let genesis = (Slot::genesis(), GENESIS_BLOCK_HASH);
        let slot = Slot::genesis().next();
        let block = (slot, Hash::random_for_test().into());
        let mut tracker = ParentReadyTracker::default();
        assert_eq!(slot.slots_in_window().count(), 4);
        assert!(tracker.mark_skipped(Slot::new(3)).is_empty());
        assert!(tracker.mark_skipped(Slot::new(2)).is_empty());
        assert_eq!(
            tracker.mark_notar_fallback(&block).to_vec(),
            vec![(Slot::new(4), block)]
        );
        assert_eq!(
            tracker.mark_skipped(slot).to_vec(),
            vec![(Slot::new(4), genesis)]
        );
    }

    #[test]
    fn out_of_order_notars() {
        assert_eq!(Slot::genesis().slots_in_window().count(), 4);
        let block1 = (Slot::new(1), Hash::random_for_test().into());
        let block2 = (Slot::new(2), Hash::random_for_test().into());
        let block3 = (Slot::new(3), Hash::random_for_test().into());
        let mut tracker = ParentReadyTracker::default();
        assert!(tracker.mark_notar_fallback(&block2).is_empty());
        assert_eq!(
            tracker.mark_notar_fallback(&block3).to_vec(),
            vec![(Slot::new(4), block3)]
        );
        assert!(tracker.mark_notar_fallback(&block1).is_empty());
    }

    #[test]
    fn no_double_counting_skip_chain() {
        assert_eq!(Slot::genesis().slots_in_window().count(), 4);
        let slot = Slot::genesis().next();
        let block = (slot, Hash::random_for_test().into());
        let mut tracker = ParentReadyTracker::default();
        assert!(tracker.mark_notar_fallback(&block).is_empty());
        assert!(tracker.mark_skipped(Slot::new(2)).is_empty());
        assert_eq!(
            tracker.mark_skipped(Slot::new(3)).to_vec(),
            vec![(Slot::new(4), block.clone())]
        );
        assert!(tracker.mark_skipped(Slot::new(4)).is_empty());
        assert!(tracker.mark_skipped(Slot::new(5)).is_empty());
        assert!(tracker.mark_skipped(Slot::new(6)).is_empty());
        assert_eq!(
            tracker.mark_skipped(Slot::new(7)).to_vec(),
            vec![(Slot::new(8), block)]
        );
    }

    #[test]
    fn no_double_counting_notar_and_skip() {
        assert_eq!(Slot::genesis().slots_in_window().count(), 4);
        let slot = Slot::genesis().next();
        let block = (slot, Hash::random_for_test().into());
        let mut tracker = ParentReadyTracker::default();
        assert!(tracker.mark_notar_fallback(&block).is_empty());
        assert!(tracker.mark_skipped(Slot::new(2)).is_empty());
        assert_eq!(
            tracker.mark_skipped(Slot::new(3)).to_vec(),
            vec![(Slot::new(4), block)]
        );
        // notably this does not re-issue a ParentReady for `block`
        assert_eq!(
            tracker.mark_skipped(Slot::new(1)).to_vec(),
            vec![(Slot::new(4), (Slot::genesis(), GENESIS_BLOCK_HASH))]
        );
    }

    #[test]
    fn wait_for_parent_ready() {
        let genesis = (Slot::genesis(), GENESIS_BLOCK_HASH);
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
        assert_eq!((slot, hash), genesis);

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
        assert_eq!(rx.try_recv(), Ok(genesis));
    }

    #[test]
    fn parent_ready_finalized() {
        let mut windows = Slot::windows();
        let window2 = windows.nth(1).unwrap();
        let window3 = windows.next().unwrap();
        let window4 = windows.next().unwrap();
        let window5 = windows.next().unwrap();
        let mut tracker = ParentReadyTracker::default();

        // basic case where finalized slot is first in its window
        let block = (
            window2.first_slot_in_window(),
            Hash::random_for_test().into(),
        );
        let parent = (block.0.prev(), Hash::random_for_test().into());
        let event = FinalizationEvent {
            finalized: Some(block.clone()),
            implicitly_finalized: vec![parent.clone()],
            implicitly_skipped: vec![],
        };
        let parents = tracker.handle_finalization(event);
        assert_eq!(parents.len(), 1);
        let parent_ready = &parents[0];
        assert_eq!(parent_ready.0, block.0);
        assert_eq!(parent_ready.1, parent);

        // case where an entire window is skipped between parent and finalized block
        let block = (
            window4.first_slot_in_window(),
            Hash::random_for_test().into(),
        );
        let parent = (
            window3.first_slot_in_window().prev(),
            Hash::random_for_test().into(),
        );
        let event = FinalizationEvent {
            finalized: Some(block.clone()),
            implicitly_finalized: vec![parent.clone()],
            implicitly_skipped: window3.slots_in_window().collect(),
        };
        let parents = tracker.handle_finalization(event);
        assert_eq!(parents.len(), 1);
        let parent_ready = &parents[0];
        assert_eq!(parent_ready.0, block.0);
        assert_eq!(parent_ready.1, parent);

        // case where finalized slot is NOT first in its window
        let block = (
            window5.first_slot_in_window().next(),
            Hash::random_for_test().into(),
        );
        let parent = (block.0.prev(), Hash::random_for_test().into());
        let parent_parent = (parent.0.prev(), Hash::random_for_test().into());
        let event = FinalizationEvent {
            finalized: Some(block.clone()),
            implicitly_finalized: vec![parent.clone(), parent_parent.clone()],
            implicitly_skipped: vec![],
        };
        let parents = tracker.handle_finalization(event);
        assert_eq!(parents.len(), 1);
        let parent_ready = &parents[0];
        assert_eq!(parent_ready.0, parent.0);
        assert_eq!(parent_ready.1, parent_parent);
    }
}
