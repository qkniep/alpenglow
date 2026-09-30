// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks finality of blocks.
//!
//! This is used internally as part of [`PoolImpl`].
//!
//! Keeps track of:
//! - Direct finalization of blocks,
//! - resulting indirect finalizations of ancestor blocks, and
//! - resulting implicit skipping of earlier slots
//!
//! It does this based on:
//! - direct finalization of blocks, as determined by [`PoolImpl`] from its certificates, and
//! - availability of blocks and knowledge of their parents.
//!
//! Each slot's [`Decision`] is written at most once and never changes afterwards.
//! So every slot is reported in at most one [`FinalizationEvent`].
//!
//! [`PoolImpl`]: crate::consensus::pool::PoolImpl

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use crate::BlockId;
use crate::crypto::merkle::{BlockHash, GENESIS_BLOCK_HASH};
use crate::types::Slot;

/// Tracks finality of blocks.
pub(super) struct FinalityTracker {
    /// Decision for each decided slot, see [`Self::decide`].
    decided: BTreeMap<Slot, Decision>,
    /// Maps blocks to their parents.
    parents: BTreeMap<BlockId, BlockId>,
    /// The highest finalized slot so far.
    ///
    /// This means that slot has a fast finalization *or* finalization + notarization.
    highest_finalized_slot: Slot,
    /// The lowest slot whose state has not yet been pruned.
    ///
    /// Everything below this is a contiguous prefix of decided
    /// (finalized or implicitly skipped) slots that has been dropped.
    /// This can lag behind [`Self::highest_finalized_slot`]
    /// (e.g. a slot may be finalized before the parent-chain is fully resolved).
    first_unpruned_slot: Slot,
}

/// Final decision about a slot, which never changes once made.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Decision {
    /// Block with the given hash is finalized, directly or implicitly.
    Finalized(BlockHash),
    /// Slot was implicitly skipped through later finalization.
    Skipped,
}

/// Information about newly finalized slots.
///
/// Each slot is reported in at most one event.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct FinalizationEvent {
    /// Directly finalized block, if any.
    pub(super) finalized: Option<BlockId>,
    /// Any implicitly finalized blocks.
    pub(super) implicitly_finalized: Vec<BlockId>,
    /// Any implicitly skipped slots.
    pub(super) implicitly_skipped: Vec<Slot>,
}

impl Default for FinalityTracker {
    /// Creates a new empty tracker.
    ///
    /// Initially, only the genesis block is considered (directly) finalized.
    fn default() -> Self {
        let mut decided = BTreeMap::new();
        decided.insert(Slot::genesis(), Decision::Finalized(GENESIS_BLOCK_HASH));
        Self {
            decided,
            parents: BTreeMap::new(),
            highest_finalized_slot: Slot::genesis(),
            first_unpruned_slot: Slot::genesis(),
        }
    }
}

impl FinalityTracker {
    /// Adds the given `parent` for the given `block`.
    ///
    /// Handles possibly resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    pub(super) fn add_parent(&mut self, block: BlockId, parent: BlockId) -> FinalizationEvent {
        assert!(block.0 > parent.0);
        // NOTE: This can genuinely happen if we see a finalization before the block.
        if block.0 < self.first_unpruned_slot {
            return FinalizationEvent::default();
        }
        match self.parents.entry(block.clone()) {
            Entry::Occupied(e) => {
                assert!(e.get() == &parent);
                return FinalizationEvent::default();
            }
            Entry::Vacant(e) => {
                e.insert(parent.clone());
            }
        }

        let mut event = FinalizationEvent::default();
        let (slot, block_hash) = block;
        if self.decided.get(&slot) == Some(&Decision::Finalized(block_hash)) {
            self.handle_implicitly_finalized(slot, parent, &mut event);
            self.prune();
        }
        event
    }

    /// Marks the given block as directly finalized.
    ///
    /// A block is directly finalized by a fast-finalization certificate, or by a
    /// finalization certificate together with its notarization certificate.
    /// If the block was newly finalized, handles resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    ///
    /// # Panics
    ///
    /// Panics if the slot was already decided differently (consensus safety violation).
    pub(super) fn mark_finalized(&mut self, block: BlockId) -> FinalizationEvent {
        let (slot, block_hash) = &block;
        debug_assert!(*slot >= self.first_unpruned_slot);
        let mut event = FinalizationEvent::default();
        if *slot < self.first_unpruned_slot
            || !self.decide(*slot, Decision::Finalized(block_hash.clone()))
        {
            return event;
        }

        event.finalized = Some(block.clone());
        self.highest_finalized_slot = self.highest_finalized_slot.max(*slot);
        if let Some(parent) = self.parents.get(&block).cloned() {
            self.handle_implicitly_finalized(*slot, parent, &mut event);
        }
        self.prune();
        event
    }

    /// Returns the highest finalized slot.
    ///
    /// This means that slot has a fast finalization *or* finalization + notarization.
    /// Note that some slots before this may still be undecided
    /// (e.g. because of unresolved parent relations).
    pub(super) fn highest_finalized_slot(&self) -> Slot {
        self.highest_finalized_slot
    }

    /// Returns the first slot whose state has not yet been pruned.
    ///
    /// All slots below this are decided and no longer tracked,
    /// so certificates and votes for them can be safely ignored.
    pub(super) fn first_unpruned_slot(&self) -> Slot {
        self.first_unpruned_slot
    }

    /// Returns `true` iff the given slot was implicitly skipped (and not yet pruned).
    pub(super) fn is_skipped(&self, slot: Slot) -> bool {
        self.decided.get(&slot) == Some(&Decision::Skipped)
    }

    /// Records `decision` for `slot`.
    ///
    /// Returns `true` iff the slot was not decided before.
    /// Repeating the same decision is a no-op returning `false`.
    ///
    /// # Panics
    ///
    /// Panics if the slot was already decided differently (consensus safety violation).
    fn decide(&mut self, slot: Slot, decision: Decision) -> bool {
        match self.decided.entry(slot) {
            Entry::Vacant(e) => {
                e.insert(decision);
                true
            }
            Entry::Occupied(e) => {
                assert_eq!(e.get(), &decision, "consensus safety violation");
                false
            }
        }
    }

    /// Handles the indirect finalization of the given block.
    ///
    /// Recurses through ancestors, potentially implicitly finalizing them as well.
    ///
    /// Updates the `event` all along the way with:
    /// - Any potentially implicitly finalized blocks, and
    /// - any implicitly skipped slots.
    fn handle_implicitly_finalized(
        &mut self,
        source_slot: Slot,
        implicitly_finalized: BlockId,
        event: &mut FinalizationEvent,
    ) {
        assert!(source_slot > implicitly_finalized.0);
        // parent slot may already be decided and pruned;
        // consider a call to `add_parent` for the `first_unpruned_slot`
        if implicitly_finalized.0 < self.first_unpruned_slot {
            return;
        }

        // implicitly skip slots in between
        for slot in implicitly_finalized.0.future_slots() {
            if slot == source_slot {
                break;
            }
            // already skipped, so this ancestry was already handled
            if !self.decide(slot, Decision::Skipped) {
                return;
            }
            event.implicitly_skipped.push(slot);
        }

        // mark block as implicitly finalized, unless it already is
        let (slot, block_hash) = &implicitly_finalized;
        if !self.decide(*slot, Decision::Finalized(block_hash.clone())) {
            return;
        }
        event
            .implicitly_finalized
            .push(implicitly_finalized.clone());

        // recurse through ancestors
        if let Some(parent) = self.parents.get(&implicitly_finalized).cloned() {
            self.handle_implicitly_finalized(implicitly_finalized.0, parent, event);
        }
    }

    /// Clears all state that is no longer needed.
    ///
    /// Advances [`Self::first_unpruned_slot`] to the end of the prefix of decided slots.
    /// Then, drops all state corresponding to (decided) slots before it.
    fn prune(&mut self) {
        let mut next = self.first_unpruned_slot.next();
        while self.decided.contains_key(&next) {
            self.first_unpruned_slot = next;
            next = next.next();
        }
        let root = self.first_unpruned_slot;
        self.decided = self.decided.split_off(&root);
        self.parents.retain(|(slot, _), _| *slot >= root);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::{genesis_block_id, random_block_id};

    #[test]
    fn basic() {
        let mut tracker = FinalityTracker::default();

        // finalize a block
        let (slot1, hash1) = random_block_id(Slot::genesis().next());
        let event = tracker.mark_finalized((slot1, hash1.clone()));
        assert_eq!(event.finalized, Some((slot1, hash1)));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // finalize another block
        let (slot2, hash2) = random_block_id(slot1.next());
        let event = tracker.mark_finalized((slot2, hash2.clone()));
        assert_eq!(event.finalized, Some((slot2, hash2)));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITHOUT skips
        let (slot3, hash3) = random_block_id(slot2.next());
        let (slot4, hash4) = random_block_id(slot3.next());
        let event = tracker.add_parent((slot4, hash4.clone()), (slot3, hash3.clone()));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_finalized((slot4, hash4.clone()));
        assert_eq!(event.finalized, Some((slot4, hash4)));
        assert_eq!(event.implicitly_finalized, vec![(slot3, hash3)]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITH skips
        let (slot7, hash7) = random_block_id(slot4.next().next().next());
        let (slot5, hash5) = random_block_id(slot7.prev().prev());
        let event = tracker.add_parent((slot7, hash7.clone()), (slot5, hash5.clone()));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_finalized((slot7, hash7.clone()));
        assert_eq!(event.finalized, Some((slot7, hash7)));
        assert_eq!(event.implicitly_finalized, vec![(slot5, hash5)]);
        assert_eq!(event.implicitly_skipped, vec![slot7.prev()]);
    }

    #[test]
    fn no_duplicates() {
        let mut tracker = FinalityTracker::default();

        // finalizing a block again is a no-op
        let (slot1, hash1) = random_block_id(Slot::genesis().next());
        let event = tracker.mark_finalized((slot1, hash1.clone()));
        assert_eq!(event.finalized, Some((slot1, hash1.clone())));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);
        let event = tracker.mark_finalized((slot1, hash1.clone()));
        assert_eq!(event, FinalizationEvent::default());

        // do NOT implicitly finalize parent, that is already directly finalized
        let (slot2, hash2) = random_block_id(slot1.next());
        let event = tracker.add_parent((slot2, hash2.clone()), (slot2.prev(), hash1));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_finalized((slot2, hash2.clone()));
        assert_eq!(event.finalized, Some((slot2, hash2)));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITHOUT skips
        let (slot4, hash4) = random_block_id(slot2.next().next());
        let (slot3, hash3) = random_block_id(slot4.prev());
        let event = tracker.add_parent((slot4, hash4.clone()), (slot3, hash3.clone()));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_finalized((slot4, hash4.clone()));
        assert_eq!(event.finalized, Some((slot4, hash4.clone())));
        assert_eq!(event.implicitly_finalized, vec![(slot3, hash3.clone())]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // do NOT implicitly finalize parent again when adding parent again
        let event = tracker.add_parent((slot4, hash4), (slot3, hash3));
        assert_eq!(event, FinalizationEvent::default());
    }

    #[test]
    #[should_panic(expected = "consensus safety violation")]
    fn conflicting_finalization_panics() {
        let mut tracker = FinalityTracker::default();
        let (slot1, hash1) = random_block_id(Slot::genesis().next());
        tracker.mark_finalized((slot1, hash1));
        let (_, other_hash) = random_block_id(slot1);
        tracker.mark_finalized((slot1, other_hash));
    }

    #[test]
    #[should_panic(expected = "consensus safety violation")]
    fn finalizing_skipped_slot_panics() {
        let mut tracker = FinalityTracker::default();
        let block2 = random_block_id(Slot::new(2));
        let block4 = random_block_id(Slot::new(4));
        // finalizing slot 4 with parent in slot 2 implicitly skips slot 3,
        // slot 1 stays undecided so slot 3 is not pruned
        tracker.add_parent(block4.clone(), block2);
        let event = tracker.mark_finalized(block4);
        assert_eq!(event.implicitly_skipped, vec![Slot::new(3)]);
        assert_eq!(tracker.first_unpruned_slot(), Slot::genesis());
        tracker.mark_finalized(random_block_id(Slot::new(3)));
    }

    #[test]
    fn prune() {
        let mut tracker = FinalityTracker::default();

        // connect (with parent relation) a chain of blocks
        let mut chain = vec![genesis_block_id()];
        for s in 1..=6u64 {
            let block = random_block_id(Slot::new(s));
            tracker.add_parent(block.clone(), chain[chain.len() - 1].clone());
            chain.push(block);
        }

        // finalize slot 5, implicitly finalizing its ancestors
        let root = Slot::new(5);
        tracker.mark_finalized(chain[5].clone());
        // this moves the watermark to slot 5
        assert_eq!(tracker.first_unpruned_slot(), root);

        // only slots at or above the watermark remain
        assert!(tracker.decided.keys().all(|s| *s >= root));
        assert!(tracker.parents.keys().all(|(s, _)| *s >= root));
        assert!(tracker.decided.contains_key(&root));
        assert!(!tracker.decided.contains_key(&Slot::new(4)));
    }

    #[test]
    fn prune_keeps_unresolved_gap() {
        let mut tracker = FinalityTracker::default();
        let (slot1, hash1) = random_block_id(Slot::genesis().next());
        let (slot2, hash2) = random_block_id(slot1.next());

        // slot 2 is finalized while slot 1 is still undecided
        let event = tracker.mark_finalized((slot2, hash2.clone()));
        assert_eq!(event.finalized, Some((slot2, hash2)));
        // cannot prune slot 1 yet
        // we can't have emitted a `FinalizationEvent` for it yet
        assert_eq!(tracker.highest_finalized_slot(), slot2);
        assert_eq!(tracker.first_unpruned_slot(), Slot::genesis());
        assert!(!tracker.decided.contains_key(&slot1));

        // can catch up once continuous chain is fully finalized
        tracker.add_parent((slot1, hash1.clone()), genesis_block_id());
        let event = tracker.mark_finalized((slot1, hash1.clone()));
        assert_eq!(event.finalized, Some((slot1, hash1)));
        assert_eq!(tracker.first_unpruned_slot(), slot2);
    }

    #[test]
    fn ignores_add_parent_below_watermark() {
        let mut tracker = FinalityTracker::default();

        // build and finalize a chain up to slot 5 to advance the watermark
        let mut prev = genesis_block_id();
        for s in 1..=5u64 {
            let block = random_block_id(Slot::new(s));
            tracker.add_parent(block.clone(), prev.clone());
            prev = block;
        }
        tracker.mark_finalized(prev);
        assert_eq!(tracker.first_unpruned_slot(), Slot::new(5));

        // a late block for an already-pruned slot is ignored, leaving no trace
        let stale = random_block_id(Slot::new(2));
        let block1 = random_block_id(Slot::new(1));
        let event = tracker.add_parent(stale.clone(), block1);
        assert_eq!(event, FinalizationEvent::default());
        assert!(!tracker.parents.contains_key(&stale));
    }

    #[test]
    fn no_reemit_when_parent_pruned_late() {
        let mut tracker = FinalityTracker::default();
        let (slot0, hash0) = genesis_block_id();
        let (slot1, hash1) = random_block_id(slot0.next());
        let (slot2, hash2) = random_block_id(slot1.next());

        // finalize slot 1 (with its parent chain)
        tracker.add_parent((slot1, hash1.clone()), (slot0, hash0));
        let event = tracker.mark_finalized((slot1, hash1.clone()));
        assert_eq!(event.finalized, Some((slot1, hash1.clone())));
        // genesis is already decided, so it is not reported again
        assert_eq!(event.implicitly_finalized, vec![]);
        // keeps the watermark at slot 1
        assert_eq!(tracker.first_unpruned_slot(), slot1);

        // finalize slot 2 before its parent edge is known
        let event = tracker.mark_finalized((slot2, hash2.clone()));
        assert_eq!(event.finalized, Some((slot2, hash2.clone())));
        // this prunes slot 1
        assert_eq!(tracker.first_unpruned_slot(), slot2);

        // late parent edge must NOT re-finalize (already-pruned) slot 1
        let event = tracker.add_parent((slot2, hash2), (slot1, hash1));
        assert_eq!(event, FinalizationEvent::default());
    }
}
