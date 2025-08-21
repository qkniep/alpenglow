// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks finality of blocks.
//!
//! This is used as part of [`PoolImpl`].
//!
//! Keeps track of:
//! - Direct finalization of blocks,
//! - resulting indirect finalizations of blocks, AND
//! - resulting implicit skipping of slots
//!
//! It does this based on:
//! - Notarization of blocks,
//! - finalization of slots, AND
//! - availability of blocks and knowledge of their parents.
//!
//! [`PoolImpl`]: crate::consensus::pool::PoolImpl

use std::collections::BTreeMap;

use crate::BlockId;
use crate::crypto::Hash;
use crate::types::Slot;

/// Tracks finality of blocks.
#[derive(Default)]
pub struct FinalityTracker {
    /// Current finalization status for each slot.
    status: BTreeMap<Slot, FinalizationStatus>,
    /// Maps blocks to their parents.
    parents: BTreeMap<BlockId, BlockId>,
    /// The highest finalized slot so far.
    highest_finalized: Slot,
}

/// Possible states a slot can be in regarding finality.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizationStatus {
    Notarized(Hash),
    Finalized,
    FinalizedAndNotarized(Hash),
    ImplicitlyFinalized(Hash),
    ImplicitlySkipped,
}

/// Information about newly finalized slots.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FinalizationEvent {
    /// Directly finalized block, if any.
    pub(super) finalized: Option<BlockId>,
    /// Any implicitly finalized blocks.
    pub(super) implicitly_finalized: Vec<BlockId>,
    /// Any implicitly skipped slots.
    pub(super) implicitly_skipped: Vec<Slot>,
}

impl FinalityTracker {
    /// Adds the given `parent` for the given `block`.
    ///
    /// Handles possibly resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    pub fn add_parent(&mut self, block: BlockId, parent: BlockId) -> FinalizationEvent {
        assert!(block.0 > parent.0);
        if let Some(p) = self.parents.get(&block) {
            assert!(p == &parent);
            return FinalizationEvent::default();
        }
        self.parents.insert(block, parent);

        let (slot, block_hash) = block;
        let Some(status) = self.status.get(&slot) else {
            return FinalizationEvent::default();
        };
        match status {
            FinalizationStatus::FinalizedAndNotarized(hash)
            | FinalizationStatus::ImplicitlyFinalized(hash) => {
                let mut event = FinalizationEvent::default();
                if &block_hash == hash {
                    self.handle_implicitly_finalized(block.0, parent, &mut event);
                }
                event
            }
            FinalizationStatus::Notarized(_)
            | FinalizationStatus::Finalized
            | FinalizationStatus::ImplicitlySkipped => FinalizationEvent::default(),
        }
    }

    /// Marks the given block as fast finalized.
    ///
    /// If the block was newly finalized, handles resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    pub fn mark_fast_finalized(&mut self, slot: Slot, block_hash: Hash) -> FinalizationEvent {
        if let Some(status) = self.status.get(&slot) {
            match status {
                FinalizationStatus::FinalizedAndNotarized(_) => {
                    return FinalizationEvent::default();
                }
                FinalizationStatus::Notarized(_)
                | FinalizationStatus::Finalized
                | FinalizationStatus::ImplicitlyFinalized(_) => {}
                FinalizationStatus::ImplicitlySkipped => unreachable!("consensus safety violation"),
            }
        }

        let mut event = FinalizationEvent::default();
        self.status
            .insert(slot, FinalizationStatus::FinalizedAndNotarized(block_hash));
        self.handle_finalized((slot, block_hash), &mut event);
        self.highest_finalized = slot.max(self.highest_finalized);
        event
    }

    /// Marks the given block as notarized.
    ///
    /// Handles possibly resulting direct finalization of the block.
    /// Further, also handles any possibly resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    pub fn mark_notarized(&mut self, slot: Slot, block_hash: Hash) -> FinalizationEvent {
        if let Some(status) = self.status.get(&slot) {
            match status {
                FinalizationStatus::Notarized(_)
                | FinalizationStatus::FinalizedAndNotarized(_)
                | FinalizationStatus::ImplicitlyFinalized(_)
                | FinalizationStatus::ImplicitlySkipped => FinalizationEvent::default(),
                FinalizationStatus::Finalized => {
                    let mut event = FinalizationEvent::default();
                    self.status
                        .insert(slot, FinalizationStatus::FinalizedAndNotarized(block_hash));
                    self.handle_finalized((slot, block_hash), &mut event);
                    event
                }
            }
        } else {
            self.status
                .insert(slot, FinalizationStatus::Notarized(block_hash));
            FinalizationEvent::default()
        }
    }

    /// Marks the given slot as finalized.
    ///
    /// Handles possibly resulting direct finalization of a block in this slot.
    /// Further, also handles any possibly resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    pub fn mark_finalized(&mut self, slot: Slot) -> FinalizationEvent {
        if let Some(status) = self.status.get(&slot) {
            match status {
                FinalizationStatus::Finalized
                | FinalizationStatus::FinalizedAndNotarized(_)
                | FinalizationStatus::ImplicitlyFinalized(_) => FinalizationEvent::default(),
                FinalizationStatus::Notarized(block_hash) => {
                    let block_hash = *block_hash;
                    let mut event = FinalizationEvent::default();
                    self.status
                        .insert(slot, FinalizationStatus::FinalizedAndNotarized(block_hash));
                    self.handle_finalized((slot, block_hash), &mut event);
                    self.highest_finalized = slot.max(self.highest_finalized);
                    event
                }
                FinalizationStatus::ImplicitlySkipped => unreachable!("consensus safety violation"),
            }
        } else {
            self.status.insert(slot, FinalizationStatus::Finalized);
            self.highest_finalized = slot.max(self.highest_finalized);
            FinalizationEvent::default()
        }
    }

    /// Returns the highest finalized slot.
    ///
    /// Does not consider whether we have the block, or even know the hash.
    pub fn highest_finalized(&self) -> Slot {
        self.highest_finalized
    }

    /// Handles the direct finalization of the given block.
    ///
    /// Recurses through ancestors, potentially implicitly finalizing them.
    ///
    /// Updates the `event` all along the way with:
    /// - The finalized block,
    /// - any potentially implicitly finalized blocks, AND
    /// - any implicitly skipped slots.
    fn handle_finalized(&mut self, finalized: BlockId, event: &mut FinalizationEvent) {
        event.finalized = Some(finalized);
        if let Some(parent) = self.parents.get(&finalized) {
            self.handle_implicitly_finalized(finalized.0, *parent, event);
        }
    }

    /// Handles the indirect finalization of the given block.
    ///
    /// Recurses through ancestors, potentially implicitly finalizing them as well.
    ///
    /// Updates the `event` all along the way with:
    /// - Any potentially implicitly finalized blocks, AND
    /// - any implicitly skipped slots.
    fn handle_implicitly_finalized(
        &mut self,
        source_slot: Slot,
        implicitly_finalized: BlockId,
        event: &mut FinalizationEvent,
    ) {
        assert!(source_slot > implicitly_finalized.0);

        // implicitly skip slots in between
        for slot in implicitly_finalized.0.future_slots() {
            if slot == source_slot {
                break;
            }
            if let Some(status) = self.status.get(&slot) {
                match status {
                    FinalizationStatus::ImplicitlySkipped => {
                        return;
                    }
                    FinalizationStatus::Notarized(_)
                    | FinalizationStatus::ImplicitlyFinalized(_) => {}
                    FinalizationStatus::Finalized
                    | FinalizationStatus::FinalizedAndNotarized(_) => {
                        unreachable!("consensus safety violation")
                    }
                }
            }
            self.status
                .insert(slot, FinalizationStatus::ImplicitlySkipped);
            event.implicitly_skipped.push(slot);
        }

        // mark block as implicitly finalized
        if let Some(status) = self.status.get(&implicitly_finalized.0) {
            match status {
                FinalizationStatus::Notarized(_) | FinalizationStatus::Finalized => {}
                FinalizationStatus::FinalizedAndNotarized(_)
                | FinalizationStatus::ImplicitlyFinalized(_) => {
                    return;
                }
                FinalizationStatus::ImplicitlySkipped => {
                    unreachable!("consensus safety violation")
                }
            }
        }
        self.status.insert(
            implicitly_finalized.0,
            FinalizationStatus::ImplicitlyFinalized(implicitly_finalized.1),
        );
        event.implicitly_finalized.push(implicitly_finalized);

        // recurse through ancestors
        if let Some(parent) = self.parents.get(&implicitly_finalized) {
            self.handle_implicitly_finalized(implicitly_finalized.0, *parent, event);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut tracker = FinalityTracker::default();

        // slow finalize a block
        let slot = Slot::genesis().next();
        let event = tracker.mark_notarized(slot, [1; 32]);
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_finalized(slot);
        assert_eq!(event.finalized, Some((slot, [1; 32])));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // fast finalize a block
        let slot = slot.next();
        let event = tracker.mark_fast_finalized(slot, [2; 32]);
        assert_eq!(event.finalized, Some((slot, [2; 32])));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITHOUT skips
        let slot = slot.next().next();
        let event = tracker.add_parent((slot, [4; 32]), (slot.prev(), [3; 32]));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_fast_finalized(slot, [4; 32]);
        assert_eq!(event.finalized, Some((slot, [4; 32])));
        assert_eq!(event.implicitly_finalized, vec![(slot.prev(), [3; 32])]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITH skips
        let slot = slot.next().next().next();
        let event = tracker.add_parent((slot, [6; 32]), (slot.prev().prev(), [5; 32]));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_fast_finalized(slot, [6; 32]);
        assert_eq!(event.finalized, Some((slot, [6; 32])));
        assert_eq!(
            event.implicitly_finalized,
            vec![(slot.prev().prev(), [5; 32])]
        );
        assert_eq!(event.implicitly_skipped, vec![slot.prev()]);
    }

    #[test]
    fn no_duplicates() {
        let mut tracker = FinalityTracker::default();

        // slow finalize + fast finalize a block
        let slot = Slot::genesis().next();
        let event = tracker.mark_finalized(slot);
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_notarized(slot, [1; 32]);
        assert_eq!(event.finalized, Some((slot, [1; 32])));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);
        let event = tracker.mark_fast_finalized(slot, [1; 32]);
        assert_eq!(event, FinalizationEvent::default());

        // do NOT implicitly finalize parent, that is already directly finalized
        let slot = slot.next();
        let event = tracker.add_parent((slot, [2; 32]), (slot.prev(), [1; 32]));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_fast_finalized(slot, [2; 32]);
        assert_eq!(event.finalized, Some((slot, [2; 32])));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITHOUT skips
        let slot = slot.next().next();
        let event = tracker.add_parent((slot, [4; 32]), (slot.prev(), [3; 32]));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_fast_finalized(slot, [4; 32]);
        assert_eq!(event.finalized, Some((slot, [4; 32])));
        assert_eq!(event.implicitly_finalized, vec![(slot.prev(), [3; 32])]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // do NOT implicitly finalize parent again when adding parent again
        let event = tracker.add_parent((slot, [4; 32]), (slot.prev(), [3; 32]));
        assert_eq!(event, FinalizationEvent::default());
    }
}
