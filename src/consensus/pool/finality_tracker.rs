// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks finality of blocks.
//!
//! This is used internally as part of [`PoolImpl`].
//!
//! Keeps track of:
//! - Direct finalization of blocks,
//! - resulting indirect finalizations of blocks, and
//! - resulting implicit skipping of slots
//!
//! It does this based on:
//! - Notarization of blocks,
//! - finalization of slots, and
//! - availability of blocks and knowledge of their parents.
//!
//! [`PoolImpl`]: crate::consensus::pool::PoolImpl

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use crate::BlockId;
use crate::crypto::merkle::{BlockHash, GENESIS_BLOCK_HASH};
use crate::types::Slot;

/// Tracks finality of blocks.
pub(super) struct FinalityTracker {
    /// Current finalization status for each slot.
    status: BTreeMap<Slot, FinalizationStatus>,
    /// Maps blocks to their parents.
    parents: BTreeMap<BlockId, BlockId>,
    /// The highest finalized slot so far.
    ///
    /// This means that slot has a fast finalization *or* finalization + notarization.
    /// Also, all prior slots are finalized (directly or implicitly) *or* implicitly skipped.
    highest_finalized_slot: Slot,
    /// The first slot whose state has not yet been pruned, i.e. the lowest slot
    /// still tracked.
    ///
    /// Everything below this is a contiguous prefix of fully resolved (finalized
    /// or implicitly skipped) slots that has been dropped. This can lag behind
    /// [`Self::highest_finalized_slot`]: a slot may be finalized before the chain
    /// connecting it down to here is known, in which case the slots in between
    /// are not yet resolved and must be kept.
    first_unpruned_slot: Slot,
}

/// Possible states a slot can be in regarding finality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum FinalizationStatus {
    /// Block with given hash is notarized, but slot is not yet (known to be) finalized.
    Notarized(BlockHash),
    /// Slot is known to be finalized, but we are missing the notarization certificate.
    FinalPendingNotar,
    /// Slot is finalized, and notarized block is known to have the given hash.
    Finalized(BlockHash),
    /// Block with given hash was implicitly finalized through later finalization.
    ImplicitlyFinalized(BlockHash),
    /// Slot was implicitly skipped through later finalization.
    ImplicitlySkipped,
}

/// Information about newly finalized slots.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct FinalizationEvent {
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
    pub(super) fn add_parent(&mut self, block: BlockId, parent: BlockId) -> FinalizationEvent {
        assert!(block.0 > parent.0);
        match self.parents.entry(block.clone()) {
            Entry::Occupied(e) => {
                assert!(e.get() == &parent);
                return FinalizationEvent::default();
            }
            Entry::Vacant(e) => {
                e.insert(parent.clone());
            }
        }

        let (slot, block_hash) = block;
        let Some(status) = self.status.get(&slot) else {
            return FinalizationEvent::default();
        };
        match status {
            FinalizationStatus::Finalized(hash) | FinalizationStatus::ImplicitlyFinalized(hash) => {
                let mut event = FinalizationEvent::default();
                if &block_hash == hash {
                    self.handle_implicitly_finalized(block.0, parent, &mut event);
                }
                self.prune();
                event
            }
            FinalizationStatus::Notarized(_)
            | FinalizationStatus::FinalPendingNotar
            | FinalizationStatus::ImplicitlySkipped => FinalizationEvent::default(),
        }
    }

    /// Marks the given block as fast finalized.
    ///
    /// If the block was newly finalized, handles resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    pub(super) fn mark_fast_finalized(
        &mut self,
        slot: Slot,
        block_hash: BlockHash,
    ) -> FinalizationEvent {
        let old = self
            .status
            .insert(slot, FinalizationStatus::Finalized(block_hash.clone()));
        if let Some(status) = old {
            match status {
                FinalizationStatus::Finalized(hash)
                | FinalizationStatus::ImplicitlyFinalized(hash) => {
                    assert_eq!(hash, block_hash, "consensus safety violation");
                    return FinalizationEvent::default();
                }
                FinalizationStatus::Notarized(hash) => {
                    assert_eq!(hash, block_hash, "consensus safety violation");
                }
                FinalizationStatus::FinalPendingNotar => {}
                FinalizationStatus::ImplicitlySkipped => panic!("consensus safety violation"),
            }
        }

        let mut event = FinalizationEvent::default();
        self.handle_finalized_block((slot, block_hash), &mut event);
        self.prune();
        event
    }

    /// Marks the given block as notarized.
    ///
    /// Handles possibly resulting direct finalization of the block.
    /// Further, also handles any possibly resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    pub(super) fn mark_notarized(
        &mut self,
        slot: Slot,
        block_hash: BlockHash,
    ) -> FinalizationEvent {
        let old = self
            .status
            .insert(slot, FinalizationStatus::Notarized(block_hash.clone()));
        let Some(status) = old else {
            return FinalizationEvent::default();
        };

        match status {
            FinalizationStatus::Notarized(hash)
            | FinalizationStatus::Finalized(hash)
            | FinalizationStatus::ImplicitlyFinalized(hash) => {
                assert_eq!(hash, block_hash, "consensus safety violation");
                FinalizationEvent::default()
            }
            FinalizationStatus::ImplicitlySkipped => FinalizationEvent::default(),
            FinalizationStatus::FinalPendingNotar => {
                let mut event = FinalizationEvent::default();
                self.status
                    .insert(slot, FinalizationStatus::Finalized(block_hash.clone()));
                self.handle_finalized_block((slot, block_hash), &mut event);
                self.prune();
                event
            }
        }
    }

    /// Marks the given slot as finalized.
    ///
    /// Handles possibly resulting direct finalization of a block in this slot.
    /// Further, also handles any possibly resulting implicit finalizations.
    ///
    /// Returns a [`FinalizationEvent`] that contains information about newly finalized slots.
    pub(super) fn mark_finalized(&mut self, slot: Slot) -> FinalizationEvent {
        let old = self
            .status
            .insert(slot, FinalizationStatus::FinalPendingNotar);
        let Some(status) = old else {
            return FinalizationEvent::default();
        };

        match status {
            FinalizationStatus::FinalPendingNotar
            | FinalizationStatus::Finalized(_)
            | FinalizationStatus::ImplicitlyFinalized(_) => FinalizationEvent::default(),
            FinalizationStatus::Notarized(block_hash) => {
                let mut event = FinalizationEvent::default();
                self.status
                    .insert(slot, FinalizationStatus::Finalized(block_hash.clone()));
                self.handle_finalized_block((slot, block_hash), &mut event);
                self.prune();
                event
            }
            FinalizationStatus::ImplicitlySkipped => panic!("consensus safety violation"),
        }
    }

    /// Returns the highest finalized slot.
    ///
    /// This means that slot has a fast finalization *or* finalization + notarization.
    /// Also, all prior slots are finalized (directly or implicitly) *or* implicitly skipped.
    pub(super) fn highest_finalized_slot(&self) -> Slot {
        self.highest_finalized_slot
    }

    /// Returns the first slot whose state has not yet been pruned.
    ///
    /// All slots below this are fully resolved and no longer tracked,
    /// so certs and votes for them can be safely ignored.
    pub(super) fn first_unpruned_slot(&self) -> Slot {
        self.first_unpruned_slot
    }

    /// Advances [`Self::first_unpruned_slot`] across the contiguous prefix of
    /// resolved slots and drops all state below it.
    ///
    /// A slot is resolved once its fate is sealed: directly or implicitly
    /// finalized, or implicitly skipped. We can only prune such a contiguous
    /// prefix: a slot can be finalized before the chain connecting it down to
    /// [`Self::first_unpruned_slot`] is known, so a higher finalized slot does
    /// not imply the slots below it are resolved yet.
    fn prune(&mut self) {
        let mut next = self.first_unpruned_slot.next();
        while self.status.get(&next).is_some_and(|status| {
            matches!(
                status,
                FinalizationStatus::Finalized(_)
                    | FinalizationStatus::ImplicitlyFinalized(_)
                    | FinalizationStatus::ImplicitlySkipped
            )
        }) {
            self.first_unpruned_slot = next;
            next = next.next();
        }
        let root = self.first_unpruned_slot;
        self.status = self.status.split_off(&root);
        self.parents.retain(|(slot, _), _| *slot >= root);
    }

    /// Handles the direct finalization of the given block.
    ///
    /// Recurses through ancestors, potentially implicitly finalizing them.
    ///
    /// Updates the `event` all along the way with:
    /// - The finalized block,
    /// - any potentially implicitly finalized blocks, and
    /// - any implicitly skipped slots.
    fn handle_finalized_block(&mut self, finalized: BlockId, event: &mut FinalizationEvent) {
        let (slot, _) = finalized;
        event.finalized = Some(finalized.clone());
        self.highest_finalized_slot = slot.max(self.highest_finalized_slot);

        if let Some(parent) = self.parents.get(&finalized).cloned() {
            self.handle_implicitly_finalized(slot, parent, event);
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

        // implicitly skip slots in between
        for slot in implicitly_finalized.0.future_slots() {
            if slot == source_slot {
                break;
            }
            let old = self
                .status
                .insert(slot, FinalizationStatus::ImplicitlySkipped);
            if let Some(status) = old {
                match status {
                    FinalizationStatus::ImplicitlySkipped => {
                        return;
                    }
                    FinalizationStatus::Notarized(_) => {}
                    FinalizationStatus::FinalPendingNotar
                    | FinalizationStatus::Finalized(_)
                    | FinalizationStatus::ImplicitlyFinalized(_) => {
                        panic!("consensus safety violation")
                    }
                }
            }
            event.implicitly_skipped.push(slot);
        }

        // mark block as implicitly finalized
        let (slot, block_hash) = implicitly_finalized.clone();
        let old = self.status.insert(
            slot,
            FinalizationStatus::ImplicitlyFinalized(block_hash.clone()),
        );
        if let Some(status) = old {
            match &status {
                FinalizationStatus::Finalized(hash)
                | FinalizationStatus::ImplicitlyFinalized(hash) => {
                    assert_eq!(*hash, block_hash, "consensus safety violation");
                    self.status.insert(slot, status);
                    return;
                }
                FinalizationStatus::Notarized(hash) => {
                    assert_eq!(*hash, block_hash, "consensus safety violation");
                }
                FinalizationStatus::FinalPendingNotar => {}
                FinalizationStatus::ImplicitlySkipped => {
                    panic!("consensus safety violation")
                }
            }
        }
        event
            .implicitly_finalized
            .push(implicitly_finalized.clone());

        // recurse through ancestors
        if let Some(parent) = self.parents.get(&implicitly_finalized).cloned() {
            self.handle_implicitly_finalized(implicitly_finalized.0, parent, event);
        }
    }
}

impl Default for FinalityTracker {
    /// Creates a new empty tracker.
    ///
    /// Initially, only the genesis block is considered (directly) finalized.
    fn default() -> Self {
        let mut status = BTreeMap::new();
        status.insert(
            Slot::genesis(),
            FinalizationStatus::Notarized(GENESIS_BLOCK_HASH),
        );
        Self {
            status,
            parents: BTreeMap::new(),
            highest_finalized_slot: Slot::genesis(),
            first_unpruned_slot: Slot::genesis(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::Hash;

    #[test]
    fn basic() {
        let mut tracker = FinalityTracker::default();

        // slow finalize a block
        let slot1 = Slot::genesis().next();
        let hash1: BlockHash = Hash::random_for_test().into();
        let event = tracker.mark_notarized(slot1, hash1.clone());
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_finalized(slot1);
        assert_eq!(event.finalized, Some((slot1, hash1)));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // fast finalize a block
        let slot2 = slot1.next();
        let hash2: BlockHash = Hash::random_for_test().into();
        let event = tracker.mark_fast_finalized(slot2, hash2.clone());
        assert_eq!(event.finalized, Some((slot2, hash2)));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITHOUT skips
        let slot4 = slot2.next().next();
        let hash3: BlockHash = Hash::random_for_test().into();
        let hash4: BlockHash = Hash::random_for_test().into();
        let event = tracker.add_parent((slot4, hash4.clone()), (slot4.prev(), hash3.clone()));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_fast_finalized(slot4, hash4.clone());
        assert_eq!(event.finalized, Some((slot4, hash4)));
        assert_eq!(event.implicitly_finalized, vec![(slot4.prev(), hash3)]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITH skips
        let slot7 = slot4.next().next().next();
        let hash5: BlockHash = Hash::random_for_test().into();
        let hash7: BlockHash = Hash::random_for_test().into();
        let event =
            tracker.add_parent((slot7, hash7.clone()), (slot7.prev().prev(), hash5.clone()));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_fast_finalized(slot7, hash7.clone());
        assert_eq!(event.finalized, Some((slot7, hash7.clone())));
        assert_eq!(
            event.implicitly_finalized,
            vec![(slot7.prev().prev(), hash5)]
        );
        assert_eq!(event.implicitly_skipped, vec![slot7.prev()]);
    }

    #[test]
    fn no_duplicates() {
        let mut tracker = FinalityTracker::default();

        // slow finalize + fast finalize a block
        let slot1 = Slot::genesis().next();
        let hash1: BlockHash = Hash::random_for_test().into();
        let event = tracker.mark_finalized(slot1);
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_notarized(slot1, hash1.clone());
        assert_eq!(event.finalized, Some((slot1, hash1.clone())));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);
        let event = tracker.mark_fast_finalized(slot1, hash1.clone());
        assert_eq!(event, FinalizationEvent::default());

        // do NOT implicitly finalize parent, that is already directly finalized
        let slot2 = slot1.next();
        let hash2: BlockHash = Hash::random_for_test().into();
        let event = tracker.add_parent((slot2, hash2.clone()), (slot2.prev(), hash1.clone()));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_fast_finalized(slot2, hash2.clone());
        assert_eq!(event.finalized, Some((slot2, hash2.clone())));
        assert_eq!(event.implicitly_finalized, vec![]);
        assert_eq!(event.implicitly_skipped, vec![]);

        // implicitly finalize a block WITHOUT skips
        let slot4 = slot2.next().next();
        let hash3: BlockHash = Hash::random_for_test().into();
        let hash4: BlockHash = Hash::random_for_test().into();
        let event = tracker.add_parent((slot4, hash4.clone()), (slot4.prev(), hash3.clone()));
        assert_eq!(event, FinalizationEvent::default());
        let event = tracker.mark_fast_finalized(slot4, hash4.clone());
        assert_eq!(event.finalized, Some((slot4, hash4.clone())));
        assert_eq!(
            event.implicitly_finalized,
            vec![(slot4.prev(), hash3.clone())]
        );
        assert_eq!(event.implicitly_skipped, vec![]);

        // do NOT implicitly finalize parent again when adding parent again
        let event = tracker.add_parent((slot4, hash4.clone()), (slot4.prev(), hash3.clone()));
        assert_eq!(event, FinalizationEvent::default());
    }

    #[test]
    fn prune() {
        let mut tracker = FinalityTracker::default();

        // Notarize and connect a chain of blocks across several slots.
        let mut prev = (Slot::genesis(), GENESIS_BLOCK_HASH);
        for s in 1..=6u64 {
            let slot = Slot::new(s);
            let hash: BlockHash = Hash::random_for_test().into();
            tracker.mark_notarized(slot, hash.clone());
            tracker.add_parent((slot, hash.clone()), prev.clone());
            prev = (slot, hash);
        }
        // Finalize slot 5, implicitly finalizing its ancestors. The whole chain
        // down to genesis is connected, so the watermark advances to slot 5.
        tracker.mark_finalized(Slot::new(5));

        let root = Slot::new(5);
        assert_eq!(tracker.first_unpruned_slot(), root);
        // Only slots at or above the watermark remain, in both maps.
        assert!(tracker.status.keys().all(|s| *s >= root));
        assert!(tracker.parents.keys().all(|(s, _)| *s >= root));
        assert!(tracker.status.contains_key(&root));
        assert!(!tracker.status.contains_key(&Slot::new(4)));
    }

    /// A slot finalized before the chain connecting it down to the watermark is
    /// known must not cause the unresolved slots below it to be pruned.
    #[test]
    fn prune_keeps_unresolved_gap() {
        let mut tracker = FinalityTracker::default();
        let hash2: BlockHash = Hash::random_for_test().into();

        // Slot 1 is finalized, but its block hash is not yet known: the chain
        // has not joined, so it stays unresolved (`FinalPendingNotar`).
        assert_eq!(
            tracker.mark_finalized(Slot::new(1)),
            FinalizationEvent::default()
        );

        // Slot 2 is directly finalized ahead of slot 1, with the connecting
        // chain still unknown.
        tracker.mark_notarized(Slot::new(2), hash2.clone());
        let event = tracker.mark_finalized(Slot::new(2));
        assert_eq!(event.finalized, Some((Slot::new(2), hash2)));

        // The watermark must NOT advance past the still-unresolved slot 1, even
        // though slot 2 is finalized. Otherwise slot 1 would be pruned and its
        // later notarization lost.
        assert_eq!(tracker.highest_finalized_slot(), Slot::new(2));
        assert_eq!(tracker.first_unpruned_slot(), Slot::genesis());
        assert!(tracker.status.contains_key(&Slot::new(1)));

        // Once slot 1's notarization arrives and the chain joins, it resolves
        // and the watermark catches up across the now-contiguous prefix.
        let hash1: BlockHash = Hash::random_for_test().into();
        tracker.add_parent(
            (Slot::new(1), hash1.clone()),
            (Slot::genesis(), GENESIS_BLOCK_HASH),
        );
        let event = tracker.mark_notarized(Slot::new(1), hash1.clone());
        assert_eq!(event.finalized, Some((Slot::new(1), hash1)));
        assert_eq!(tracker.first_unpruned_slot(), Slot::new(2));
    }
}
