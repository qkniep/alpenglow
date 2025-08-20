// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tracks finality of blocks.
//!
//!

use std::collections::BTreeMap;

use crate::BlockId;
use crate::crypto::Hash;
use crate::types::Slot;

///
#[derive(Default)]
pub struct FinalityTracker {
    ///
    status: BTreeMap<Slot, FinalizationStatus>,
    ///
    parents: BTreeMap<BlockId, BlockId>,

    ///
    highest_finalized: Slot,
}

///
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizationStatus {
    Notarized(Hash),
    Finalized,
    FinalizedAndNotarized(Hash),
    ImplicitlyFinalized(Hash),
    ImplicitlySkipped,
}

///
#[derive(Default)]
pub struct FinalizationEvent {
    pub(super) finalized: Option<BlockId>,
    pub(super) implicitly_finalized: Vec<BlockId>,
    pub(super) implicitly_skipped: Vec<Slot>,
}

impl FinalityTracker {
    ///
    pub fn add_parent(&mut self, block: BlockId, parent: BlockId) -> FinalizationEvent {
        let mut event = FinalizationEvent::default();
        self.parents.insert(block, parent);
        if let Some(status) = self.status.get(&block.0)
            && let FinalizationStatus::FinalizedAndNotarized(block_hash)
            | FinalizationStatus::ImplicitlyFinalized(block_hash) = status
            && block.1 == *block_hash
        {
            self.handle_implicitly_finalized(block.0, parent, &mut event);
        }
        event
    }

    ///
    pub fn mark_fast_finalized(&mut self, slot: Slot, block_hash: Hash) -> FinalizationEvent {
        let mut event = FinalizationEvent::default();
        if let Some(status) = self.status.get(&slot) {
            match status {
                FinalizationStatus::FinalizedAndNotarized(_) => {
                    return event;
                }
                FinalizationStatus::Notarized(_)
                | FinalizationStatus::Finalized
                | FinalizationStatus::ImplicitlyFinalized(_) => {}
                FinalizationStatus::ImplicitlySkipped => unreachable!("consensus safety violation"),
            }
        }

        self.status
            .insert(slot, FinalizationStatus::FinalizedAndNotarized(block_hash));
        self.handle_finalized((slot, block_hash), &mut event);
        self.highest_finalized = slot.max(self.highest_finalized);
        event
    }

    ///
    pub fn mark_notarized(&mut self, slot: Slot, block_hash: Hash) -> FinalizationEvent {
        let mut event = FinalizationEvent::default();
        if let Some(status) = self.status.get(&slot) {
            match status {
                FinalizationStatus::Notarized(_)
                | FinalizationStatus::FinalizedAndNotarized(_)
                | FinalizationStatus::ImplicitlyFinalized(_)
                | FinalizationStatus::ImplicitlySkipped => {
                    return event;
                }
                FinalizationStatus::Finalized => {
                    self.status
                        .insert(slot, FinalizationStatus::FinalizedAndNotarized(block_hash));
                    self.handle_finalized((slot, block_hash), &mut event);
                    return event;
                }
            }
        } else {
            self.status
                .insert(slot, FinalizationStatus::Notarized(block_hash));
            event
        }
    }

    ///
    pub fn mark_finalized(&mut self, slot: Slot) -> FinalizationEvent {
        let mut event = FinalizationEvent::default();
        if let Some(status) = self.status.get(&slot) {
            match status {
                FinalizationStatus::Finalized
                | FinalizationStatus::FinalizedAndNotarized(_)
                | FinalizationStatus::ImplicitlyFinalized(_) => {
                    return event;
                }
                FinalizationStatus::Notarized(block_hash) => {
                    self.handle_finalized((slot, *block_hash), &mut event);
                    self.highest_finalized = slot.max(self.highest_finalized);
                    return event;
                }
                FinalizationStatus::ImplicitlySkipped => unreachable!("consensus safety violation"),
            }
        } else {
            self.status.insert(slot, FinalizationStatus::Finalized);
            self.highest_finalized = slot.max(self.highest_finalized);
            event
        }
    }

    ///
    pub fn highest_finalized(&self) -> Slot {
        self.highest_finalized
    }

    ///
    fn handle_finalized(&mut self, finalized: BlockId, event: &mut FinalizationEvent) {
        event.finalized = Some(finalized);
        if let Some(parent) = self.parents.get(&finalized) {
            self.handle_implicitly_finalized(finalized.0, *parent, event);
        }
    }

    ///
    fn handle_implicitly_finalized(
        &mut self,
        source_slot: Slot,
        implicitly_finalized: BlockId,
        event: &mut FinalizationEvent,
    ) {
        assert!(source_slot > implicitly_finalized.0);
        for slot in implicitly_finalized.0.future_slots() {
            if slot == source_slot {
                break;
            }
            // TODO: add assertions
            self.status
                .insert(slot, FinalizationStatus::ImplicitlySkipped);
        }
        // TODO: add assertions
        self.status.insert(
            implicitly_finalized.0,
            FinalizationStatus::ImplicitlyFinalized(implicitly_finalized.1),
        );
        event.implicitly_finalized.push(implicitly_finalized);

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
    }
}
