// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Slot`] type.

use std::fmt::Display;

use static_assertions::const_assert;
use wincode::{SchemaRead, SchemaWrite};

use super::epoch::Epoch;

/// Number of slots in each leader window.
// NOTE: this is public to support testing and one additional function.
// Consider hiding it.
pub const SLOTS_PER_WINDOW: u64 = 4;

/// Number of slots in each epoch.
// NOTE: consider hiding this definition.
pub const SLOTS_PER_EPOCH: u64 = 18_000;

// Epoch boundaries must coincide with leader-window boundaries, so that a leader
// window never straddles two epochs (and thus two validator sets). The
// epoch-local leader rotation in `EpochInfo::leader` also relies on each epoch
// being a whole number of windows.
const_assert!(SLOTS_PER_EPOCH.is_multiple_of(SLOTS_PER_WINDOW));

/// Slot number type.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, SchemaRead, SchemaWrite)]
pub struct Slot(u64);

impl Slot {
    /// Creates a new slot with the given number.
    pub const fn new(slot: u64) -> Self {
        Self(slot)
    }

    /// Returns the genesis slot.
    pub const fn genesis() -> Self {
        Self(0)
    }

    /// Returns the inner `u64`.
    pub const fn inner(self) -> u64 {
        self.0
    }

    /// Returns the epoch this slot belongs to.
    pub const fn epoch(self) -> Epoch {
        Epoch::new(self.0 / SLOTS_PER_EPOCH)
    }

    /// Returns the first slot in the epoch this slot belongs to.
    pub const fn first_slot_in_epoch(self) -> Slot {
        self.epoch().first_slot()
    }

    /// Returns `true` iff this slot is the first slot of its epoch.
    pub const fn is_epoch_start(self) -> bool {
        self.0.is_multiple_of(SLOTS_PER_EPOCH)
    }

    /// Returns an infinite iterator that yields the first slot in each window.
    pub fn windows() -> impl Iterator<Item = Self> {
        (0..).step_by(SLOTS_PER_WINDOW as usize).map(Self)
    }

    /// Returns a double-ended iterator that yields all the slots in the window `self` is in.
    pub fn slots_in_window(self) -> impl DoubleEndedIterator<Item = Slot> {
        let start = self.first_slot_in_window();
        (start.0..start.0 + SLOTS_PER_WINDOW).map(Self)
    }

    /// Returns an infinite iterator that yields all the slots after `self`.
    pub fn future_slots(&self) -> impl Iterator<Item = Self> {
        (self.0 + 1..).map(Self)
    }

    /// Returns the first slot in the window this slot belongs to.
    pub fn first_slot_in_window(&self) -> Slot {
        let window = self.0 / SLOTS_PER_WINDOW;
        Self(window * SLOTS_PER_WINDOW)
    }

    /// Returns the last slow in the window this slot belongs to.
    pub fn last_slot_in_window(&self) -> Slot {
        let window = self.0 / SLOTS_PER_WINDOW;
        let next_window = window + 1;
        Self(next_window * SLOTS_PER_WINDOW - 1)
    }

    /// Returns true if `self` is the first slot in the window.
    pub fn is_start_of_window(&self) -> bool {
        self.0.is_multiple_of(SLOTS_PER_WINDOW)
    }

    /// Returns the next slot after `self`.
    pub fn next(&self) -> Self {
        Self(self.0 + 1)
    }

    /// Returns the previous slot before `self`.
    pub fn prev(&self) -> Self {
        Self(self.0.checked_sub(1).unwrap())
    }

    /// Returns `true` iff this slot is part of the genesis window.
    pub fn is_genesis_window(&self) -> bool {
        let window = self.0 / SLOTS_PER_WINDOW;
        window == 0
    }

    /// Returns `true` iff this slot is the genesis slot.
    pub fn is_genesis(&self) -> bool {
        self.0 == 0
    }
}

impl Default for Slot {
    fn default() -> Self {
        Self::genesis()
    }
}

impl Display for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let window_slots = Slot::windows().take(10).collect::<Vec<_>>();
        for (window, first_slot) in window_slots.iter().take(9).enumerate() {
            assert!(first_slot.is_start_of_window());
            assert_eq!(*first_slot, first_slot.first_slot_in_window());
            let last_slot = first_slot.last_slot_in_window();
            assert_eq!(last_slot.next(), window_slots[window + 1]);
            assert_eq!(last_slot, window_slots[window + 1].prev());
        }
    }

    #[test]
    fn epoch_boundaries() {
        assert_eq!(Slot::genesis().epoch(), Epoch::genesis());
        assert!(Slot::genesis().is_epoch_start());

        // last slot of epoch 0 and first slot of epoch 1
        let last_of_0 = Slot::new(SLOTS_PER_EPOCH - 1);
        let first_of_1 = Slot::new(SLOTS_PER_EPOCH);
        assert_eq!(last_of_0.epoch(), Epoch::new(0));
        assert!(!last_of_0.is_epoch_start());
        assert_eq!(first_of_1.epoch(), Epoch::new(1));
        assert!(first_of_1.is_epoch_start());

        // first_slot_in_epoch maps any slot to its epoch's first slot
        assert_eq!(last_of_0.first_slot_in_epoch(), Slot::genesis());
        assert_eq!(first_of_1.first_slot_in_epoch(), first_of_1);
        assert_eq!(
            Slot::new(SLOTS_PER_EPOCH + 5).first_slot_in_epoch(),
            first_of_1
        );

        // epoch round-trips through Epoch::first_slot
        for e in 0..4 {
            assert_eq!(Epoch::new(e).first_slot().epoch(), Epoch::new(e));
        }
    }

    #[test]
    fn epoch_boundary_is_window_start() {
        // The const_assert guarantees this, but check it behaviourally too:
        // every epoch boundary must also be a window boundary.
        assert!(Slot::new(SLOTS_PER_EPOCH).is_start_of_window());
        assert_eq!(
            Slot::new(SLOTS_PER_EPOCH).first_slot_in_window(),
            Slot::new(SLOTS_PER_EPOCH)
        );
    }
}
