// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Slot`] type.

use std::fmt::Display;

use wincode::{SchemaRead, SchemaWrite};

/// Number of slots in each leader window.
// NOTE: this is public to support testing and one additional function.
// Consider hiding it.
pub const SLOTS_PER_WINDOW: u64 = 4;

/// Number of slots in each epoch.
// NOTE: consider hiding this definition.
pub const SLOTS_PER_EPOCH: u64 = 18_000;

/// Slot number type.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, SchemaRead, SchemaWrite)]
pub struct Slot(u64);

impl Slot {
    /// Creates a new slot with the given number.
    pub fn new(slot: u64) -> Self {
        Self(slot)
    }

    /// Returns the genesis slot.
    pub fn genesis() -> Self {
        Self(0)
    }

    /// Returns the inner `u64`.
    pub fn inner(self) -> u64 {
        self.0
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
}
