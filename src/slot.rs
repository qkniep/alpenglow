use std::fmt::Display;

use serde::{Deserialize, Serialize};

/// Number of slots in each leader window.
///
/// NOTE: this is public to support testing and one function additional function.
/// Consider hiding it.
pub const SLOTS_PER_WINDOW: u64 = 4;
/// Number of slots in each epoch.
///
/// NOTE: consider hiding this definition.
pub const SLOTS_PER_EPOCH: u64 = 18_000;

/// Slot number type.
#[derive(Clone, Copy, Debug, PartialOrd, Ord, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Slot(u64);

impl Slot {
    pub fn new(slot: u64) -> Self {
        Self(slot)
    }

    /// Returns the inner u64.
    pub fn inner(self) -> u64 {
        self.0
    }

    /// Returns an infinite iterator that yields the first slot in each window.
    pub fn windows() -> impl Iterator<Item = Self> {
        (0..).map(Self)
    }

    /// Returns a double-ended iterator that yields all the slots in the
    /// window `self` is in.
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
        self.0 % SLOTS_PER_WINDOW == 0
    }

    /// Returns the next slot after `self`.
    pub fn next(&self) -> Self {
        Self(self.0 + 1)
    }

    /// Returns the previous slot before `self`.
    pub fn prev(&self) -> Self {
        Self(self.0 - 1)
    }

    /// Returns true if this slot is part of the genesis window.
    pub fn is_genesis_window(&self) -> bool {
        let window = self.0 / SLOTS_PER_WINDOW;
        window == 0
    }
}

impl Display for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
