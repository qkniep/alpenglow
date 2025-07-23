use std::fmt::Display;

use serde::{Deserialize, Serialize};

use crate::ValidatorInfo;

/// Number of slots in each leader window.
///
/// NOTE: this is public to support testing and one function additional function.
/// Consider hiding it.
pub const SLOTS_PER_WINDOW: u64 = 4;

/// Slot number type.
#[derive(Clone, Copy, Debug, PartialOrd, Ord, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Slot(u64);

impl Slot {
    pub fn new(slot: u64) -> Self {
        Self(slot)
    }

    pub fn inner(self) -> u64 {
        self.0
    }

    pub fn windows() -> impl Iterator<Item = Self> {
        (0..).map(|i| Self(i * SLOTS_PER_WINDOW))
    }

    pub fn to_be_bytes(&self) -> [u8; 8] {
        self.0.to_be_bytes()
    }

    pub fn slots_in_window(self) -> impl Iterator<Item = Slot> {
        let start = self.first_slot_in_window();
        (start.0..start.0 + SLOTS_PER_WINDOW).map(|s| Self::new(s))
    }

    pub fn future_slots(&self) -> impl Iterator<Item = Self> {
        (self.0 + 1..).map(|s| Self(s))
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

    pub fn first_slot_in_next_window(&self) -> Self {
        let window = self.0 / SLOTS_PER_WINDOW;
        let next_window = window + 1;
        Self(next_window * SLOTS_PER_WINDOW)
    }

    pub fn last_slot_in_prev_window(&self) -> Self {
        let window = self.0 / SLOTS_PER_WINDOW;
        Self(window * SLOTS_PER_WINDOW - 1)
    }

    pub fn is_start_of_window(&self) -> bool {
        self.0 % SLOTS_PER_WINDOW == 0
    }

    pub fn next(&self) -> Self {
        Self(self.0 + 1)
    }

    pub fn prev(&self) -> Self {
        Self(self.0 - 1)
    }

    /// Returns which validator should be the leader for the window this slot is in.
    pub fn leader<'a>(&self, validators: &'a [ValidatorInfo]) -> &'a ValidatorInfo {
        let slot = self.0;
        let window = (slot / SLOTS_PER_WINDOW) as usize;
        let ind = window % validators.len();
        &validators[ind]
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
