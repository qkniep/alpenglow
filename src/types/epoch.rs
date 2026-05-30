// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Epoch`] type.

use std::fmt::Display;

use serde::{Deserialize, Serialize};
use wincode::{SchemaRead, SchemaWrite};

use super::slot::{SLOTS_PER_EPOCH, Slot};

/// Epoch number type.
///
/// An epoch is a fixed-length, contiguous range of [`SLOTS_PER_EPOCH`] slots.
/// The validator set is constant within an epoch and may only change at epoch
/// boundaries. Epoch `e` covers slots `[e * SLOTS_PER_EPOCH, (e + 1) * SLOTS_PER_EPOCH)`.
#[repr(transparent)]
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SchemaRead,
    SchemaWrite,
    Serialize,
    Deserialize,
)]
#[serde(transparent)]
pub struct Epoch(u64);

impl Epoch {
    /// Creates a new epoch with the given number.
    pub const fn new(epoch: u64) -> Self {
        Self(epoch)
    }

    /// Returns the genesis epoch (epoch 0, containing the genesis slot).
    pub const fn genesis() -> Self {
        Self(0)
    }

    /// Returns the inner `u64`.
    pub const fn inner(self) -> u64 {
        self.0
    }

    /// Returns the epoch immediately after `self`.
    pub const fn next(self) -> Self {
        Self(self.0 + 1)
    }

    /// Returns the first slot belonging to this epoch.
    pub const fn first_slot(self) -> Slot {
        Slot::new(self.0 * SLOTS_PER_EPOCH)
    }
}

impl Default for Epoch {
    fn default() -> Self {
        Self::genesis()
    }
}

impl Display for Epoch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
