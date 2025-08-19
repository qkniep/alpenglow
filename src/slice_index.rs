// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};

const MAX_SLICES_PER_BLOCK: usize = 1024;

/// Slice index type.
///
/// Using strong type to enforce certain constraints, e.g. it is never >= MAX_SLICES_PER_BLOCK.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord)]
pub struct SliceIndex(usize);

impl SliceIndex {
    /// Creates a new SliceIndex for testing purposes.
    #[cfg(test)]
    pub(crate) fn new(index: usize) -> Self {
        assert!(index < MAX_SLICES_PER_BLOCK);
        Self(index)
    }

    /// Returns the inner `usize`.
    pub(crate) fn inner(self) -> usize {
        self.0
    }

    /// Returns the first, i.e. smallest, `SliceIndex`.
    pub(crate) fn first() -> Self {
        Self(0)
    }

    /// Returns `true` if self is the first, i.e. smallest, `SliceIndex`.
    pub(crate) fn is_first(&self) -> bool {
        self.0 == 0
    }

    /// Returns true if self is the last i.e. MAX_SLICES_PER_BLOCK - 1 SliceIndex.
    pub(crate) fn is_last(&self) -> bool {
        self.0 == MAX_SLICES_PER_BLOCK - 1
    }

    /// Returns an iterator that iterates over all the valid SliceIndexes.
    pub(crate) fn all() -> impl Iterator<Item = Self> {
        (0..MAX_SLICES_PER_BLOCK).map(Self)
    }

    /// Returns an iterator that iterates over SliceIndexes starting from the first to self inclusive.
    pub(crate) fn until(&self) -> impl Iterator<Item = Self> {
        (0..=self.0).map(Self)
    }
}
