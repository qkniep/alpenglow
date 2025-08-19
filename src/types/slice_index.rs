// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::fmt::Display;

use serde:de::{self, Visitor};
use serde::{Deserialize, Serialize};

const MAX_SLICES_PER_BLOCK: usize = 1024;

/// Slice index type.
///
/// Using strong type to enforce certain constraints, e.g. it is never >= MAX_SLICES_PER_BLOCK.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct SliceIndex(usize);

impl SliceIndex {
    /// Creates a new SliceIndex for testing purposes.
    ///
    /// Panics if `index` is not in the valid range.
    #[cfg(test)]
    pub(crate) fn new_unchecked(index: usize) -> Self {
        Self::new(index).unwrap()
    }

    /// Creates a new SliceIndex.
    fn new(index: usize) -> Option<Self> {
        if index >= MAX_SLICES_PER_BLOCK {
            None
        } else {
            Some(Self(index))
        }
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

    /// Returns `true` if self is the max possible, i.e. `MAX_SLICES_PER_BLOCK - 1`, SliceIndex.
    pub(crate) fn is_max(&self) -> bool {
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

impl Display for SliceIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'de> Deserialize<'de> for SliceIndex {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_u64(SliceIndexVisitor)
    }
}

struct SliceIndexVisitor;

impl<'de> Visitor<'de> for SliceIndexVisitor {
    type Value = SliceIndex;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            formatter,
            "expected a usize between 0 and {MAX_SLICES_PER_BLOCK}"
        )
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        SliceIndex::new(v as usize).ok_or(de::Error::custom(
            "input {v} is not in the range [0:{MAX_SLICES_PER_BLOCK})",
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slice_index_valid_deserialization() {
        let vs = [0, 1, MAX_SLICES_PER_BLOCK - 10, MAX_SLICES_PER_BLOCK - 1];
        let vs = vs.into_iter().map(|v| v.to_string());
        for v in vs {
            serde_json::from_str::<SliceIndex>(&v).unwrap();
        }
    }

    #[test]
    fn slice_index_invalid_deserialization() {
        let vs = [
            (-1).to_string(),
            i64::MIN.to_string().to_string(),
            MAX_SLICES_PER_BLOCK.to_string(),
            (MAX_SLICES_PER_BLOCK + 1).to_string(),
            (i64::MAX).to_string(),
            (u64::MAX).to_string(),
            (usize::MAX).to_string(),
        ];
        for v in vs {
            serde_json::from_str::<SliceIndex>(&v).unwrap_err();
        }
    }
}
