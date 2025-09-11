use std::fmt::Display;

use serde::de::{self, Visitor};
use serde::{Deserialize, Serialize};

use crate::shredder::TOTAL_SHREDS;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct ShredIndex(usize);

impl ShredIndex {
    pub fn new(index: usize) -> Option<Self> {
        if index >= TOTAL_SHREDS {
            None
        } else {
            Some(Self(index))
        }
    }

    /// Returns the inner `usize`.
    pub(crate) fn inner(self) -> usize {
        self.0
    }

    /// Returns an iterator that iterates over all the valid SliceIndexes.
    pub(crate) fn all() -> impl Iterator<Item = Self> {
        (0..TOTAL_SHREDS).map(Self)
    }
}

impl Display for ShredIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'de> Deserialize<'de> for ShredIndex {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_u64(ShredIndexVisitor)
    }
}

struct ShredIndexVisitor;

impl<'de> Visitor<'de> for ShredIndexVisitor {
    type Value = ShredIndex;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "expected a usize between 0 and {TOTAL_SHREDS}")
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        ShredIndex::new(v as usize).ok_or(de::Error::custom(
            "input {v} is not in the range [0:{MAX_SLICES_PER_BLOCK})",
        ))
    }
}
