// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ShredIndex`] type.

use std::fmt::Display;
use std::mem::MaybeUninit;
use std::ops::Deref;

use serde::de::{self, Visitor};
use serde::{Deserialize, Serialize};
use wincode::{SchemaRead, SchemaWrite};

use crate::shredder::TOTAL_SHREDS;

/// Shred index type.
///
/// Using strong type to enforce certain constraints, e.g. it is never >= [`TOTAL_SHREDS`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, SchemaWrite)]
pub struct ShredIndex(usize);

impl ShredIndex {
    /// Creates a new shred index.
    pub fn new(index: usize) -> Option<Self> {
        if index >= TOTAL_SHREDS {
            None
        } else {
            Some(Self(index))
        }
    }

    /// Returns an iterator that iterates over all the valid shred indices.
    pub(crate) fn all() -> impl Iterator<Item = Self> {
        (0..TOTAL_SHREDS).map(Self)
    }
}

impl Deref for ShredIndex {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
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
            "input {v} is not in the range [0:{TOTAL_SHREDS})",
        ))
    }
}

impl<'de> SchemaRead<'de> for ShredIndex {
    type Dst = Self;

    fn read(
        reader: &mut impl wincode::io::Reader<'de>,
        dst: &mut MaybeUninit<Self::Dst>,
    ) -> wincode::ReadResult<()> {
        // SAFETY: Any read of `std::mem::size_of(usize)` bytes correctly initializes `usize`.
        unsafe {
            reader.copy_into_t(dst)?;
            if dst.assume_init_ref().0 >= TOTAL_SHREDS {
                Err(wincode::ReadError::Custom("shred index out of bounds"))
            } else {
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_serde() {
        let vs = [0, 1, TOTAL_SHREDS - 10, TOTAL_SHREDS - 1];
        let vs = vs.into_iter().map(|v| v.to_string());
        for v in vs {
            serde_json::from_str::<ShredIndex>(&v).unwrap();
        }
    }

    #[test]
    fn invalid_serde() {
        let vs = [
            (-1).to_string(),
            i64::MIN.to_string(),
            TOTAL_SHREDS.to_string(),
            (TOTAL_SHREDS + 1).to_string(),
            (i64::MAX).to_string(),
            (u64::MAX).to_string(),
            (usize::MAX).to_string(),
        ];
        for v in vs {
            serde_json::from_str::<ShredIndex>(&v).unwrap_err();
        }
    }

    #[test]
    fn valid_wincode() {
        let vs = [0, 1, TOTAL_SHREDS - 10, TOTAL_SHREDS - 1];
        let vs = vs.iter().map(wincode::serialize);
        for res in vs {
            let v = res.unwrap();
            wincode::deserialize::<ShredIndex>(&v).unwrap();
        }
    }

    #[test]
    fn invalid_wincode() {
        let vs = [TOTAL_SHREDS, TOTAL_SHREDS + 1, usize::MAX];
        let vs = vs.iter().map(wincode::serialize);
        for res in vs {
            let v = res.unwrap();
            wincode::deserialize::<ShredIndex>(&v).unwrap_err();
        }
    }
}
