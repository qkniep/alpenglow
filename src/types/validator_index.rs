// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatorIndex`] type.

use std::fmt::Display;

use serde::{Deserialize, Serialize};
use wincode::{SchemaRead, SchemaWrite};

/// Index of a validator within an epoch's canonical validator list.
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
pub struct ValidatorIndex(u64);

impl ValidatorIndex {
    /// Creates a new validator index.
    pub fn new(index: u64) -> Self {
        Self(index)
    }

    /// Returns the inner `u64`.
    pub fn inner(self) -> u64 {
        self.0
    }

    /// Returns the index as a `usize` for use as an array index.
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
}

impl Display for ValidatorIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
