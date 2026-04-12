// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatorId`] type.

use std::fmt::Display;

use serde::{Deserialize, Serialize};
use wincode::{SchemaRead, SchemaWrite};

/// Validator ID number type.
#[repr(transparent)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
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
pub struct ValidatorId(u64);

impl ValidatorId {
    /// Creates a new validator ID.
    pub fn new(id: u64) -> Self {
        Self(id)
    }

    /// Returns the inner `u64`.
    pub fn inner(self) -> u64 {
        self.0
    }

    /// Returns the ID as a `usize` for use as an array index.
    pub fn as_index(self) -> usize {
        self.0 as usize
    }
}

impl Display for ValidatorId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
