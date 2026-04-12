// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Stake`] type.

use std::fmt::Display;
use std::ops::{Sub, SubAssign};

use derive_more::{Add, AddAssign, From, Into, Mul, Sum};
use serde::{Deserialize, Serialize};
use wincode::{SchemaRead, SchemaWrite};

/// Validator stake type.
#[repr(transparent)]
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Add,
    AddAssign,
    Mul,
    Sum,
    From,
    Into,
    SchemaRead,
    SchemaWrite,
    Serialize,
    Deserialize,
)]
#[serde(transparent)]
pub struct Stake(u64);

impl Stake {
    /// Creates a new stake value.
    pub fn new(stake: u64) -> Self {
        Self(stake)
    }

    /// Returns the inner `u64`.
    pub fn inner(self) -> u64 {
        self.0
    }

    /// Divides self by `divisor`, rounding up.
    pub fn div_ceil(self, divisor: u64) -> Self {
        Self(self.0.div_ceil(divisor))
    }

    /// Checked addition. Returns `None` on overflow.
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(Self)
    }
}

impl Sub for Stake {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl SubAssign for Stake {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl Display for Stake {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
