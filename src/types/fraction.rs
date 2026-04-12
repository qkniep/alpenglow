// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Fraction type for exact fractional comparisons without floating point.

use std::cmp::Ordering;
use std::fmt;

/// A fraction represented as numerator/denominator for exact comparisons.
///
/// This avoids floating-point precision issues when comparing stake thresholds.
/// The denominator must be non-zero; constructing with a zero denominator panics.
///
/// Note: `Eq` uses cross-multiplication (so `1/2 == 2/4`), but `Hash` is not
/// implemented. Do not use `Fraction` as a hash map key.
///
/// # Examples
/// ```
/// use alpenglow::types::Fraction;
///
/// const THRESHOLD: Fraction = Fraction::new(3, 5);
/// assert!(THRESHOLD.is_met(6, 10));
/// assert!(!THRESHOLD.is_met(5, 10));
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Fraction {
    numerator: u64,
    denominator: u64,
}

impl Fraction {
    /// Creates a new fraction. Panics if `denominator` is zero.
    #[must_use]
    pub const fn new(numerator: u64, denominator: u64) -> Self {
        assert!(denominator != 0, "fraction denominator must be non-zero");
        Self {
            numerator,
            denominator,
        }
    }

    /// Returns `true` if `value / total >= self`.
    ///
    /// Uses cross-multiplication in u128 to avoid floating-point imprecision
    /// and integer overflow.
    #[must_use]
    pub const fn is_met(self, value: u64, total: u64) -> bool {
        debug_assert!(total != 0, "is_met called with zero total");
        (value as u128) * (self.denominator as u128) >= (total as u128) * (self.numerator as u128)
    }

    /// Approximates this fraction as an f64.
    #[must_use]
    pub fn approx_f64(self) -> f64 {
        self.numerator as f64 / self.denominator as f64
    }
}

impl PartialEq for Fraction {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Fraction {}

impl PartialOrd for Fraction {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Fraction {
    fn cmp(&self, other: &Self) -> Ordering {
        let lhs = (self.numerator as u128) * (other.denominator as u128);
        let rhs = (other.numerator as u128) * (self.denominator as u128);
        lhs.cmp(&rhs)
    }
}

impl fmt::Display for Fraction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordering() {
        assert!(Fraction::new(1, 3) < Fraction::new(1, 2));
        assert!(Fraction::new(2, 4) == Fraction::new(1, 2));
        assert!(Fraction::new(3, 4) > Fraction::new(2, 3));
    }

    #[test]
    fn is_met_basic() {
        let threshold = Fraction::new(3, 5);
        assert!(threshold.is_met(3, 5));
        assert!(threshold.is_met(6, 10));
        assert!(threshold.is_met(7, 10));
        assert!(!threshold.is_met(5, 10));
    }

    #[test]
    fn is_met_boundary() {
        let threshold = Fraction::new(3, 5);
        assert!(threshold.is_met(7, 11));
        assert!(!threshold.is_met(6, 11));
    }

    #[test]
    fn is_met_strong_threshold() {
        let threshold = Fraction::new(4, 5);
        assert!(threshold.is_met(9, 11));
        assert!(!threshold.is_met(8, 11));
    }

    #[test]
    fn f64_precision_loss() {
        let total_stake = 100_000_000_000_000_000u64;
        let stake = 60_000_000_000_000_001u64;

        let f64_ratio = stake as f64 / total_stake as f64;
        assert!(f64_ratio <= 0.6, "f64 loses precision here");

        let threshold = Fraction::new(3, 5);
        assert!(threshold.is_met(stake, total_stake));
    }

    #[test]
    fn display() {
        assert_eq!(Fraction::new(3, 5).to_string(), "3/5");
    }

    #[test]
    #[should_panic(expected = "fraction denominator must be non-zero")]
    fn zero_denominator_panics() {
        let _ = Fraction::new(1, 0);
    }

    #[test]
    fn approx_f64() {
        let f = Fraction::new(3, 5);
        assert!((f.approx_f64() - 0.6).abs() < f64::EPSILON);
    }
}
