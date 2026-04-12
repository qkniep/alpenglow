// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Fraction type for exact fractional comparisons without floating point.

use std::cmp::Ordering;
use std::fmt;
use std::num::NonZeroU64;

/// A fraction represented as numerator/denominator for exact comparisons.
///
/// This avoids floating-point precision issues when comparing stake thresholds.
/// The non-zero denominator invariant is enforced by the type system via [`NonZeroU64`].
///
/// Note: `Eq` uses cross-multiplication (so `1/2 == 2/4`), but `Hash` is not
/// implemented. Do not use `Fraction` as a hash map key.
///
/// # Examples
/// ```
/// use std::num::NonZeroU64;
/// use alpenglow::types::Fraction;
///
/// const THRESHOLD: Fraction = Fraction::new(3, NonZeroU64::new(5).unwrap());
/// assert!(THRESHOLD.is_met(6, 10));
/// assert!(!THRESHOLD.is_met(5, 10));
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Fraction {
    numerator: u64,
    denominator: NonZeroU64,
}

impl Fraction {
    /// Creates a new fraction.
    #[must_use]
    pub const fn new(numerator: u64, denominator: NonZeroU64) -> Self {
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
        (value as u128) * (self.denominator.get() as u128)
            >= (total as u128) * (self.numerator as u128)
    }

    /// Approximates this fraction as an f64.
    #[must_use]
    pub fn approx_f64(self) -> f64 {
        self.numerator as f64 / self.denominator.get() as f64
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
        let lhs = (self.numerator as u128) * (other.denominator.get() as u128);
        let rhs = (other.numerator as u128) * (self.denominator.get() as u128);
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

    const fn frac(n: u64, d: u64) -> Fraction {
        Fraction::new(n, NonZeroU64::new(d).unwrap())
    }

    #[test]
    fn ordering() {
        assert!(frac(1, 3) < frac(1, 2));
        assert!(frac(2, 4) == frac(1, 2));
        assert!(frac(3, 4) > frac(2, 3));
    }

    #[test]
    fn is_met_basic() {
        let threshold = frac(3, 5);
        assert!(threshold.is_met(3, 5));
        assert!(threshold.is_met(6, 10));
        assert!(threshold.is_met(7, 10));
        assert!(!threshold.is_met(5, 10));
    }

    #[test]
    fn is_met_boundary() {
        let threshold = frac(3, 5);
        assert!(threshold.is_met(7, 11));
        assert!(!threshold.is_met(6, 11));
    }

    #[test]
    fn is_met_strong_threshold() {
        let threshold = frac(4, 5);
        assert!(threshold.is_met(9, 11));
        assert!(!threshold.is_met(8, 11));
    }

    #[test]
    fn f64_precision_loss() {
        let total_stake = 100_000_000_000_000_000u64;
        let stake = 60_000_000_000_000_001u64;

        let f64_ratio = stake as f64 / total_stake as f64;
        assert!(f64_ratio <= 0.6, "f64 loses precision here");

        assert!(frac(3, 5).is_met(stake, total_stake));
    }

    #[test]
    fn display() {
        assert_eq!(frac(3, 5).to_string(), "3/5");
    }

    #[test]
    fn approx_f64() {
        assert!((frac(3, 5).approx_f64() - 0.6).abs() < f64::EPSILON);
    }
}
