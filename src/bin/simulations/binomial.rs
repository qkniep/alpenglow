// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Minimal binomial CDF used by the MCP parameter analyses.
//!
//! Computed via the forward recurrence
//! `P(X = i+1) / P(X = i) = (n - i) / (i + 1) · p / (1 - p)`,
//! which is stable enough for the `n` (low hundreds) used in the simulations
//! while avoiding a transitive dependency on `statrs` / `nalgebra` / `simba`.

/// Returns `P(X <= k)` for `X ~ Binomial(n, p)`.
///
/// `p` must lie in `[0, 1]`. Saturates at `1.0` to absorb floating-point drift.
pub(crate) fn binomial_cdf(p: f64, n: u64, k: u64) -> f64 {
    debug_assert!((0.0..=1.0).contains(&p));
    if k >= n {
        return 1.0;
    }
    if p == 0.0 {
        return 1.0;
    }
    let q = 1.0 - p;
    if q == 0.0 {
        // p == 1.0 with k < n: all mass sits at n.
        return 0.0;
    }

    let n_f = n as f64;
    let ratio = p / q;
    let mut pmf = q.powi(n as i32);
    let mut cdf = pmf;
    for i in 0..k {
        pmf *= (n_f - i as f64) / (i + 1) as f64 * ratio;
        cdf += pmf;
    }
    cdf.min(1.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn approx_eq(a: f64, b: f64, tol: f64) {
        assert!((a - b).abs() <= tol, "expected {a} ≈ {b} (tol {tol})");
    }

    #[test]
    fn boundary_cases() {
        assert_eq!(binomial_cdf(0.0, 10, 0), 1.0);
        assert_eq!(binomial_cdf(1.0, 10, 9), 0.0);
        assert_eq!(binomial_cdf(1.0, 10, 10), 1.0);
        assert_eq!(binomial_cdf(0.5, 10, 10), 1.0);
        assert_eq!(binomial_cdf(0.5, 10, 99), 1.0);
    }

    #[test]
    fn known_values() {
        // P(X <= 5 | n=10, p=0.5) = 638/1024
        approx_eq(binomial_cdf(0.5, 10, 5), 638.0 / 1024.0, 1e-12);
        // P(X <= 0 | n=10, p=0.2) = 0.8^10
        approx_eq(binomial_cdf(0.2, 10, 0), 0.8_f64.powi(10), 1e-15);
        // P(X <= n-1 | n, p) = 1 - p^n
        approx_eq(binomial_cdf(0.3, 20, 19), 1.0 - 0.3_f64.powi(20), 1e-15);
    }

    #[test]
    fn monotone_in_k() {
        let mut prev = 0.0;
        for k in 0..=50 {
            let v = binomial_cdf(0.4, 50, k);
            assert!(v >= prev - 1e-15);
            prev = v;
        }
        approx_eq(prev, 1.0, 1e-12);
    }
}
