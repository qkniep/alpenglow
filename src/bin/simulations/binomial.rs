// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Minimal binomial upper-tail probability used by the MCP parameter analyses.
//!
//! Computed via the backward recurrence
//! `P(X = i-1) / P(X = i) = i / (n - i + 1) · (1 - p) / p`,
//! summing from the top so that the tiny tail probabilities these analyses
//! care about keep full relative precision. This also avoids a transitive
//! dependency on `statrs` / `nalgebra` / `simba`.
//!
//! The series starts from `p^n`, which underflows to `0.0` once
//! `n · ln(1/p)` exceeds ~700 (e.g. `p = 0.2`, `n >= 460`). That is well beyond
//! the `n` (low hundreds) used in the simulations.

/// Returns `P(X >= m)` for `X ~ Binomial(n, p)`.
///
/// Sums the upper tail directly, so small probabilities — the regime these
/// analyses actually care about — keep full relative precision instead of
/// losing it to catastrophic cancellation in `1.0 - cdf`.
///
/// `p` must lie in `[0, 1]`. Saturates at `1.0` to absorb floating-point drift.
pub(crate) fn binomial_at_least(p: f64, n: u64, m: u64) -> f64 {
    debug_assert!((0.0..=1.0).contains(&p));
    if m == 0 {
        return 1.0;
    }
    if m > n {
        return 0.0;
    }
    if p == 0.0 {
        // m >= 1 here, so no mass reaches it.
        return 0.0;
    }
    let q = 1.0 - p;
    if q == 0.0 {
        // p == 1.0 with m <= n: all mass sits at n.
        return 1.0;
    }

    let ratio = q / p;
    let mut pmf = p.powi(n as i32); // P(X = n)
    let mut sf = pmf;
    let mut i = n;
    while i > m {
        pmf *= i as f64 / (n - i + 1) as f64 * ratio;
        sf += pmf;
        i -= 1;
    }
    sf.min(1.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn approx_eq(a: f64, b: f64, tol: f64) {
        assert!((a - b).abs() <= tol, "expected {a} ≈ {b} (tol {tol})");
    }

    fn rel_eq(a: f64, b: f64, rel_tol: f64) {
        assert!(
            (a - b).abs() <= rel_tol * b.abs(),
            "expected {a} ≈ {b} (rel tol {rel_tol})"
        );
    }

    #[test]
    fn boundary_cases() {
        // `m == 0` is always certain, `m > n` is impossible.
        assert_eq!(binomial_at_least(0.5, 10, 0), 1.0);
        assert_eq!(binomial_at_least(0.5, 10, 11), 0.0);
        // p == 0.0: no mass above 0; p == 1.0: all mass at n.
        assert_eq!(binomial_at_least(0.0, 10, 1), 0.0);
        assert_eq!(binomial_at_least(1.0, 10, 10), 1.0);
        assert_eq!(binomial_at_least(1.0, 10, 11), 0.0);
    }

    #[test]
    fn known_values() {
        // P(X >= 6 | n=10, p=0.5) = 386/1024
        approx_eq(binomial_at_least(0.5, 10, 6), 386.0 / 1024.0, 1e-12);
        // P(X >= 1 | n=10, p=0.2) = 1 - 0.8^10
        approx_eq(binomial_at_least(0.2, 10, 1), 1.0 - 0.8_f64.powi(10), 1e-15);
        // P(X >= n | n, p) = p^n
        approx_eq(binomial_at_least(0.3, 20, 20), 0.3_f64.powi(20), 1e-30);
    }

    #[test]
    fn deep_tail_keeps_precision() {
        // Exact rational values (via P(X >= m) = sum of C(n,i) p^i q^(n-i)).
        // These are the regime the callers operate in; `1.0 - cdf` returns
        // 0.0 or is off by ~800x here, so check tight relative tolerance.
        rel_eq(binomial_at_least(0.2, 200, 80), 7.378_5e-11, 1e-3);
        rel_eq(binomial_at_least(0.2, 200, 96), 6.955_9e-19, 1e-3);
        rel_eq(binomial_at_least(0.15, 300, 91), 1.396_2e-11, 1e-3);
    }

    #[test]
    fn monotone_in_m() {
        // P(X >= m) is non-increasing in m, from 1.0 at m=0 down to p^n at m=n.
        let mut prev = 1.0;
        for m in 0..=50 {
            let v = binomial_at_least(0.4, 50, m);
            assert!(v <= prev + 1e-15);
            prev = v;
        }
        approx_eq(prev, 0.4_f64.powi(50), 1e-30);
    }
}
