// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Monte-Carlo simulations to evaluate robustness of random quorums.
//!
//! This implements two main attack scenarios:
//! - Equivocation attack: Less than 20% of stake is Byzantine.
//! - Censorship attack: Up to 40% of stake is crashed.
//!
//! For each attack scenario multiple adversary strategies are simulated:
//! - Random: Corrupt a random subset of validators.
//! - Small: Corrupt as many of the smallest validators as possible.
//! - Large: Corrupt as many of the largest validators as possible.

use std::fs::File;
use std::sync::RwLock;

use alpenglow::disseminator::rotor::{FaitAccompli1Sampler, SamplingStrategy};
use alpenglow::{Stake, ValidatorInfo};
use log::debug;
use rand::prelude::*;
use rayon::prelude::*;
use static_assertions::const_assert_eq;

/// Parallelism level for rayon.
const PARALLELISM: usize = 1000;
/// Interval to take write locks on `tests` and `failures`.
const WRITE_BATCH: usize = 1000;
/// Number of total iterations per attack scenario.
const TOTAL_ITERATIONS: usize = 100_000_000;
const_assert_eq!(TOTAL_ITERATIONS % (PARALLELISM * WRITE_BATCH), 0);
/// Simulations stop early if the number of failures is greater than this.
const MAX_FAILURES: usize = 10_000;

/// Adversary strength.
#[derive(Clone, Copy, Debug)]
pub struct AdversaryStrength {
    /// Fraction of stake that may crash.
    pub crashed: f64,
    /// Fraction of stake that may be arbitrarily controlled by the adversary.
    pub byzantine: f64,
}

/// Test harness for quorum robustness testing.
pub struct QuorumRobustnessTest<S: SamplingStrategy> {
    sampler: RwLock<S>,
    quorum_sizes: Vec<usize>,
    attacks: Vec<QuorumAttack>,

    tests: RwLock<usize>,
    failures: RwLock<usize>,

    validators: Vec<ValidatorInfo>,
    total_stake: Stake,
    stake_distribution: String,
}

impl<S: SamplingStrategy + Send + Sync> QuorumRobustnessTest<S> {
    /// Creates a new instance of the test harness.
    pub fn new(
        validators: Vec<ValidatorInfo>,
        stake_distribution: String,
        sampler: S,
        quorum_sizes: Vec<usize>,
        attacks: Vec<QuorumAttack>,
    ) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let sampler = RwLock::new(sampler);
        let tests = RwLock::new(0);
        let failures = RwLock::new(0);

        Self {
            sampler,
            quorum_sizes,
            attacks,

            tests,
            failures,

            validators,
            total_stake,
            stake_distribution,
        }
    }

    /// Runs robustness test with an `attack_frac` fraction of stake corrupted.
    ///
    /// This runs the various strategies of choosing validators to corrupt.
    /// Returns the failure probability for the strongest adversary strategy.
    ///
    /// Results are written as a single line into `csv_file`.
    pub fn run(&self, adversary_strength: AdversaryStrength, csv_file: &mut csv::Writer<File>) {
        let mut attack_prob = 0.0;

        // try three different adversary strategies
        // let partition_failure_rate = self.run_bin_packing(attack_frac, attack_prob);
        // debug!("bin-packing failure rate: {}", partition_failure_rate);
        // self.reset();
        // attack_prob = attack_prob.max(parittion_failure_rate);

        let random_failure_rate = self.run_random(attack_frac, attack_prob);
        debug!("random failure rate: {random_failure_rate}");
        self.reset();
        attack_prob = attack_prob.max(random_failure_rate);

        let small_failure_rate = self.run_small(attack_frac, attack_prob);
        debug!("small failure rate: {small_failure_rate}");
        self.reset();
        attack_prob = small_failure_rate.max(attack_prob);

        let large_failure_rate = self.run_large(attack_frac, attack_prob);
        debug!("large failure rate: {large_failure_rate}");
        self.reset();
        attack_prob = attack_prob.max(large_failure_rate);

        // write results to CSV
        let stake_distribution = self.stake_distribution;
        let sampling_strategy = S::name();
        csv_file
            .write_record(&[
                stake_distribution,
                sampling_strategy.to_string(),
                attack_frac.to_string(),
                self.params().num_data_shreds.to_string(),
                self.params().num_shreds.to_string(),
                attack_prob.log2().to_string(),
            ])
            .unwrap();
        csv_file.flush().unwrap();
    }

    fn run_small(&self, attack_frac: f64, know_attack_prob: f64) -> f64 {
        debug!("running attack with small nodes corrupted");
        // corrupt `attack_frac` smallest validators
        let mut corrupted = vec![false; self.validators.len()];
        let mut validators_to_corrupt = self.validators.clone();
        validators_to_corrupt.sort_by_key(|v| v.stake);
        let mut corrupted_stake = 0.0;
        for v in &validators_to_corrupt {
            let rel_stake = v.stake as f64 / self.total_stake as f64;
            if corrupted_stake + rel_stake < attack_frac {
                corrupted[v.id as usize] = true;
                corrupted_stake += rel_stake;
            } else {
                break;
            }
        }
        (0..PARALLELISM).into_par_iter().for_each(|_| {
            for _ in 0..TOTAL_ITERATIONS / PARALLELISM / WRITE_BATCH {
                let (tests, done) =
                    self.run_with_corrupted(WRITE_BATCH, attack_frac == 0.2, &corrupted);
                *self.tests.write().unwrap() += tests;
                if done
                    || *self.tests.read().unwrap() as f64
                        > 3.0 * (*self.failures.read().unwrap() as f64) / know_attack_prob
                {
                    break;
                }
            }
        });
        *self.failures.read().unwrap() as f64 / *self.tests.read().unwrap() as f64
    }

    fn run_large(&self, attack_frac: f64, know_attack_prob: f64) -> f64 {
        debug!("running attack with large nodes corrupted");
        // corrupt `attack_frac` largest validators
        let mut corrupted = vec![false; self.validators.len()];
        let mut validators_to_corrupt = self.validators.clone();
        validators_to_corrupt.sort_by_key(|v| -(v.stake as i64));
        let mut corrupted_stake = 0.0;
        for v in &validators_to_corrupt {
            let rel_stake = v.stake as f64 / self.total_stake as f64;
            if corrupted_stake + rel_stake < attack_frac {
                corrupted[v.id as usize] = true;
                corrupted_stake += rel_stake;
            }
        }
        (0..PARALLELISM).into_par_iter().for_each(|_| {
            for _ in 0..TOTAL_ITERATIONS / PARALLELISM / WRITE_BATCH {
                let (tests, done) =
                    self.run_with_corrupted(WRITE_BATCH, attack_frac == 0.2, &corrupted);
                *self.tests.write().unwrap() += tests;
                if done
                    || *self.tests.read().unwrap() as f64
                        > 3.0 * (*self.failures.read().unwrap() as f64) / know_attack_prob
                {
                    break;
                }
            }
        });
        *self.failures.read().unwrap() as f64 / *self.tests.read().unwrap() as f64
    }

    fn run_random(&self, attack_frac: f64, know_attack_prob: f64) -> f64 {
        debug!("running attack with random nodes corrupted");
        (0..PARALLELISM).into_par_iter().for_each(|_| {
            // greedily corrupt less than `attack_frac` of validators
            let mut corrupted = vec![false; self.validators.len()];
            let mut validators_to_corrupt = self.validators.clone();
            let mut corrupted_stake = 0.0;
            validators_to_corrupt.shuffle(&mut rand::rng());

            for v in &validators_to_corrupt {
                let rel_stake = v.stake as f64 / self.total_stake as f64;
                if corrupted_stake + rel_stake < attack_frac {
                    corrupted[v.id as usize] = true;
                    corrupted_stake += rel_stake;
                }
            }

            for _ in 0..TOTAL_ITERATIONS / PARALLELISM / WRITE_BATCH {
                let (tests, done) =
                    self.run_with_corrupted(WRITE_BATCH, attack_frac == 0.2, &corrupted);
                *self.tests.write().unwrap() += tests;
                if done
                    || *self.tests.read().unwrap() as f64
                        > 3.0 * (*self.failures.read().unwrap() as f64) / know_attack_prob
                {
                    break;
                }
            }
        });
        *self.failures.read().unwrap() as f64 / *self.tests.read().unwrap() as f64
    }

    fn _run_bin_packing(&self, attack_frac: f64, know_attack_prob: f64) -> f64 {
        debug!("running attack with bin-packing attack");
        let fa1_sampler = FaitAccompli1Sampler::new_with_partition_fallback(
            self.validators.clone(),
            self.quorum_size as u64,
        );
        let bin_sampler = fa1_sampler.fallback_sampler;
        let vals = &bin_sampler.bin_validators;
        let stakes = &bin_sampler.bin_stakes;
        let attack_frac_in_bins = attack_frac / (vals.len() as f64 / self.quorum_size as f64);
        let stake_per_bin = self.total_stake as f64 / self.quorum_size as f64;

        (0..PARALLELISM).into_par_iter().for_each(|_| {
            // greedily corrupt less than `attack_frac` of validators
            // evenly spread over the bins!
            let mut corrupted = vec![false; self.validators.len()];
            let mut total_corrupted_stake = 0.0;

            for bin in 0..vals.len() {
                let mut corrupted_stake = 0.0;
                let mut entries: Vec<_> = stakes[bin].iter().zip(vals[bin].iter()).collect();
                entries.sort_by_key(|(s, _)| **s);
                for (stake, id) in &entries {
                    if corrupted[**id as usize] {
                        corrupted_stake += **stake as f64;
                    }
                }
                for (stake, id) in entries {
                    let val_stake = self.validators[*id as usize].stake as f64;
                    if corrupted[*id as usize] {
                        continue;
                    } else if corrupted_stake + (*stake as f64)
                        < stake_per_bin * attack_frac_in_bins
                        // && val_stake < stake_per_bin
                        && total_corrupted_stake + val_stake < self.total_stake as f64 * attack_frac
                    {
                        corrupted[*id as usize] = true;
                        corrupted_stake += *stake as f64;
                        total_corrupted_stake += val_stake;
                    }
                }
            }
            assert!(total_corrupted_stake < self.total_stake as f64 * attack_frac);

            for _ in 0..TOTAL_ITERATIONS / PARALLELISM / WRITE_BATCH {
                let (tests, done) =
                    self.run_with_corrupted(WRITE_BATCH, attack_frac == 0.2, &corrupted);
                *self.tests.write().unwrap() += tests;
                let better_attack_known = *self.tests.read().unwrap() as f64
                    > 3.0 * (*self.failures.read().unwrap() as f64) / know_attack_prob;
                if done || better_attack_known {
                    break;
                }
            }
        });
        *self.failures.read().unwrap() as f64 / *self.tests.read().unwrap() as f64
    }

    fn run_with_corrupted(
        &self,
        iterations: usize,
        byzantine: &[bool],
        crashed: &[bool],
    ) -> (usize, bool) {
        let mut rng = SmallRng::from_rng(&mut rand::rng());
        let mut tests = 0;
        let sampler = &self.sampler;
        for _ in 0..iterations {
            tests += 1;
            for _ in 0..self.params().num_slices {
                let sampled = sampler.sample_multiple(self.quorum_size, &mut rng);
                let byzantine_samples = sampled
                    .into_iter()
                    .filter(|v| byzantine[*v as usize])
                    .count();
                if (!byzantine
                    && corrupted_samples > self.params().num_shreds - self.params().num_data_shreds)
                    || (byzantine && corrupted_samples >= self.params().num_data_shreds)
                {
                    *self.failures.write().unwrap() += 1;
                    break;
                }
                if *self.failures.read().unwrap() >= MAX_FAILURES {
                    return (tests, true);
                }
            }
        }
        (tests, false)
    }

    fn reset(&self) {
        *self.tests.write().unwrap() = 0;
        *self.failures.write().unwrap() = 0;
    }
}

pub struct QuorumAttack {
    pub name: String,
    pub quorum: QuorumThreshold,
}

pub enum QuorumThreshold {
    Simple {
        quorum: usize,
        threshold: usize,
        is_crash_enough: bool,
    },
    All(Vec<QuorumThreshold>),
    Any(Vec<QuorumThreshold>),
}
