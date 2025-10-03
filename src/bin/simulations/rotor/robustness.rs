// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Calculations about the robustness of the Rotor block dissemination protocol.
//!
//! This implements two main attack scenarios:
//! - Equivocation attack: Less than 20% of stake is Byzantine.
//! - Censorship attack: Up to 40% of stake is crashed.
//!
//!

use std::fs::File;
use std::sync::RwLock;

use alpenglow::disseminator::rotor::sampling_strategy::UniformSampler;
use alpenglow::disseminator::rotor::{FaitAccompli1Sampler, SamplingStrategy};
use alpenglow::{Stake, ValidatorInfo};
use log::debug;
use rand::prelude::*;
use rayon::prelude::*;

use super::RotorParams;
use crate::rotor::RotorInstanceBuilder;

/// Simulations stop early if the number of failures is greater than this.
const MAX_FAILURES: usize = 10_000;

/// Test harness for Rotor robustness testing.
pub struct RotorRobustnessTest<S: SamplingStrategy> {
    validators: Vec<ValidatorInfo>,
    total_stake: Stake,
    builder: RotorInstanceBuilder<UniformSampler, S>,

    tests: RwLock<usize>,
    failures: RwLock<usize>,
}

impl<S: SamplingStrategy + Send + Sync> RotorRobustnessTest<S> {
    /// Creates a new instance of the test harness.
    pub fn new(
        validators: Vec<ValidatorInfo>,
        sampler: S,
        num_data_shreds: usize,
        num_shreds: usize,
    ) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let tests = RwLock::new(0);
        let failures = RwLock::new(0);
        // let sampler = RwLock::new(sampler);

        let params = RotorParams {
            num_data_shreds,
            num_shreds,
            num_slices: 1,
        };

        let builder =
            RotorInstanceBuilder::new(UniformSampler::new(validators.clone()), sampler, params);

        Self {
            validators,
            total_stake,
            builder,

            tests,
            failures,
        }
    }

    /// Runs robustness test with an `attack_frac` fraction of stake corrupted.
    ///
    /// This runs the various strategies of choosing validators to corrupt.
    /// Returns the failure probability for the strongest adversary strategy.
    ///
    /// The `test_name` should be of the form "<stake-distribution>-<sampling-strategy>".
    /// Results are written as a single line into to `csv_file`.
    pub fn run(&self, test_name: &str, attack_frac: f64, csv_file: &mut csv::Writer<File>) {
        let mut attack_prob = 0.0;

        // try three different adversary strategies
        // let partition_failure_rate = self.run_bin_packing(attack_frac, attack_prob);
        // debug!("bin-packing failure rate: {}", partition_failure_rate);
        // *self.tests.write().unwrap() = 0;
        // *self.failures.write().unwrap() = 0;
        // attack_prob = attack_prob.max(parittion_failure_rate);

        let random_failure_rate = self.run_random(attack_frac, attack_prob);
        debug!("random failure rate: {random_failure_rate}");
        *self.tests.write().unwrap() = 0;
        *self.failures.write().unwrap() = 0;
        attack_prob = attack_prob.max(random_failure_rate);

        let small_failure_rate = self.run_small(attack_frac, attack_prob);
        debug!("small failure rate: {small_failure_rate}");
        *self.tests.write().unwrap() = 0;
        *self.failures.write().unwrap() = 0;
        attack_prob = small_failure_rate.max(attack_prob);

        let large_failure_rate = self.run_large(attack_frac, attack_prob);
        debug!("large failure rate: {large_failure_rate}");
        *self.tests.write().unwrap() = 0;
        *self.failures.write().unwrap() = 0;
        attack_prob = attack_prob.max(large_failure_rate);

        // write results to CSV
        let parts = test_name.split('-').collect::<Vec<_>>();
        let stake_distribution = parts[0];
        let sampling_strategy = parts[1];
        csv_file
            .write_record(&[
                stake_distribution.to_string(),
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
        (0..1000).into_par_iter().for_each(|_| {
            for _ in 0..100_000 {
                let (tests, done) = self.run_with_corrupted(1000, attack_frac == 0.2, &corrupted);
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
        (0..1000).into_par_iter().for_each(|_| {
            for _ in 0..100_000 {
                let (tests, done) = self.run_with_corrupted(1000, attack_frac == 0.2, &corrupted);
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
        (0..1000).into_par_iter().for_each(|_| {
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

            for _ in 0..100_000 {
                let (tests, done) = self.run_with_corrupted(1000, attack_frac == 0.2, &corrupted);
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
            self.params().num_shreds as u64,
        );
        let bin_sampler = fa1_sampler.fallback_sampler;
        let vals = &bin_sampler.bin_validators;
        let stakes = &bin_sampler.bin_stakes;
        let attack_frac_in_bins =
            attack_frac / (vals.len() as f64 / self.params().num_shreds as f64);
        let stake_per_bin = self.total_stake as f64 / self.params().num_shreds as f64;

        (0..1000).into_par_iter().for_each(|_| {
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

            for _ in 0..100_000 {
                let (tests, done) = self.run_with_corrupted(1000, attack_frac == 0.2, &corrupted);
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

    fn run_with_corrupted(&self, n: usize, byzantine: bool, corrupted: &[bool]) -> (usize, bool) {
        let mut rng = SmallRng::from_rng(&mut rand::rng());
        let mut tests = 0;
        let sampler = &self.builder.rotor_sampler;
        for _ in 0..n {
            tests += 1;
            for _ in 0..self.params().num_slices {
                let sampled = sampler.sample_multiple(self.params().num_shreds, &mut rng);
                let corrupted_samples = sampled
                    .into_iter()
                    .filter(|v| corrupted[*v as usize])
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

    fn params(&self) -> &RotorParams {
        &self.builder.params
    }
}
