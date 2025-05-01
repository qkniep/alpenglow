// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//!
//!
//!

use std::collections::BTreeSet;
use std::fs::File;
use std::sync::RwLock;

use alpenglow::ValidatorId;
use alpenglow::{Stake, ValidatorInfo, disseminator::rotor::SamplingStrategy};
use log::debug;
use rand::prelude::*;
use rayon::prelude::*;

///
pub struct RotorSafetyTest<S: SamplingStrategy + Sync + Send> {
    validators: Vec<ValidatorInfo>,
    total_stake: Stake,
    sampler: RwLock<S>,
    num_data_shreds: usize,
    num_shreds: usize,

    tests: RwLock<usize>,
    failures: RwLock<usize>,
}

impl<S: SamplingStrategy + Sync + Send> RotorSafetyTest<S> {
    ///
    pub fn new(
        validators: Vec<ValidatorInfo>,
        sampler: S,
        num_data_shreds: usize,
        num_shreds: usize,
    ) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let tests = RwLock::new(0);
        let failures = RwLock::new(0);
        let sampler = RwLock::new(sampler);
        Self {
            validators,
            total_stake,
            sampler,
            num_data_shreds,
            num_shreds,

            tests,
            failures,
        }
    }

    ///
    pub fn run(&self, test_name: &str, attack_frac: f64, csv_file: &mut csv::Writer<File>) {
        let small_failure_rate = self.run_small(attack_frac);
        debug!("small failure rate: {}", small_failure_rate);
        *self.tests.write().unwrap() = 0;
        *self.failures.write().unwrap() = 0;

        let large_failure_rate = self.run_large(attack_frac);
        debug!("large failure rate: {}", large_failure_rate);
        *self.tests.write().unwrap() = 0;
        *self.failures.write().unwrap() = 0;

        let random_failure_rate = self.run_random(attack_frac);
        debug!("random failure rate: {}", random_failure_rate);
        *self.tests.write().unwrap() = 0;
        *self.failures.write().unwrap() = 0;

        let attack_prob = small_failure_rate
            .max(large_failure_rate)
            .max(random_failure_rate);

        let parts = test_name.split('-').collect::<Vec<_>>();
        let stake_distribution = parts[0];
        let sampling_strategy = parts[1];

        csv_file
            .write_record(&[
                stake_distribution.to_string(),
                sampling_strategy.to_string(),
                attack_frac.to_string(),
                self.num_data_shreds.to_string(),
                self.num_shreds.to_string(),
                attack_prob.log2().to_string(),
            ])
            .unwrap();
        csv_file.flush().unwrap();
    }

    fn run_small(&self, attack_frac: f64) -> f64 {
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
        (0..100_000).into_par_iter().for_each(|_| {
            self.run_with_corrupted(100_000, attack_frac == 0.2, &corrupted);
        });
        *self.failures.read().unwrap() as f64 / *self.tests.read().unwrap() as f64
    }

    fn run_large(&self, attack_frac: f64) -> f64 {
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
            } else {
                break;
            }
        }
        (0..100_000).into_par_iter().for_each(|_| {
            self.run_with_corrupted(100_000, attack_frac == 0.2, &corrupted);
        });
        *self.failures.read().unwrap() as f64 / *self.tests.read().unwrap() as f64
    }

    fn run_random(&self, attack_frac: f64) -> f64 {
        debug!("running attack with random nodes corrupted");
        (0..100_000).into_par_iter().for_each(|_| {
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

            self.run_with_corrupted(100_000, attack_frac == 0.2, &corrupted);
        });
        *self.failures.read().unwrap() as f64 / *self.tests.read().unwrap() as f64
    }

    fn run_with_corrupted(&self, n: usize, byzantine: bool, corrupted: &[bool]) {
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
        for _ in 0..n {
            let sampler = self.sampler.read().unwrap();
            let sampled = sampler.sample_multiple(self.num_shreds, &mut rng);
            let mut corrupted_samples = 0;
            for v in sampled {
                if corrupted[v as usize] {
                    corrupted_samples += 1;
                }
            }
            *self.tests.write().unwrap() += 1;
            if (!byzantine && corrupted_samples > self.num_shreds - self.num_data_shreds)
                || (byzantine && corrupted_samples > self.num_data_shreds)
            {
                let mut failures = self.failures.write().unwrap();
                *failures += 1;
            }
            if *self.failures.read().unwrap() >= 3 {
                return;
            }
        }
    }
}
