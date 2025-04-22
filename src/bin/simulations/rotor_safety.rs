use std::collections::HashSet;
use std::sync::{Mutex, RwLock};

use alpenglow::ValidatorId;
use alpenglow::{Stake, ValidatorInfo, disseminator::rotor::SamplingStrategy};
use log::info;
use rand::prelude::*;
use rayon::prelude::*;

pub struct RotorSafetyTest<S: SamplingStrategy + Sync + Send> {
    validators: Vec<ValidatorInfo>,
    total_stake: Stake,
    sampler: RwLock<S>,
    num_shreds: usize,

    tests: Mutex<usize>,
    failures: RwLock<usize>,
}

impl<S: SamplingStrategy + Sync + Send> RotorSafetyTest<S> {
    pub fn new(validators: Vec<ValidatorInfo>, sampler: S, num_shreds: usize) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let tests = Mutex::new(0);
        let failures = RwLock::new(0);
        let sampler = RwLock::new(sampler);
        Self {
            validators,
            total_stake,
            sampler,
            num_shreds,

            tests,
            failures,
        }
    }

    pub fn run(&self) {
        let small_failure_rate = self.run_small();
        let large_failure_rate = self.run_large();
        let random_failure_rate = self.run_random();
        let attack_prob = small_failure_rate
            .min(large_failure_rate)
            .min(random_failure_rate);

        info!(
            "{:<3} shreds, attack prob [log2]: {:.3}",
            self.num_shreds,
            attack_prob.log2(),
        );
    }

    fn run_small(&self) -> f64 {
        // corrupt 40% smallest validators
        let mut corrupted = HashSet::new();
        let mut validators_to_corrupt = self.validators.clone();
        validators_to_corrupt.sort_by_key(|v| v.stake);
        let mut corrupted_stake = 0.0;
        for v in &validators_to_corrupt {
            let rel_stake = v.stake as f64 / self.total_stake as f64;
            if corrupted_stake + rel_stake < 0.2 {
                corrupted.insert(v.id);
                corrupted_stake += rel_stake;
            } else {
                break;
            }
        }
        (0..100_000).into_par_iter().for_each(|_| {
            self.run_with_corrupted(100_000, &corrupted);
        });
        *self.failures.read().unwrap() as f64 / *self.tests.lock().unwrap() as f64
    }

    fn run_large(&self) -> f64 {
        // corrupt 40% largest validators
        let mut corrupted = HashSet::new();
        let mut validators_to_corrupt = self.validators.clone();
        validators_to_corrupt.sort_by_key(|v| -(v.stake as i64));
        let mut corrupted_stake = 0.0;
        for v in &validators_to_corrupt {
            let rel_stake = v.stake as f64 / self.total_stake as f64;
            if corrupted_stake + rel_stake < 0.2 {
                corrupted.insert(v.id);
                corrupted_stake += rel_stake;
            } else {
                break;
            }
        }
        (0..100_000).into_par_iter().for_each(|_| {
            self.run_with_corrupted(100_000, &corrupted);
        });
        *self.failures.read().unwrap() as f64 / *self.tests.lock().unwrap() as f64
    }

    fn run_random(&self) -> f64 {
        (0..100_000).into_par_iter().for_each(|_| {
            // greedily corrupt less than 40% of validators
            let mut corrupted = HashSet::new();
            let mut validators_to_corrupt = self.validators.clone();
            let mut corrupted_stake = 0.0;
            validators_to_corrupt.shuffle(&mut rand::rng());

            for v in &validators_to_corrupt {
                let rel_stake = v.stake as f64 / self.total_stake as f64;
                if corrupted_stake + rel_stake < 0.2 {
                    corrupted.insert(v.id);
                    corrupted_stake += rel_stake;
                }
            }

            self.run_with_corrupted(100_000, &corrupted);
        });
        *self.failures.read().unwrap() as f64 / *self.tests.lock().unwrap() as f64
    }

    fn run_with_corrupted(&self, n: usize, corrupted: &HashSet<ValidatorId>) {
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
        for _ in 0..n {
            let sampler = self.sampler.read().unwrap();
            let sampled = sampler.sample_multiple(self.num_shreds, &mut rng);
            let mut corrupted_samples = 0;
            for v in sampled {
                if corrupted.contains(&v.id) {
                    corrupted_samples += 1;
                }
            }
            *self.tests.lock().unwrap() += 1;
            if corrupted_samples > self.num_shreds - 32 {
                let mut failures = self.failures.write().unwrap();
                *failures += 1;
            }
            if *self.failures.read().unwrap() >= 1 {
                return;
            }
        }
    }
}
