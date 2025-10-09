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

use std::cmp::Reverse;
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
    failures: RwLock<Vec<usize>>,

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
        let failures = RwLock::new(vec![0; attacks.len()]);

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
        let mut attack_probs = vec![0.0; self.attacks.len()];

        // try three different adversary strategies
        // let partition_failure_rate = self.run_bin_packing(adversary_strength, attack_probs);
        // debug!("bin-packing failure rates:");
        // for (attack, prob) in self.attacks.iter().zip(partition_failure_rate.iter()) {
        //     debug!("  - {}: {:.1}%", attack.name, prob);
        // }
        // self.reset();
        // attack_prob = attack_prob.max(parittion_failure_rate);

        let random_attack_probs = self.run_random(adversary_strength, &attack_probs);
        debug!("random failure rates:");
        for (attack, prob) in self.attacks.iter().zip(random_attack_probs.iter()) {
            debug!("  - {}: {:.1}%", attack.name, prob);
        }
        self.reset();
        // attack_prob = attack_prob.max(random_failure_rate);

        let small_attack_probs = self.run_small(adversary_strength, &attack_probs);
        debug!("small failure rates:");
        for (attack, prob) in self.attacks.iter().zip(small_attack_probs.iter()) {
            debug!("  - {}: {:.1}%", attack.name, prob);
        }
        self.reset();
        // attack_prob = small_failure_rate.max(attack_prob);

        let large_attack_porbs = self.run_large(adversary_strength, &attack_probs);
        debug!("large failure rate:");
        for (attack, prob) in self.attacks.iter().zip(large_attack_porbs.iter()) {
            debug!("  - {}: {:.1}%", attack.name, prob);
        }
        self.reset();
        // attack_prob = attack_prob.max(large_failure_rate);

        // write results to CSV
        let sampling_strategy = S::name();
        let mut row = vec![
            self.stake_distribution.clone(),
            sampling_strategy.to_string(),
            adversary_strength.byzantine.to_string(),
            adversary_strength.crashed.to_string(),
            // self.params().num_data_shreds.to_string(),
            // self.params().num_shreds.to_string(),
        ];
        for attack_prob in &attack_probs {
            row.push(attack_prob.log2().to_string());
        }
        csv_file.write_record(&row).unwrap();
        csv_file.flush().unwrap();
    }

    fn run_small(
        &self,
        adversary_strength: AdversaryStrength,
        known_attack_probs: &[f64],
    ) -> Vec<f64> {
        debug!("running attack with small nodes corrupted");
        let mut byzantine = vec![false; self.validators.len()];
        let mut crashed = vec![false; self.validators.len()];
        let mut validators_to_corrupt = self.validators.clone();
        validators_to_corrupt.sort_by_key(|v| v.stake);

        // corrupt smallest validators (first byzantine, then crashed)
        let mut byzantine_stake = 0.0;
        let mut crashed_stake = 0.0;
        for v in &validators_to_corrupt {
            let rel_stake = v.stake as f64 / self.total_stake as f64;
            if byzantine_stake + rel_stake < adversary_strength.byzantine {
                byzantine[v.id as usize] = true;
                byzantine_stake += rel_stake;
            } else if crashed_stake + rel_stake < adversary_strength.crashed {
                crashed[v.id as usize] = true;
                crashed_stake += rel_stake;
            } else {
                break;
            }
        }

        // run tests
        (0..PARALLELISM).into_par_iter().for_each(|_| {
            for _ in 0..TOTAL_ITERATIONS / PARALLELISM / WRITE_BATCH {
                let (tests, hit_max_failures) =
                    self.run_with_corrupted(WRITE_BATCH, &byzantine, &crashed);
                *self.tests.write().unwrap() += tests;
                if hit_max_failures
                // || *self.tests.read().unwrap() as f64
                //     > 3.0 * (*self.failures.read().unwrap() as f64) / know_attack_prob
                {
                    break;
                }
            }
        });

        self.attack_probabilities()
    }

    fn run_large(
        &self,
        adversary_strength: AdversaryStrength,
        known_attack_probs: &[f64],
    ) -> Vec<f64> {
        debug!("running attack with large nodes corrupted");
        let mut byzantine = vec![false; self.validators.len()];
        let mut crashed = vec![false; self.validators.len()];
        let mut validators_to_corrupt = self.validators.clone();
        validators_to_corrupt.sort_by_key(|v| Reverse(v.stake));

        // corrupt largest validators (first byzantine, then crashed)
        let mut byzantine_stake = 0.0;
        let mut crashed_stake = 0.0;
        for v in &validators_to_corrupt {
            let rel_stake = v.stake as f64 / self.total_stake as f64;
            if byzantine_stake + rel_stake < adversary_strength.byzantine {
                byzantine[v.id as usize] = true;
                byzantine_stake += rel_stake;
            } else if crashed_stake + rel_stake < adversary_strength.crashed {
                crashed[v.id as usize] = true;
                crashed_stake += rel_stake;
            } else {
                break;
            }
        }

        // run tests
        (0..PARALLELISM).into_par_iter().for_each(|_| {
            for _ in 0..TOTAL_ITERATIONS / PARALLELISM / WRITE_BATCH {
                let (tests, hit_max_failures) =
                    self.run_with_corrupted(WRITE_BATCH, &byzantine, &crashed);
                *self.tests.write().unwrap() += tests;
                if hit_max_failures
                // || *self.tests.read().unwrap() as f64
                //     > 3.0 * (*self.failures.read().unwrap() as f64) / know_attack_prob
                {
                    break;
                }
            }
        });

        self.attack_probabilities()
    }

    fn run_random(
        &self,
        adversary_strength: AdversaryStrength,
        known_attack_probs: &[f64],
    ) -> Vec<f64> {
        debug!("running attack with random nodes corrupted");
        (0..PARALLELISM).into_par_iter().for_each(|_| {
            let mut byzantine = vec![false; self.validators.len()];
            let mut crashed = vec![false; self.validators.len()];
            let mut validators_to_corrupt = self.validators.clone();
            validators_to_corrupt.shuffle(&mut rand::rng());

            // greedily corrupt validators (prioritizing byzantine)
            let mut byzantine_stake = 0.0;
            let mut crashed_stake = 0.0;
            for v in &validators_to_corrupt {
                let rel_stake = v.stake as f64 / self.total_stake as f64;
                if byzantine_stake + rel_stake < adversary_strength.byzantine {
                    byzantine[v.id as usize] = true;
                    byzantine_stake += rel_stake;
                } else if crashed_stake + rel_stake < adversary_strength.crashed {
                    crashed[v.id as usize] = true;
                    crashed_stake += rel_stake;
                }
            }

            // run tests
            for _ in 0..TOTAL_ITERATIONS / PARALLELISM / WRITE_BATCH {
                let (tests, hit_max_failures) =
                    self.run_with_corrupted(WRITE_BATCH, &byzantine, &crashed);
                *self.tests.write().unwrap() += tests;
                // let better_attack_known = *self.tests.read().unwrap() as f64
                //     > 3.0 * (*self.failures.read().unwrap() as f64) / know_attack_prob;
                if hit_max_failures
                // || better_attack_known
                {
                    break;
                }
            }
        });
        self.attack_probabilities()
    }

    // fn _run_bin_packing(
    //     &self,
    //     adversary_strength: AdversaryStrength,
    //     known_attack_probs: &[f64],
    // ) -> Vec<f64> {
    //     debug!("running attack with bin-packing attack");
    //     let fa1_sampler = FaitAccompli1Sampler::new_with_partition_fallback(
    //         self.validators.clone(),
    //         self.quorum_size as u64,
    //     );
    //     let bin_sampler = fa1_sampler.fallback_sampler;
    //     let vals = &bin_sampler.bin_validators;
    //     let stakes = &bin_sampler.bin_stakes;
    //     let attack_frac_in_bins = attack_frac / (vals.len() as f64 / self.quorum_size as f64);
    //     let stake_per_bin = self.total_stake as f64 / self.quorum_size as f64;
    //
    //     (0..PARALLELISM).into_par_iter().for_each(|_| {
    //         // greedily corrupt less than `attack_frac` of validators
    //         // evenly spread over the bins!
    //         let mut corrupted = vec![false; self.validators.len()];
    //         let mut total_corrupted_stake = 0.0;
    //
    //         for bin in 0..vals.len() {
    //             let mut corrupted_stake = 0.0;
    //             let mut entries: Vec<_> = stakes[bin].iter().zip(vals[bin].iter()).collect();
    //             entries.sort_by_key(|(s, _)| **s);
    //             for (stake, id) in &entries {
    //                 if corrupted[**id as usize] {
    //                     corrupted_stake += **stake as f64;
    //                 }
    //             }
    //             for (stake, id) in entries {
    //                 let val_stake = self.validators[*id as usize].stake as f64;
    //                 if corrupted[*id as usize] {
    //                     continue;
    //                 } else if corrupted_stake + (*stake as f64)
    //                     < stake_per_bin * attack_frac_in_bins
    //                     // && val_stake < stake_per_bin
    //                     && total_corrupted_stake + val_stake < self.total_stake as f64 * attack_frac
    //                 {
    //                     corrupted[*id as usize] = true;
    //                     corrupted_stake += *stake as f64;
    //                     total_corrupted_stake += val_stake;
    //                 }
    //             }
    //         }
    //         assert!(total_corrupted_stake < self.total_stake as f64 * attack_frac);
    //
    //         for _ in 0..TOTAL_ITERATIONS / PARALLELISM / WRITE_BATCH {
    //             let (tests, hit_max_failures) =
    //                 self.run_with_corrupted(WRITE_BATCH, attack_frac == 0.2, &corrupted);
    //             *self.tests.write().unwrap() += tests;
    //             // let better_attack_known = *self.tests.read().unwrap() as f64
    //             //     > 3.0 * (*self.failures.read().unwrap() as f64) / know_attack_prob;
    //             if hit_max_failures
    //             // || better_attack_known
    //             {
    //                 break;
    //             }
    //         }
    //     });
    //     self.attack_probabilities()
    // }

    fn run_with_corrupted(
        &self,
        iterations: usize,
        byzantine: &[bool],
        crashed: &[bool],
    ) -> (usize, bool) {
        let mut rng = SmallRng::from_rng(&mut rand::rng());
        let mut tests = 0;
        let sampler = &self.sampler.read().unwrap();
        for _ in 0..iterations {
            tests += 1;
            let corrupted = self
                .quorum_sizes
                .iter()
                .copied()
                .map(|quorum_size| {
                    let sampled = sampler.sample_multiple(quorum_size, &mut rng);
                    let byzantine_samples =
                        sampled.iter().filter(|v| byzantine[**v as usize]).count();
                    let crashed_samples = sampled.iter().filter(|v| crashed[**v as usize]).count();
                    (byzantine_samples, crashed_samples)
                })
                .collect::<Vec<_>>();
            for (attack_index, attack) in self.attacks.iter().enumerate() {
                if attack.evaluate(&corrupted) {
                    let attack_failures = &mut self.failures.write().unwrap()[attack_index];
                    *attack_failures += 1;
                    if *attack_failures >= MAX_FAILURES {
                        return (tests, true);
                    }
                }
            }
        }
        (tests, false)
    }

    fn attack_probabilities(&self) -> Vec<f64> {
        (0..self.attacks.len())
            .map(|i| self.failures.read().unwrap()[i] as f64 / *self.tests.read().unwrap() as f64)
            .collect()
    }

    fn reset(&self) {
        *self.tests.write().unwrap() = 0;
        *self.failures.write().unwrap() = vec![0; self.attacks.len()];
    }
}

#[derive(Clone, Debug)]
pub struct QuorumAttack {
    pub name: String,
    pub quorum: QuorumThreshold,
}

impl QuorumAttack {
    fn evaluate(&self, corrupted: &[(usize, usize)]) -> bool {
        self.quorum.evaluate(corrupted)
    }
}

#[derive(Clone, Debug)]
pub enum QuorumThreshold {
    Simple {
        quorum: usize,
        threshold: usize,
        is_crash_enough: bool,
    },
    All(Vec<QuorumThreshold>),
    Any(Vec<QuorumThreshold>),
}

impl QuorumThreshold {
    fn evaluate(&self, corrupted: &[(usize, usize)]) -> bool {
        match self {
            QuorumThreshold::Simple {
                quorum,
                threshold,
                is_crash_enough,
            } => {
                let (byzantine, crashed) = corrupted[*quorum];
                if *is_crash_enough {
                    byzantine + crashed >= *threshold
                } else {
                    byzantine >= *threshold
                }
            }
            QuorumThreshold::All(thresholds) => thresholds
                .iter()
                .map(|threshold| threshold.evaluate(corrupted))
                .all(|b| b),
            QuorumThreshold::Any(thresholds) => thresholds
                .iter()
                .map(|threshold| threshold.evaluate(corrupted))
                .any(|b| b),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quorum_threshold() {
        let threshold1 = QuorumThreshold::Simple {
            quorum: 0,
            threshold: 1,
            is_crash_enough: false,
        };
        let threshold2 = QuorumThreshold::Simple {
            quorum: 1,
            threshold: 2,
            is_crash_enough: true,
        };
        let threshold_both = QuorumThreshold::All(vec![threshold1.clone(), threshold2.clone()]);
        let threshold_either = QuorumThreshold::Any(vec![threshold1.clone(), threshold2.clone()]);

        let corrupted = [(0, 0), (0, 0)];
        assert_eq!(threshold1.evaluate(&corrupted), false);
        assert_eq!(threshold2.evaluate(&corrupted), false);
        assert_eq!(threshold_both.evaluate(&corrupted), false);
        assert_eq!(threshold_either.evaluate(&corrupted), false);

        let corrupted = [(0, 1), (0, 0)];
        assert_eq!(threshold1.evaluate(&corrupted), false);
        assert_eq!(threshold2.evaluate(&corrupted), false);
        assert_eq!(threshold_both.evaluate(&corrupted), false);
        assert_eq!(threshold_either.evaluate(&corrupted), false);

        let corrupted = [(1, 0), (0, 0)];
        assert_eq!(threshold1.evaluate(&corrupted), true);
        assert_eq!(threshold2.evaluate(&corrupted), false);
        assert_eq!(threshold_both.evaluate(&corrupted), false);
        assert_eq!(threshold_either.evaluate(&corrupted), true);

        let corrupted = [(1, 0), (2, 0)];
        assert_eq!(threshold1.evaluate(&corrupted), true);
        assert_eq!(threshold2.evaluate(&corrupted), true);
        assert_eq!(threshold_both.evaluate(&corrupted), true);
        assert_eq!(threshold_either.evaluate(&corrupted), true);

        let corrupted = [(1, 0), (0, 2)];
        assert_eq!(threshold1.evaluate(&corrupted), true);
        assert_eq!(threshold2.evaluate(&corrupted), true);
        assert_eq!(threshold_both.evaluate(&corrupted), true);
        assert_eq!(threshold_either.evaluate(&corrupted), true);

        let corrupted = [(1, 0), (1, 1)];
        assert_eq!(threshold1.evaluate(&corrupted), true);
        assert_eq!(threshold2.evaluate(&corrupted), true);
        assert_eq!(threshold_both.evaluate(&corrupted), true);
        assert_eq!(threshold_either.evaluate(&corrupted), true);
    }
}
