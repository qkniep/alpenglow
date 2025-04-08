// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::sync::Mutex;

use rand::distr::weighted::WeightedIndex;
use rand::prelude::*;

use crate::{Stake, ValidatorInfo};

const MAX_TRIES_PER_SAMPLE: usize = 100_000;

/// An abstraction for randomly sampling validators based on some distribution.
pub trait SamplingStrategy {
    fn sample(&self, rng: &mut dyn rand::RngCore) -> &ValidatorInfo;

    fn sample_multiple(&self, k: usize, rng: &mut dyn rand::RngCore) -> Vec<ValidatorInfo> {
        (0..k).map(|_| self.sample(rng)).cloned().collect()
    }
}

/// A basic sampler that picks all validators with equal probability.
pub struct UniformSampler {
    validators: Vec<ValidatorInfo>,
}

impl UniformSampler {
    pub const fn new(validators: Vec<ValidatorInfo>) -> Self {
        Self { validators }
    }
}

impl SamplingStrategy for UniformSampler {
    fn sample(&self, rng: &mut dyn rand::RngCore) -> &ValidatorInfo {
        let index = rng.random_range(0..self.validators.len());
        &self.validators[index]
    }
}

/// A sampler that picks validators directly proportional to their stake.
pub struct StakeWeightedSampler {
    validators: Vec<ValidatorInfo>,
    stake_index: WeightedIndex<u64>,
}

impl StakeWeightedSampler {
    pub fn new(validators: Vec<ValidatorInfo>) -> Self {
        let stakes: Vec<u64> = validators.iter().map(|v| v.stake).collect();
        let stake_index = WeightedIndex::new(&stakes).unwrap();
        Self {
            validators,
            stake_index,
        }
    }
}

impl SamplingStrategy for StakeWeightedSampler {
    fn sample(&self, rng: &mut dyn rand::RngCore) -> &ValidatorInfo {
        let index = self.stake_index.sample(rng);
        &self.validators[index]
    }
}

/// A hybrid sampler between weighted sampling with and without replacement.
///
/// Any element is sample at most `ceil(max_samples)` times.
/// Elements are rejected with probability proportional to `k / max_samples`,
/// where `k` is how often the element has been sampled before.
/// Sampling differs between, e.g., `max_samples = 2` and `max_samples = 2.5`.
///
/// - For `max_samples = 1` it is stake-weighted sampling WITHOUT replacement.
/// - For `max_samples -> inf` it approaches the behavior WITH replacement.
pub struct DecayingAcceptanceSampler {
    stake_weighted: StakeWeightedSampler,
    max_samples: f64,
    sample_count: Mutex<Vec<usize>>,
}

impl DecayingAcceptanceSampler {
    pub fn new(validators: Vec<ValidatorInfo>, max_samples: f64) -> Self {
        let sample_count = vec![0; validators.len()];
        Self {
            stake_weighted: StakeWeightedSampler::new(validators),
            max_samples,
            sample_count: Mutex::new(sample_count),
        }
    }

    /// Resets the internal state of this stateful sampler.
    /// After resetting it is just as it was when it was first created.
    pub fn reset(&self) {
        let mut sample_count = self.sample_count.lock().unwrap();
        *sample_count = vec![0; self.stake_weighted.validators.len()];
    }
}

impl SamplingStrategy for DecayingAcceptanceSampler {
    fn sample(&self, rng: &mut dyn rand::RngCore) -> &ValidatorInfo {
        for _ in 0..MAX_TRIES_PER_SAMPLE {
            let sample = self.stake_weighted.sample(rng);
            let mut sample_count = self.sample_count.lock().unwrap();
            let p_reject = sample_count[sample.id as usize] as f64 / self.max_samples;
            if rng.random::<f64>() >= p_reject {
                sample_count[sample.id as usize] += 1;
                return sample;
            }
        }

        panic!("rejected all {MAX_TRIES_PER_SAMPLE} samples");
    }
}

/// A sampler that simulates the probability distribution in Turbine for Rotor.
///
/// The goal is to distribute the required work for validators as in Turbine.
/// Specifically, it should respect the same upper bound on the amount of work,
/// that is, for `v` validators and given `turbine_fanout` any validator should
/// be sampled no more than with probability `turbine_fanout / v`.
pub struct TurbineSampler {
    stake_weighted: StakeWeightedSampler,
    /// Specific fanout of the Turbine tree we want to simulate.
    turbine_fanout: usize,
}

impl TurbineSampler {
    // FIXME: broken
    // TODO: support more than 2 levels of Turbine
    pub fn new(mut validators: Vec<ValidatorInfo>, turbine_fanout: usize) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let expected_work: Vec<_> = validators
            .iter()
            .map(|v| {
                let root_prob = v.stake as f64 / total_stake as f64;
                let root_work = root_prob * (turbine_fanout as f64).max(validators.len() as f64);
                let mut level1_prob = (1.0 - root_prob) * root_prob;
                let mut level1_work = 0.0;
                for pos in 0..turbine_fanout {
                    level1_work += level1_prob
                        * (turbine_fanout as f64)
                            .min((validators.len().saturating_sub(turbine_fanout * pos)) as f64);
                    level1_prob *= 1.0 - root_prob;
                }
                root_work + level1_work
            })
            .collect();
        for (i, w) in expected_work.iter().enumerate() {
            validators[i].stake = (w * 1_000_000_000.0) as Stake;
        }

        Self {
            stake_weighted: StakeWeightedSampler::new(validators),
            turbine_fanout,
        }
    }
}

impl SamplingStrategy for TurbineSampler {
    fn sample(&self, rng: &mut dyn rand::RngCore) -> &ValidatorInfo {
        let root = self.stake_weighted.sample(rng);
        if rng.random::<f64>() < 0.2 {
            root
        } else {
            let mut sample = self.stake_weighted.sample(rng);
            while sample.id == root.id {
                sample = self.stake_weighted.sample(rng);
            }
            sample
        }
    }
}

/// A sampler that uses the FA1-F committee sampling strategy.
///
/// This is a strict improvement over performing IID stake-weighted sampling.
/// It achieves lower variance by deterministically sampling high-stake validators.
///
/// FA1-F is parameterized by a fallback sampler F and runs in two phases:
/// 1. Any validator with more than 1/k fractional stake, is deterministically
///    selected floor(fractional stake * k) times.
/// 2. For the remaining k' samples, sample each validator from F, instantiated
///    with modified stake weights: S'(v) = S(v) - floor(S(v) * k) / k
///
/// See also: <https://dl.acm.org/doi/pdf/10.1145/3576915.3623194>
pub struct FaitAccompli1Sampler<F: SamplingStrategy> {
    validators: Vec<ValidatorInfo>,
    fallback_sampler: F,
}

impl<F: SamplingStrategy> FaitAccompli1Sampler<F> {
    pub const fn new(validators: Vec<ValidatorInfo>, fallback_sampler: F) -> Self {
        Self {
            validators,
            fallback_sampler,
        }
    }
}

impl FaitAccompli1Sampler<StakeWeightedSampler> {
    /// Creates a new FA1-F sampler with an IID stake-weighted fallback sampler.
    // FIXME: hard-coded k=64
    // TODO: how to handle initializing fallback sampler?
    //       support running sample_multiple(...) on different k?
    pub fn new_with_stake_weighted_fallback(validators: Vec<ValidatorInfo>) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let mut validators_truncated_stake = validators.clone();
        for v in &mut validators_truncated_stake {
            let frac_stake = v.stake as f64 / total_stake as f64;
            let samples = (frac_stake * 64 as f64).floor() as u64;
            v.stake -= samples * total_stake / 64;
        }
        let fallback_sampler = StakeWeightedSampler::new(validators_truncated_stake);
        Self {
            validators,
            fallback_sampler,
        }
    }
}

impl<F: SamplingStrategy> SamplingStrategy for FaitAccompli1Sampler<F> {
    fn sample(&self, rng: &mut dyn rand::RngCore) -> &ValidatorInfo {
        let index = rng.random_range(0..self.validators.len());
        &self.validators[index]
    }

    fn sample_multiple(&self, k: usize, rng: &mut dyn rand::RngCore) -> Vec<ValidatorInfo> {
        let mut validators = Vec::new();
        let total_stake: Stake = self.validators.iter().map(|v| v.stake).sum();
        for v in &self.validators {
            let frac_stake = v.stake as f64 / total_stake as f64;
            let samples = (frac_stake * k as f64).floor() as u64;
            for _ in 0..samples {
                validators.push(v.clone());
            }
        }
        while validators.len() < k {
            validators.push(self.fallback_sampler.sample(rng).clone());
        }
        validators
    }
}

/// A sampler that uses the FA2 committee sampling strategy.
///
/// See also: <https://dl.acm.org/doi/pdf/10.1145/3576915.3623194>
pub struct FaitAccompli2Sampler {
    validators: Vec<ValidatorInfo>,
}

impl FaitAccompli2Sampler {
    pub const fn new(validators: Vec<ValidatorInfo>) -> Self {
        Self { validators }
    }
}

impl SamplingStrategy for FaitAccompli2Sampler {
    fn sample(&self, rng: &mut dyn rand::RngCore) -> &ValidatorInfo {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;

    use core::f64;
    use std::collections::HashSet;

    fn create_validator_info(count: u64) -> Vec<ValidatorInfo> {
        let mut validators = Vec::new();
        for i in 0..count {
            let sk = SecretKey::new(&mut rand::rng());
            let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
            validators.push(ValidatorInfo {
                id: i,
                stake: 1,
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: String::new(),
                disseminator_address: String::new(),
                repair_address: String::new(),
            });
        }
        validators
    }

    #[test]
    fn uniform_sampler() {
        // apply Hoeffding's bound to number of different samples
        let validators = create_validator_info(1000);
        let sampler = UniformSampler::new(validators);
        let sampled_val = sampler.sample_multiple(1000, &mut rand::rng());
        let sampled_ids: HashSet<_> = sampled_val.iter().map(|v| v.id).collect();
        assert!(sampled_ids.len() > 500 && sampled_ids.len() < 750);
        // apply Chernoff's bound to maximum appearances of any sample
        let max_appearances = sampled_ids
            .iter()
            .map(|i| sampled_val.iter().filter(|v| v.id == *i).count())
            .max()
            .unwrap();
        assert!(max_appearances > 1);
        assert!(max_appearances < 17);

        // bounds should hold even with one high-stake validator
        let mut validators = create_validator_info(1000);
        validators[0].stake = 1_000_000_000;
        let sampler = UniformSampler::new(validators);
        let sampled_val = sampler.sample_multiple(1000, &mut rand::rng());
        let sampled_ids: HashSet<_> = sampled_val.iter().map(|v| v.id).collect();
        assert!(sampled_ids.len() > 500 && sampled_ids.len() < 750);
        let max_appearances = sampled_ids
            .iter()
            .map(|i| sampled_val.iter().filter(|v| v.id == *i).count())
            .max()
            .unwrap();
        assert!(max_appearances > 1);
        assert!(max_appearances < 17);

        // bound should hold even with every second validator being high-stake
        let mut validators = create_validator_info(1000);
        for i in (0..validators.len()).step_by(2) {
            validators[i].stake = 1_000_000_000;
        }
        let sampler = UniformSampler::new(validators);
        let sampled_val = sampler.sample_multiple(1000, &mut rand::rng());
        let sampled_ids: HashSet<_> = sampled_val.iter().map(|v| v.id).collect();
        assert!(sampled_ids.len() > 500 && sampled_ids.len() < 750);
        let max_appearances = sampled_ids
            .iter()
            .map(|i| sampled_val.iter().filter(|v| v.id == *i).count())
            .max()
            .unwrap();
        assert!(max_appearances > 1);
        assert!(max_appearances < 17);
    }

    #[test]
    fn stake_weighted_sampler() {
        // with equal stake, bounds from uniform sampling hold
        let validators = create_validator_info(1000);
        let sampler = StakeWeightedSampler::new(validators);
        let sampled_val = sampler.sample_multiple(1000, &mut rand::rng());
        let sampled_ids: HashSet<_> = sampled_val.iter().map(|v| v.id).collect();
        assert!(sampled_ids.len() > 500 && sampled_ids.len() < 750);
        let max_appearances = sampled_ids
            .iter()
            .map(|i| sampled_val.iter().filter(|v| v.id == *i).count())
            .max()
            .unwrap();
        assert!(max_appearances > 1);
        assert!(max_appearances < 17);

        // sampling is done by stake and with replacement
        let mut validators = create_validator_info(100);
        validators[0].stake = 1_000_000_000;
        let sampler = StakeWeightedSampler::new(validators);
        assert_eq!(sampler.sample(&mut rand::rng()).id, 0);
        let sampled_val = sampler.sample_multiple(100, &mut rand::rng());
        let sampled0 = sampled_val.iter().filter(|v| v.id == 0).count();
        assert!(sampled0 == 100);
    }

    #[test]
    fn decaying_acceptance_sampler() {
        // max_samples = 1 equivalent to sampling w/o replacement
        let validators = create_validator_info(100);
        let sampler = DecayingAcceptanceSampler::new(validators, 1.0);
        let sampled_val = sampler.sample_multiple(100, &mut rand::rng());
        let sampled_ids: HashSet<_> = sampled_val.iter().map(|v| v.id).collect();
        assert_eq!(sampled_ids.len(), 100);

        // heavy node sampled at most max_samples times
        let mut validators = create_validator_info(100);
        validators[0].stake = 10_000;
        let sampler = DecayingAcceptanceSampler::new(validators, 5.0);
        let sampled_val = sampler.sample_multiple(100, &mut rand::rng());
        let sampled0 = sampled_val.iter().filter(|v| v.id == 0).count();
        assert!(sampled0 <= 5);

        // max_samples = inf equivalent to sampling with replacement
        let mut validators = create_validator_info(100);
        validators[0].stake = 1_000_000_000;
        let sampler = DecayingAcceptanceSampler::new(validators, f64::INFINITY);
        assert_eq!(sampler.sample(&mut rand::rng()).id, 0);
        let sampled_val = sampler.sample_multiple(100, &mut rand::rng());
        let sampled0 = sampled_val.iter().filter(|v| v.id == 0).count();
        assert!(sampled0 == 100);
    }

    #[test]
    fn turbine_sampler() {
        // // check upper bound
        // let mut validators = create_validator_info(4000);
        // validators[0].stake = 10_000;
        // let sampler = TurbineSampler::new(validators, 200);
        // let sampled_val = sampler.sample_multiple(100, &mut rand::rng());
        // let sampled_ids: HashSet<_> = sampled_val.iter().map(|v| v.id).collect();
        // let max_appearances = sampled_ids
        //     .iter()
        //     .map(|i| sampled_val.iter().filter(|v| v.id == *i).count())
        //     .max()
        //     .unwrap();
        // // should be sampled an expected 5 times
        // assert!(max_appearances > 0);
        // assert!(max_appearances < 10);

        // TODO: compare to actual `Turbine` implementation
    }

    #[test]
    fn fa1_sampler() {
        // with k equal-weight nodes this deterministically selects all nodes
        // FIXME: panics when trying to create fallback sampler with all 0 stakes
        //
        // let validators = create_validator_info(64);
        // let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators);
        // let sampled = sampler.sample_multiple(64, &mut rand::rng());
        // assert_eq!(sampled.len(), 64);
        // let sampled: HashSet<_> = sampled.into_iter().map(|v| v.id).collect();
        // assert_eq!(sampled.len(), 64);
        // for id in 0..64 {
        //     assert!(sampled.contains(&id));
        // }

        // with many low-stake nodes this becomes the underlying fallback distribution
        let validators = create_validator_info(1000);
        let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators);
        let sampled_val = sampler.sample_multiple(64, &mut rand::rng());
        assert_eq!(sampled_val.len(), 64);
        let sampled_ids: HashSet<_> = sampled_val.iter().map(|v| v.id).collect();
        let max_appearances = sampled_ids
            .iter()
            .map(|i| sampled_val.iter().filter(|v| v.id == *i).count())
            .max()
            .unwrap();
        assert!(max_appearances >= 1);
        assert!(max_appearances < 3);

        // with a mix, high stake nodes appear at least `floor(stake * k)` times
        let mut validators = create_validator_info(1000);
        validators[0].stake = 52;
        validators[1].stake = 52;
        let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators);
        let sampled_val = sampler.sample_multiple(64, &mut rand::rng());
        assert_eq!(sampled_val.len(), 64);
        let sampled0 = sampled_val.iter().filter(|v| v.id == 0).count();
        let sampled1 = sampled_val.iter().filter(|v| v.id == 1).count();
        assert!(sampled0 >= 3);
        assert!(sampled1 >= 3);
    }

    #[test]
    fn fa2_sampler() {
        // TODO: add test
    }
}
