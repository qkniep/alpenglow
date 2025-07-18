// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Different strategies for sampling validators.
//!
//! First, this module provides a trait for randomly sampling validators.
//! To implement a new sampling strategy, you need to implement [`SamplingStrategy`],
//! by implementing [`SamplingStrategy::sample`].
//! The trait provides a default implementation for sampling `k` validators,
//! via [`SamplingStrategy::sample_multiple`].
//! However, samplers might override this for performance reasons.
//!
//! # Sampling strategies
//!
//! This module provides implementations for the following sampling strategies:
//! - [`UniformSampler`] does uniform sampling with replacement.
//! - [`StakeWeightedSampler`] samples validators proportional to their stake.
//! - [`DecayingAcceptanceSampler`] samples validators less as they approach maximum.
//! - [`TurbineSampler`] simulates the workload of Turbine.
//! - [`FaitAccompli1Sampler`] uses the FA1-F committee sampling strategy.

use std::sync::Mutex;

use rand::distr::weighted::WeightedIndex;
use rand::prelude::*;

use crate::disseminator::turbine::DEFAULT_FANOUT;
use crate::{Stake, ValidatorId, ValidatorInfo};

const MAX_TRIES_PER_SAMPLE: usize = 100_000;

/// An abstraction for randomly sampling validators based on some distribution.
pub trait SamplingStrategy {
    /// Samples a validator with this probability distribution.
    ///
    /// Depending on the implementor, this may or may not be stateless.
    ///
    /// # Panics
    ///
    /// Implementations may panic if the sampler has reached an invalid state
    /// or if the sampling process failed [`MAX_TRIES_PER_SAMPLE`] times.
    fn sample<R: RngCore>(&self, rng: &mut R) -> ValidatorId;

    /// Samples a validator's info ...
    fn sample_info<R: RngCore>(&self, rng: &mut R) -> &ValidatorInfo;

    /// Samples `k` validators with this probability distribution.
    ///
    /// # Panics
    ///
    /// Panics if any of the `k` calls to [`SamplingStrategy::sample`] panics.
    fn sample_multiple<R: RngCore>(&self, k: usize, rng: &mut R) -> Vec<ValidatorId> {
        (0..k).map(|_| self.sample(rng)).collect()
    }
}

/// A basic sampler that picks all validators with equal probability.
///
/// This sampler is stateless and chooses validators with replacement.
/// Multiple samples from this are thus independent and identically distributed.
#[derive(Clone)]
pub struct UniformSampler {
    validators: Vec<ValidatorInfo>,
}

impl UniformSampler {
    pub const fn new(validators: Vec<ValidatorInfo>) -> Self {
        Self { validators }
    }
}

impl SamplingStrategy for UniformSampler {
    fn sample<R: RngCore>(&self, rng: &mut R) -> ValidatorId {
        rng.random_range(0..self.validators.len()) as ValidatorId
    }

    fn sample_info<R: RngCore>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng) as usize;
        &self.validators[index]
    }
}

/// A sampler that picks validators directly proportional to their stake.
///
/// This sampler is stateless and chooses validators with replacement.
/// Multiple samples from this are thus independent and identically distributed.
#[derive(Clone)]
pub struct StakeWeightedSampler {
    validators: Vec<ValidatorInfo>,
    stake_index: WeightedIndex<u64>,
}

impl StakeWeightedSampler {
    /// Creates a new `StakeWeightedSampler` instance.
    pub fn new(validators: Vec<ValidatorInfo>) -> Self {
        let stakes: Vec<Stake> = validators.iter().map(|v| v.stake).collect();
        let stake_index = WeightedIndex::new(&stakes).unwrap();
        Self {
            validators,
            stake_index,
        }
    }
}

impl SamplingStrategy for StakeWeightedSampler {
    fn sample<R: RngCore>(&self, rng: &mut R) -> ValidatorId {
        self.stake_index.sample(rng) as ValidatorId
    }

    fn sample_info<R: RngCore>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng) as usize;
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
    /// Creates a new `DecayingAcceptanceSampler` instance.
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
    /// Samples a validator with the given probability distribution.
    ///
    /// # Panics
    ///
    /// Panics if after [`MAX_TRIES_PER_SAMPLE`] samples none was valid.
    fn sample<R: RngCore>(&self, rng: &mut R) -> ValidatorId {
        for _ in 0..MAX_TRIES_PER_SAMPLE {
            let sample = self.stake_weighted.sample(rng);
            let mut sample_count = self.sample_count.lock().unwrap();
            let p_reject = sample_count[sample as usize] as f64 / self.max_samples;
            if rng.random::<f64>() >= p_reject {
                sample_count[sample as usize] += 1;
                return sample;
            }
        }

        panic!("rejected all {MAX_TRIES_PER_SAMPLE} samples");
    }

    fn sample_info<R: RngCore>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng) as usize;
        &self.stake_weighted.validators[index]
    }

    fn sample_multiple<R: RngCore>(&self, k: usize, rng: &mut R) -> Vec<ValidatorId> {
        let samples = (0..k).map(|_| self.sample(rng)).collect();
        self.reset();
        samples
    }
}

impl Clone for DecayingAcceptanceSampler {
    fn clone(&self) -> Self {
        Self {
            stake_weighted: self.stake_weighted.clone(),
            max_samples: self.max_samples,
            sample_count: Mutex::new(self.sample_count.lock().unwrap().clone()),
        }
    }
}

/// A sampler that simulates the probability distribution in Turbine for Rotor.
///
/// The goal is to distribute the required work for validators as in Turbine.
/// Specifically, it should respect the same upper bound on the amount of work,
/// that is, for `v` validators and given `turbine_fanout` any validator should
/// be sampled no more than with probability `turbine_fanout / v`.
#[derive(Clone)]
pub struct TurbineSampler {
    stake_weighted: StakeWeightedSampler,
}

impl TurbineSampler {
    /// Creates a new `TurbineSampler` instance simulating the [`DEFAULT_FANOUT`]
    /// from the actual [`Turbine`] implementation.
    ///
    /// [`Turbine`]: crate::disseminator::turbine::Turbine
    pub fn new(validators: Vec<ValidatorInfo>) -> Self {
        Self::new_with_fanout(validators, DEFAULT_FANOUT)
    }

    /// Creates a new `TurbineSampler` instance simulating the given fanout.
    // FIXME: slow and still somewhat incaccurate
    // TODO: support more than 2 levels of Turbine?
    #[must_use]
    pub fn new_with_fanout(mut validators: Vec<ValidatorInfo>, turbine_fanout: usize) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();

        // calculate expected work for each validator
        let mut expected_work = vec![0.0; validators.len()];
        for leader in &validators {
            let validators_left = validators.len() - 1;
            let prob = leader.stake as f64 / total_stake as f64;
            expected_work[leader.id as usize] += prob;
            for root in &validators {
                if root.id == leader.id {
                    continue;
                }
                let validators_left = validators_left - 1;
                let stake_left = total_stake - leader.stake;
                let prob = prob * root.stake as f64 / stake_left as f64;
                let root_work = (turbine_fanout as f64).min(validators_left as f64);
                expected_work[root.id as usize] += prob * root_work;
                for maybe_level1 in &validators {
                    if maybe_level1.id == leader.id || maybe_level1.id == root.id {
                        continue;
                    }
                    let stake_left = total_stake - root.stake;
                    let select_prob = maybe_level1.stake as f64 / stake_left as f64;
                    let full_level1_slots = validators_left / turbine_fanout;
                    let prob_full =
                        prob * (1.0 - (1.0 - select_prob).powi(full_level1_slots as i32));
                    let full_level1_work = turbine_fanout as f64;
                    expected_work[maybe_level1.id as usize] += prob_full * full_level1_work;
                    let prob_partial =
                        prob * (1.0 - select_prob).powi(full_level1_slots as i32) * select_prob;
                    let partial_level1_work = (validators_left % turbine_fanout) as f64;
                    expected_work[maybe_level1.id as usize] += prob_partial * partial_level1_work;
                }
            }
        }

        // turn expected work into stakes
        for (i, w) in expected_work.iter().enumerate() {
            validators[i].stake = (w * 1_000_000_000.0) as Stake;
        }

        Self {
            stake_weighted: StakeWeightedSampler::new(validators),
        }
    }
}

impl SamplingStrategy for TurbineSampler {
    /// Samples a validator with the given probability distribution.
    ///
    /// # Panics
    ///
    /// Panics if after [`MAX_TRIES_PER_SAMPLE`] samples none was valid.
    fn sample<R: RngCore>(&self, rng: &mut R) -> ValidatorId {
        let root = self.stake_weighted.sample(rng);
        if rng.random::<f64>() < 0.2 {
            root
        } else {
            for _ in 0..MAX_TRIES_PER_SAMPLE {
                let sample = self.stake_weighted.sample(rng);
                if sample != root {
                    return sample;
                }
            }
            panic!("rejected all {MAX_TRIES_PER_SAMPLE} samples");
        }
    }

    fn sample_info<R: RngCore>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng) as usize;
        &self.stake_weighted.validators[index]
    }
}

/// A sampler that samples proportional to stake with reduced variance.
///
/// This sampler operates on `k` bins of validators of equal stake.
/// Within each bin a validator is sampled with probability proportional to its stake.
/// To sample `k` validators then, one validator is drawn from each of the `k` bins.
///
/// Given that each validator has less stake than to fill one bins entirely,
/// as is the case if this is used as the fallback sampler in [`FaitAccompli1Sampler`],
/// each validator appears in at most two bins and is thus sampled at most twice.
///
/// In expectation each validator is sampled proportionally to its stake.
/// However, this is done with lower variance than [`StakeWeightedSampler`] would.
pub struct PartitionSampler {
    validators: Vec<ValidatorInfo>,
    bins: Vec<WeightedIndex<u64>>,
    pub bin_validators: Vec<Vec<ValidatorId>>,
    pub bin_stakes: Vec<Vec<Stake>>,
}

impl PartitionSampler {
    /// Creates a new `ParitionSampler` instance.
    ///
    /// Partitions the given validators into `num_bins` bins of equal stake.
    /// Paritioning is done randomly by splitting a randomly permuted list of nodes.
    pub fn new(validators: Vec<ValidatorInfo>, num_bins: usize) -> Self {
        if num_bins == 0 {
            return Self {
                validators,
                bins: Vec::new(),
                bin_validators: Vec::new(),
                bin_stakes: Vec::new(),
            };
        }

        let mut bin_validators = vec![Vec::new(); num_bins];
        let mut bin_stakes = vec![Vec::new(); num_bins];

        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let stake_per_bin = total_stake.div_ceil(num_bins as Stake);
        let mut validators_random = validators.clone();
        validators_random.shuffle(&mut rand::rng());

        // partition into bins
        let mut current_bin = 0;
        let mut current_bin_stake = 0;
        for v in validators_random {
            let mut stake = v.stake;
            while stake > 0 {
                bin_validators[current_bin].push(v.id);
                let stake_to_take = stake.min(stake_per_bin - current_bin_stake);
                current_bin_stake += stake_to_take;
                bin_stakes[current_bin].push(stake_to_take);
                stake -= stake_to_take;
                if current_bin < num_bins - 1 && (stake > 0 || current_bin_stake == stake_per_bin) {
                    current_bin += 1;
                    current_bin_stake = 0;
                }
            }
        }

        // generate stake weighted indices for each bin
        let mut bins = Vec::with_capacity(num_bins);
        for stakes in &bin_stakes {
            let bin = WeightedIndex::new(stakes).unwrap();
            bins.push(bin);
        }

        Self {
            validators,
            bins,
            bin_validators,
            bin_stakes,
        }
    }
}

impl SamplingStrategy for PartitionSampler {
    fn sample<R: RngCore>(&self, _rng: &mut R) -> ValidatorId {
        unimplemented!()
    }

    fn sample_info<R: RngCore>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng) as usize;
        &self.validators[index]
    }

    fn sample_multiple<R: RngCore>(&self, _k: usize, rng: &mut R) -> Vec<ValidatorId> {
        let mut samples = Vec::new();
        for (bin, validators) in self.bins.iter().zip(self.bin_validators.iter()) {
            let i = bin.sample(rng);
            samples.push(validators[i]);
        }
        samples
    }
}

impl Clone for PartitionSampler {
    fn clone(&self) -> Self {
        Self {
            validators: self.validators.clone(),
            bins: self.bins.clone(),
            bin_validators: self.bin_validators.clone(),
            bin_stakes: self.bin_stakes.clone(),
        }
    }
}

/// A sampler that uses the FA1-F committee sampling strategy.
///
/// This is a strict improvement over performing IID stake-weighted sampling.
/// It achieves lower variance by deterministically sampling high-stake validators.
///
/// FA1-F is parameterized by a fallback sampler `F` and runs in two phases:
/// 1. Any validator with more than `1/k` fractional stake, is deterministically
///    selected `floor(fractional stake * k)` times.
/// 2. For the remaining `k'` samples, sample each validator from `F`, instantiated
///    with modified stake weights: `S'(v) = S(v) - floor(S(v) * k) / k`
///
/// See also: <https://dl.acm.org/doi/pdf/10.1145/3576915.3623194>
pub struct FaitAccompli1Sampler<F: SamplingStrategy> {
    validators: Vec<ValidatorInfo>,
    required_samples: Vec<ValidatorId>,
    pub fallback_sampler: F,
}

impl FaitAccompli1Sampler<PartitionSampler> {
    /// Creates a new FA1-F sampler with a variance-reducing partition fallback sampler.
    ///
    /// See [`PartitionSampler`] for more details.
    // TODO: how to handle initializing fallback sampler?
    //       support running sample_multiple(...) on different k?
    #[must_use]
    pub fn new_with_partition_fallback(validators: Vec<ValidatorInfo>, k: u64) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let mut required_samples = Vec::new();
        let mut validators_truncated_stake = validators.clone();
        for v in &mut validators_truncated_stake {
            let frac_stake = v.stake as f64 / total_stake as f64;
            let samples = (frac_stake * k as f64).floor() as u64;
            v.stake -= samples * total_stake / k;
            required_samples.extend((0..samples).map(|_| v.id));
        }
        let all_zero = validators_truncated_stake.iter().all(|v| v.stake == 0);
        let k_prime = k as usize - required_samples.len();
        let fallback_sampler = if all_zero {
            PartitionSampler::new(validators.clone(), k_prime)
        } else {
            PartitionSampler::new(validators_truncated_stake, k_prime)
        };
        Self {
            validators,
            required_samples,
            fallback_sampler,
        }
    }
}

impl FaitAccompli1Sampler<StakeWeightedSampler> {
    /// Creates a new FA1-F sampler with an IID stake-weighted fallback sampler.
    ///
    /// See [`StakeWeightedSampler`] for more details.
    // TODO: how to handle initializing fallback sampler?
    //       support running sample_multiple(...) on different k?
    #[must_use]
    pub fn new_with_stake_weighted_fallback(validators: Vec<ValidatorInfo>, k: u64) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let mut required_samples = Vec::new();
        let mut validators_truncated_stake = validators.clone();
        for v in &mut validators_truncated_stake {
            let frac_stake = v.stake as f64 / total_stake as f64;
            let samples = (frac_stake * k as f64).floor() as u64;
            v.stake -= samples * total_stake / k;
            required_samples.extend((0..samples).map(|_| v.id));
        }
        let all_zero = validators_truncated_stake.iter().all(|v| v.stake == 0);
        let fallback_sampler = if all_zero {
            StakeWeightedSampler::new(validators.clone())
        } else {
            StakeWeightedSampler::new(validators_truncated_stake)
        };
        Self {
            validators,
            required_samples,
            fallback_sampler,
        }
    }
}

impl<F: SamplingStrategy> SamplingStrategy for FaitAccompli1Sampler<F> {
    fn sample<R: RngCore>(&self, rng: &mut R) -> ValidatorId {
        rng.random_range(0..self.validators.len()) as ValidatorId
    }

    fn sample_info<R: RngCore>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng) as usize;
        &self.validators[index]
    }

    fn sample_multiple<R: RngCore>(&self, k: usize, rng: &mut R) -> Vec<ValidatorId> {
        let mut validators = Vec::with_capacity(k);
        validators.extend_from_slice(&self.required_samples);
        if validators.len() < k {
            let k_prime = k - validators.len();
            let additional_samples = self.fallback_sampler.sample_multiple(k_prime, rng);
            validators.extend_from_slice(&additional_samples);
        }
        validators
    }
}

impl<F: SamplingStrategy + Clone> Clone for FaitAccompli1Sampler<F> {
    fn clone(&self) -> Self {
        Self {
            validators: self.validators.clone(),
            required_samples: self.required_samples.clone(),
            fallback_sampler: self.fallback_sampler.clone(),
        }
    }
}

/// A sampler that uses the FA2 committee sampling strategy.
///
/// See also: <https://dl.acm.org/doi/pdf/10.1145/3576915.3623194>
pub struct FaitAccompli2Sampler {
    validators: Vec<ValidatorInfo>,
    required_samples: Vec<ValidatorId>,
    medium_nodes: Vec<(ValidatorId, f64)>,
    fallback_sampler: StakeWeightedSampler,
}

impl FaitAccompli2Sampler {
    /// Creates a new FA2 sampler instance.
    ///
    /// This is instantiated for a fixed number of samples `k`.
    /// To this end, the FA1 and FA2 pre-processing steps are applied,
    /// and also a stake-weighted IID fallback sampler is generated.
    // TODO: support running sample_multiple(...) on different k?
    pub fn new(validators: Vec<ValidatorInfo>, k: u64) -> Self {
        // FA1 step
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let mut required_samples = Vec::new();
        for v in &validators {
            let frac_stake = v.stake as f64 / total_stake as f64;
            let samples = (frac_stake * k as f64).floor() as u64;
            required_samples.extend((0..samples).map(|_| v.id));
        }

        // FA2 step
        let f = Self::minimize_f(&validators, k);
        let mut medium_nodes = Vec::new();
        for (i, fi) in f.iter().enumerate() {
            let rel_stake = validators[i].stake as f64 / total_stake as f64;
            if *fi > rel_stake {
                let p = 1.0 - (fi - rel_stake) * k as f64;
                medium_nodes.push((i as ValidatorId, p));
            }
        }

        // generate stake-weighted IID fallback sampler
        let r: f64 = validators
            .iter()
            .enumerate()
            .filter(|(i, v)| v.stake as f64 / total_stake as f64 > f[*i])
            .map(|(i, v)| v.stake as f64 / total_stake as f64 - f[i])
            .sum();
        let new_stake_distribution: Vec<ValidatorInfo> = validators
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, mut v)| {
                if v.stake as f64 / total_stake as f64 > f[i] {
                    v.stake = ((v.stake as f64 / total_stake as f64 - f[i]) / r
                        * total_stake as f64) as Stake;
                } else {
                    v.stake = 0;
                }
                v
            })
            .collect();
        let fallback_sampler = match r == 0.0 {
            true => StakeWeightedSampler::new(validators.clone()),
            false => StakeWeightedSampler::new(new_stake_distribution),
        };

        Self {
            validators,
            required_samples,
            medium_nodes,
            fallback_sampler,
        }
    }

    fn minimize_f(validators: &[ValidatorInfo], k: u64) -> Vec<f64> {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let f: Vec<f64> = validators
            .iter()
            .map(|v| (v.stake as f64 / total_stake as f64 * k as f64).round() / k as f64)
            .collect();
        assert!(f.iter().sum::<f64>() <= 1.0);
        f
    }
}

impl SamplingStrategy for FaitAccompli2Sampler {
    fn sample<R: RngCore>(&self, _rng: &mut R) -> ValidatorId {
        // FA2 only supports multiple samples
        unimplemented!()
    }

    fn sample_info<R: RngCore>(&self, _rng: &mut R) -> &ValidatorInfo {
        // FA2 only supports multiple samples
        unimplemented!()
    }

    fn sample_multiple<R: RngCore>(&self, k: usize, rng: &mut R) -> Vec<ValidatorId> {
        // add required FA1 samples
        let mut validators = Vec::with_capacity(k);
        validators.extend_from_slice(&self.required_samples);

        // sample medium nodes (FA2 step)
        for (validator, probability) in &self.medium_nodes {
            if rng.random_bool(*probability) {
                validators.push(*validator);
            }
        }

        // sample remaining validators IID stake-weighted
        if validators.len() < k {
            let k_prime = k - validators.len();
            let additional_samples = self.fallback_sampler.sample_multiple(k_prime, rng);
            validators.extend_from_slice(&additional_samples);
        }

        validators
    }
}

impl Clone for FaitAccompli2Sampler {
    fn clone(&self) -> Self {
        Self {
            validators: self.validators.clone(),
            required_samples: self.required_samples.clone(),
            medium_nodes: self.medium_nodes.clone(),
            fallback_sampler: self.fallback_sampler.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ValidatorId;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::disseminator::turbine::WeightedShuffle;
    use crate::network::simulated::stake_distribution::VALIDATOR_DATA;
    use crate::shredder::TOTAL_SHREDS;

    use std::collections::HashSet;

    fn create_validator_info(count: ValidatorId) -> Vec<ValidatorInfo> {
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
        let sampled = sampler.sample_multiple(1000, &mut rand::rng());
        let sampled_set: HashSet<_> = sampled.iter().collect();
        assert!(sampled_set.len() > 500 && sampled_set.len() < 750);
        // apply Chernoff's bound to maximum appearances of any sample
        let max_appearances = sampled_set
            .iter()
            .map(|i| sampled.iter().filter(|v| *v == *i).count())
            .max()
            .unwrap();
        assert!(max_appearances > 1);
        assert!(max_appearances < 17);

        // bounds should hold even with one high-stake validator
        let mut validators = create_validator_info(1000);
        validators[0].stake = 1_000_000_000;
        let sampler = UniformSampler::new(validators);
        let sampled = sampler.sample_multiple(1000, &mut rand::rng());
        let sampled_set: HashSet<_> = sampled.iter().collect();
        assert!(sampled_set.len() > 500 && sampled_set.len() < 750);
        let max_appearances = sampled_set
            .iter()
            .map(|i| sampled.iter().filter(|v| *v == *i).count())
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
        let sampled = sampler.sample_multiple(1000, &mut rand::rng());
        let sampled_set: HashSet<_> = sampled.iter().collect();
        assert!(sampled_set.len() > 500 && sampled_set.len() < 750);
        let max_appearances = sampled_set
            .iter()
            .map(|i| sampled.iter().filter(|v| *v == *i).count())
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
        let sampled = sampler.sample_multiple(1000, &mut rand::rng());
        let sampled_set: HashSet<_> = sampled.iter().collect();
        assert!(sampled_set.len() > 500 && sampled_set.len() < 750);
        let max_appearances = sampled_set
            .iter()
            .map(|i| sampled.iter().filter(|v| *v == *i).count())
            .max()
            .unwrap();
        assert!(max_appearances > 1);
        assert!(max_appearances < 17);

        // sampling is done by stake and with replacement
        let mut validators = create_validator_info(100);
        validators[0].stake = 1_000_000_000;
        let sampler = StakeWeightedSampler::new(validators);
        assert_eq!(sampler.sample(&mut rand::rng()), 0);
        let sampled = sampler.sample_multiple(100, &mut rand::rng());
        let sampled0 = sampled.into_iter().filter(|v| *v == 0).count();
        assert!(sampled0 == 100);
    }

    #[test]
    fn decaying_acceptance_sampler() {
        // max_samples = 1 equivalent to sampling w/o replacement
        let validators = create_validator_info(100);
        let sampler = DecayingAcceptanceSampler::new(validators, 1.0);
        let sampled = sampler.sample_multiple(100, &mut rand::rng());
        let sampled_set: HashSet<_> = sampled.iter().copied().collect();
        assert_eq!(sampled_set.len(), 100);

        // heavy node sampled at most max_samples times
        let mut validators = create_validator_info(100);
        validators[0].stake = 10_000;
        let sampler = DecayingAcceptanceSampler::new(validators, 5.0);
        let sampled = sampler.sample_multiple(100, &mut rand::rng());
        let sampled0 = sampled.into_iter().filter(|v| *v == 0).count();
        assert!(sampled0 <= 5);

        // max_samples = inf equivalent to sampling with replacement
        let mut validators = create_validator_info(100);
        validators[0].stake = 1_000_000_000;
        let sampler = DecayingAcceptanceSampler::new(validators, f64::INFINITY);
        assert_eq!(sampler.sample(&mut rand::rng()), 0);
        let sampled = sampler.sample_multiple(100, &mut rand::rng());
        let sampled0 = sampled.into_iter().filter(|v| *v == 0).count();
        assert!(sampled0 == 100);
    }

    #[test]
    #[ignore]
    fn turbine_sampler() {
        const SLICES: usize = 100;

        let mut rng = rand::rng();
        let mut validators = create_validator_info(4000);
        // two large nodes with 5% of the stake each
        validators[0].stake = 200;
        validators[1].stake = 200;
        let sampler = TurbineSampler::new(validators.clone());
        let sampled = sampler.sample_multiple(TOTAL_SHREDS * SLICES, &mut rng);
        let appearances0 = sampled.iter().filter(|v| **v == 0).count();
        let appearances1 = sampled.iter().filter(|v| **v == 1).count();
        let work0 = (TOTAL_SHREDS * SLICES / 20) + appearances0 * validators.len();
        let work1 = (TOTAL_SHREDS * SLICES / 20) + appearances1 * validators.len();

        let mut turbine_work0 = 0;
        let mut turbine_work1 = 0;
        for _ in 0..TOTAL_SHREDS * SLICES {
            let mut weighted_shuffle = WeightedShuffle::new(validators.iter().map(|v| v.stake));
            let validator_ids: Vec<_> = weighted_shuffle
                .shuffle(&mut rng)
                .map(|i| i as ValidatorId)
                .collect();

            let leader = validator_ids[0];
            if leader == 0 {
                turbine_work0 += 1;
            } else if leader == 1 {
                turbine_work1 += 1;
            }
            let root = validator_ids[1];
            if root == 0 {
                turbine_work0 += DEFAULT_FANOUT;
            } else if root == 1 {
                turbine_work1 += DEFAULT_FANOUT;
            }
            let mut validators_left = validators.len() - 2 - DEFAULT_FANOUT;
            for i in 0..DEFAULT_FANOUT {
                let parent = validator_ids[2 + i] as usize;
                if parent == 0 {
                    turbine_work0 += DEFAULT_FANOUT.min(validators_left);
                } else if parent == 1 {
                    turbine_work1 += DEFAULT_FANOUT.min(validators_left);
                }
                if validators_left < DEFAULT_FANOUT {
                    break;
                }
                validators_left -= DEFAULT_FANOUT;
            }
        }

        let rel_workload = (turbine_work0 + turbine_work1) as f64 / (work0 + work1) as f64;
        assert!(rel_workload < 1.1);
        assert!(rel_workload > 0.9);
    }

    #[tokio::test]
    #[ignore]
    async fn turbine_sampler_real_world() {
        const SLICES: usize = 100_000;

        // use real mainnet validator stake distribution
        let mut stakes = Vec::new();
        for validator in VALIDATOR_DATA.iter() {
            if validator.is_active && validator.delinquent == Some(false) {
                let stake = validator.active_stake.unwrap();
                if stake > 0 {
                    stakes.push(stake);
                }
            }
        }
        let total_stake: Stake = stakes.iter().sum();
        let mut validators = create_validator_info(stakes.len() as ValidatorId);
        for (i, stake) in stakes.into_iter().enumerate() {
            validators[i].stake = stake;
        }

        // count workload of each validator in Turbine
        let mut rng = rand::rng();
        let mut turbine_workload = vec![0; validators.len()];
        for _ in 0..TOTAL_SHREDS * SLICES {
            let mut weighted_shuffle = WeightedShuffle::new(validators.iter().map(|v| v.stake));
            let validator_ids: Vec<_> = weighted_shuffle
                .shuffle(&mut rng)
                .map(|i| i as ValidatorId)
                .collect();

            let _leader = validator_ids[0];
            let root = validator_ids[1];
            turbine_workload[root as usize] += DEFAULT_FANOUT;
            let mut validators_left = validators.len() - 2 - DEFAULT_FANOUT;
            for i in 0..DEFAULT_FANOUT {
                let parent = validator_ids[2 + i] as usize;
                turbine_workload[parent] += DEFAULT_FANOUT.min(validators_left);
                if validators_left < DEFAULT_FANOUT {
                    break;
                }
                validators_left -= DEFAULT_FANOUT;
            }
        }
        let turbine_workload_normalized = turbine_workload
            .into_iter()
            .map(|w| w as f64 / (64.0 * SLICES as f64));

        // count workload of each validator in TurbineSampler
        let mut sampler_workload = vec![0; validators.len()];
        let sampler = TurbineSampler::new(validators.clone());
        for _ in 0..SLICES {
            let relays = sampler.sample_multiple(64, &mut rng);
            for relay in relays {
                let relay_stake = validators[relay as usize].stake;
                let relay_leader_prob = relay_stake as f64 / total_stake as f64;
                if rng.random_bool(relay_leader_prob) {
                    sampler_workload[relay as usize] += validators.len() - 1;
                } else {
                    sampler_workload[relay as usize] += validators.len() - 2;
                }
            }
        }
        let sampler_workload_normalized = sampler_workload
            .into_iter()
            .map(|w| w as f64 / (64.0 * SLICES as f64));

        // compare the two
        let stake_iter = validators.iter().map(|v| v.stake).enumerate();
        let iter = stake_iter
            .zip(turbine_workload_normalized)
            .zip(sampler_workload_normalized);
        for (((i, stake), tw), sw) in iter {
            println!("validator {i}, {stake} stake, tw {tw}, sw {sw}");
            let rel_workload = tw / sw;
            if tw > 0.01 {
                assert!(rel_workload < 1.25);
                assert!(rel_workload > 0.75);
            }
        }
    }

    #[test]
    fn fa1_sampler() {
        // with k equal-weight nodes this deterministically selects all nodes
        let validators = create_validator_info(64);
        let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators, 64);
        let sampled = sampler.sample_multiple(64, &mut rand::rng());
        assert_eq!(sampled.len(), 64);
        let sampled: HashSet<_> = sampled.into_iter().collect();
        assert_eq!(sampled.len(), 64);
        for id in 0..64 {
            assert!(sampled.contains(&id));
        }

        // with k equal-weight nodes this deterministically selects all nodes
        // (also for partitioning fallback sampler)
        let validators = create_validator_info(64);
        let sampler = FaitAccompli1Sampler::new_with_partition_fallback(validators, 64);
        let sampled = sampler.sample_multiple(64, &mut rand::rng());
        assert_eq!(sampled.len(), 64);
        let sampled: HashSet<_> = sampled.into_iter().collect();
        assert_eq!(sampled.len(), 64);
        for id in 0..64 {
            assert!(sampled.contains(&id));
        }

        // with many low-stake nodes this becomes the underlying fallback distribution
        let mut avg_max_appearances = 0.0;
        for _ in 0..20 {
            let validators = create_validator_info(1000);
            let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators, 64);
            let sampled = sampler.sample_multiple(64, &mut rand::rng());
            assert_eq!(sampled.len(), 64);
            let sampled_set = sampled.iter().collect::<HashSet<_>>();
            let max_appearances = sampled_set
                .iter()
                .map(|i| sampled.iter().filter(|v| *v == *i).count())
                .max()
                .unwrap();
            avg_max_appearances += max_appearances as f64 / 20.0;
        }
        assert!(avg_max_appearances >= 1.0);
        assert!(avg_max_appearances < 3.0);

        // with a mix, high stake nodes appear at least `floor(stake * k)` times
        let mut validators = create_validator_info(1000);
        validators[0].stake = 52;
        validators[1].stake = 52;
        let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators, 64);
        let sampled = sampler.sample_multiple(64, &mut rand::rng());
        assert_eq!(sampled.len(), 64);
        let sampled0 = sampled.iter().filter(|v| **v == 0).count();
        let sampled1 = sampled.iter().filter(|v| **v == 1).count();
        assert!(sampled0 >= 3);
        assert!(sampled1 >= 3);
    }

    #[test]
    fn partition_sampler() {
        // TODO: add tests
    }

    #[test]
    fn fa2_sampler() {
        // TODO: add test
    }
}
