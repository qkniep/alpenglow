// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Strategies for sampling validators.
//!
//! This module provides two traits reflecting two distinct operations:
//!
//! - [`SamplingStrategy`] samples a single validator from some distribution.
//!   Implemented by [`UniformSampler`], [`StakeWeightedSampler`], [`TurbineSampler`], etc.
//!
//! - [`QuorumSamplingStrategy`] samples a fixed-size committee (quorum) of validators.
//!   The quorum size is fixed at construction time. Implemented by [`FaitAccompli1Sampler`],
//!   [`FaitAccompli2Sampler`], and [`PartitionSampler`].
//!
//! Any single-node strategy can be turned into a quorum strategy via IID sampling:
//! Call [`SamplingStrategy::into_quorum_strategy`] to obtain an [`IidQuorumSampler`].
//! The reverse direction (quorum → single-node) is intentionally not provided,
//! because quorum strategies like FA1 have no meaningful single-node operation.
//!
//! # Sampling strategies
//!
//! Single-node strategies ([`SamplingStrategy`]):
//! - [`AllSameSampler`] always returns the same validator (for testing).
//! - [`UniformSampler`] picks all validators with equal probability.
//! - [`StakeWeightedSampler`] picks validators proportional to their stake.
//! - [`DecayingAcceptanceSampler`] hybrid between with/without replacement.
//! - [`TurbineSampler`] simulates the workload of Turbine.
//!
//! Quorum strategies ([`QuorumSamplingStrategy`]):
//! - [`IidQuorumSampler`] wraps any single-node strategy, sampling IID.
//! - [`DecayingAcceptanceSampler`] hybrid between with/without replacement.
//! - [`PartitionSampler`] splits validators into bins and samples from each bin.
//! - [`FaitAccompli1Sampler`] uses the FA1-F committee sampling strategy.
//! - [`FaitAccompli2Sampler`] uses the FA2 committee sampling strategy.
//!
//! Note that [`DecayingAcceptanceSampler`] implements both traits.
//! When used as a single-node strategy, it needs to be manually reset.
//! When used as a quorum strategy, it automatically resets after each call to [`sample_quorum`].
//!
//! [`sample_quorum`]: QuorumSamplingStrategy::sample_quorum

use std::sync::Mutex;

use rand::distr::weighted::WeightedIndex;
use rand::prelude::*;

use crate::disseminator::turbine::DEFAULT_FANOUT;
use crate::{Stake, ValidatorId, ValidatorInfo};

/// Sampling strategies involving rejection sampling may panic after rejecting this many samples.
const MAX_TRIES_PER_SAMPLE: usize = 100_000;

/// Strategy for sampling individual validators from some distribution.
///
/// Use [`into_quorum_strategy`] to turn any single-node strategy into a
/// [`QuorumSamplingStrategy`] via IID sampling.
///
/// [`into_quorum_strategy`]: SamplingStrategy::into_quorum_strategy
pub trait SamplingStrategy {
    /// Samples a validator with this probability distribution.
    ///
    /// # Panics
    ///
    /// Implementations may panic if the sampler has reached an invalid state
    /// or if the sampling process failed [`MAX_TRIES_PER_SAMPLE`] times.
    fn sample<R: Rng>(&self, rng: &mut R) -> ValidatorId {
        self.sample_info(rng).id
    }

    /// Samples a validator's [`ValidatorInfo`] with this probability distribution.
    ///
    /// # Panics
    ///
    /// Implementations may panic if the sampler has reached an invalid state
    /// or if the sampling process failed [`MAX_TRIES_PER_SAMPLE`] times.
    fn sample_info<R: Rng>(&self, rng: &mut R) -> &ValidatorInfo;

    /// Wraps this sampler into an [`IidQuorumSampler`] with the given quorum size.
    ///
    /// The returned adapter implements [`QuorumSamplingStrategy`] by calling
    /// [`sample`] `k` times independently.
    ///
    /// [`sample`]: SamplingStrategy::sample
    fn into_quorum_strategy(self, k: usize) -> IidQuorumSampler<Self>
    where
        Self: Sized,
    {
        IidQuorumSampler::new(self, k)
    }
}

/// Strategy for sampling a fixed-size quorum (committee) of validators.
///
/// The quorum size is determined at construction time. Strategies like
/// [`FaitAccompli1Sampler`] pre-compute internal state based on this size,
/// so it cannot be changed after construction.
pub trait QuorumSamplingStrategy {
    /// Returns the quorum size this sampler was constructed for.
    fn quorum_size(&self) -> usize;

    /// Samples a quorum of [`Self::quorum_size()`] validators.
    fn sample_quorum<R: Rng>(&self, rng: &mut R) -> Vec<ValidatorId>;
}

/// Adapter that turns any [`SamplingStrategy`] into a [`QuorumSamplingStrategy`]
/// by sampling IID (independently and identically distributed).
///
/// Created via [`SamplingStrategy::into_quorum_strategy`].
#[derive(Clone)]
pub struct IidQuorumSampler<S: SamplingStrategy> {
    inner: S,
    k: usize,
}

impl<S: SamplingStrategy> IidQuorumSampler<S> {
    /// Creates a new [`IidQuorumSampler`] wrapping `inner` with quorum size `k`.
    pub fn new(inner: S, k: usize) -> Self {
        Self { inner, k }
    }
}

impl<S: SamplingStrategy> SamplingStrategy for IidQuorumSampler<S> {
    fn sample<R: Rng>(&self, rng: &mut R) -> ValidatorId {
        self.inner.sample(rng)
    }

    fn sample_info<R: Rng>(&self, rng: &mut R) -> &ValidatorInfo {
        self.inner.sample_info(rng)
    }
}

impl<S: SamplingStrategy> QuorumSamplingStrategy for IidQuorumSampler<S> {
    fn quorum_size(&self) -> usize {
        self.k
    }

    fn sample_quorum<R: Rng>(&self, rng: &mut R) -> Vec<ValidatorId> {
        (0..self.k).map(|_| self.inner.sample(rng)).collect()
    }
}

/// A trivial sampler that picks the same validator all the time.
#[derive(Clone)]
pub struct AllSameSampler(pub ValidatorInfo);

impl SamplingStrategy for AllSameSampler {
    fn sample<R: Rng>(&self, _rng: &mut R) -> ValidatorId {
        self.0.id
    }

    fn sample_info<R: Rng>(&self, _rng: &mut R) -> &ValidatorInfo {
        &self.0
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
    fn sample<R: Rng>(&self, rng: &mut R) -> ValidatorId {
        ValidatorId::new(rng.random_range(0..self.validators.len()) as u64)
    }

    fn sample_info<R: Rng>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng).as_index();
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
        let stakes = validators.iter().map(|v| v.stake.inner());
        let stake_index = WeightedIndex::new(stakes).unwrap();
        Self {
            validators,
            stake_index,
        }
    }
}

impl SamplingStrategy for StakeWeightedSampler {
    fn sample<R: Rng>(&self, rng: &mut R) -> ValidatorId {
        ValidatorId::new(self.stake_index.sample(rng) as u64)
    }

    fn sample_info<R: Rng>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng).as_index();
        &self.validators[index]
    }
}

/// A sampler that simulates the probability distribution of Turbine for Rotor.
///
/// The goal is to distribute the required work for validators as in Turbine.
/// Specifically, it should respect the same upper bound on the amount of work,
/// that is, for `v` validators and given `fanout` any validator should
/// be sampled no more than with probability `fanout / v`.
#[derive(Clone)]
pub struct TurbineSampler {
    fanout: usize,
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
    // TODO: support more than 2 levels of Turbine?
    #[must_use]
    pub fn new_with_fanout(mut validators: Vec<ValidatorInfo>, turbine_fanout: usize) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();

        // calculate expected work for each validator (only excess over leader work)
        let mut expected_work = vec![0.0; validators.len()];
        let validators_left = validators.len() - 1;
        for leader in &validators {
            let prob = leader.stake.inner() as f64 / total_stake.inner() as f64;
            let stake_left = total_stake - leader.stake;
            let validators_left = validators_left - 1;
            for root in &validators {
                if root.id == leader.id {
                    continue;
                }
                let prob = prob * root.stake.inner() as f64 / stake_left.inner() as f64;
                let root_work = (turbine_fanout as f64).min(validators_left as f64);
                expected_work[root.id.as_index()] += prob * root_work;
                let stake_left = stake_left - root.stake;
                let validators_left = validators_left.saturating_sub(turbine_fanout);
                for maybe_level1 in &validators {
                    if maybe_level1.id == leader.id || maybe_level1.id == root.id {
                        continue;
                    }
                    let select_prob = maybe_level1.stake.inner() as f64 / stake_left.inner() as f64;
                    let full_level1_slots = validators_left / turbine_fanout;
                    let prob_full =
                        prob * (1.0 - (1.0 - select_prob).powi(full_level1_slots as i32));
                    let full_level1_work = turbine_fanout as f64;
                    expected_work[maybe_level1.id.as_index()] += prob_full * full_level1_work;
                    let prob_partial =
                        prob * (1.0 - select_prob).powi(full_level1_slots as i32) * select_prob;
                    let partial_level1_work = (validators_left % turbine_fanout) as f64;
                    expected_work[maybe_level1.id.as_index()] += prob_partial * partial_level1_work;
                }
            }
        }

        // turn expected work into stakes
        for (i, w) in expected_work.into_iter().enumerate() {
            validators[i].stake = Stake::new((w * 1_000_000_000.0) as u64);
        }

        Self {
            fanout: turbine_fanout,
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
    fn sample<R: Rng>(&self, rng: &mut R) -> ValidatorId {
        let n = self.stake_weighted.validators.len();
        let root = self.stake_weighted.sample(rng);
        if rng.random::<f64>() < self.fanout as f64 / n as f64 {
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

    fn sample_info<R: Rng>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng).as_index();
        &self.stake_weighted.validators[index]
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
/// - For `max_samples -> infinity` it approaches the behavior WITH replacement.
///
/// This sampler implements [`QuorumSamplingStrategy`] with a fixed quorum size.
/// Internal state is automatically reset after each call to [`sample_quorum`].
///
/// [`sample_quorum`]: QuorumSamplingStrategy::sample_quorum
pub struct DecayingAcceptanceSampler {
    stake_weighted: StakeWeightedSampler,
    max_samples: f64,
    sample_count: Mutex<Vec<usize>>,
    k: usize,
}

impl DecayingAcceptanceSampler {
    /// Creates a new `DecayingAcceptanceSampler` instance with the given quorum size.
    pub fn new(validators: Vec<ValidatorInfo>, max_samples: f64, k: usize) -> Self {
        let sample_count = vec![0; validators.len()];
        Self {
            stake_weighted: StakeWeightedSampler::new(validators),
            max_samples,
            sample_count: Mutex::new(sample_count),
            k,
        }
    }

    /// Resets the internal state of this stateful sampler.
    /// After resetting it is just as it was when it was first created.
    pub fn reset(&self) {
        let mut sample_count = self.sample_count.lock().unwrap();
        *sample_count = vec![0; self.stake_weighted.validators.len()];
    }

    /// Samples a single validator with the decaying acceptance distribution.
    ///
    /// This is stateful: repeated calls without [`reset`] will cause
    /// previously-sampled validators to be rejected more often.
    ///
    /// # Panics
    ///
    /// Panics if after [`MAX_TRIES_PER_SAMPLE`] samples none was valid.
    ///
    /// [`reset`]: DecayingAcceptanceSampler::reset
    pub fn sample_one<R: Rng>(&self, rng: &mut R) -> ValidatorId {
        for _ in 0..MAX_TRIES_PER_SAMPLE {
            let sample = self.stake_weighted.sample(rng);
            let mut sample_count = self.sample_count.lock().unwrap();
            let p_reject = sample_count[sample.as_index()] as f64 / self.max_samples;
            if rng.random::<f64>() >= p_reject {
                sample_count[sample.as_index()] += 1;
                return sample;
            }
        }

        panic!("rejected all {MAX_TRIES_PER_SAMPLE} samples");
    }
}

impl SamplingStrategy for DecayingAcceptanceSampler {
    fn sample<R: Rng>(&self, rng: &mut R) -> ValidatorId {
        self.sample_one(rng)
    }

    fn sample_info<R: Rng>(&self, rng: &mut R) -> &ValidatorInfo {
        let index = self.sample(rng).as_index();
        &self.stake_weighted.validators[index]
    }
}

impl QuorumSamplingStrategy for DecayingAcceptanceSampler {
    fn quorum_size(&self) -> usize {
        self.k
    }

    fn sample_quorum<R: Rng>(&self, rng: &mut R) -> Vec<ValidatorId> {
        let samples = (0..self.k).map(|_| self.sample_one(rng)).collect();
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
            k: self.k,
        }
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
#[derive(Clone)]
pub struct PartitionSampler {
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
                bins: Vec::new(),
                bin_validators: Vec::new(),
                bin_stakes: Vec::new(),
            };
        }

        let mut bin_validators = vec![Vec::new(); num_bins];
        let mut bin_stakes = vec![Vec::new(); num_bins];

        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let stake_per_bin = total_stake.div_ceil(num_bins as u64);
        let mut validators_random = validators;
        validators_random.shuffle(&mut rand::rng());

        // partition into bins
        let mut current_bin = 0;
        let mut current_bin_stake = Stake::new(0);
        for v in validators_random {
            let mut stake = v.stake;
            while stake > Stake::new(0) {
                bin_validators[current_bin].push(v.id);
                let stake_to_take = stake.min(stake_per_bin - current_bin_stake);
                current_bin_stake += stake_to_take;
                bin_stakes[current_bin].push(stake_to_take);
                stake -= stake_to_take;
                if current_bin < num_bins - 1
                    && (stake > Stake::new(0) || current_bin_stake == stake_per_bin)
                {
                    current_bin += 1;
                    current_bin_stake = Stake::new(0);
                }
            }
        }

        // generate stake weighted indices for each bin
        let mut bins = Vec::with_capacity(num_bins);
        for stakes in &bin_stakes {
            let bin = WeightedIndex::new(stakes.iter().map(|s| s.inner())).unwrap();
            bins.push(bin);
        }

        Self {
            bins,
            bin_validators,
            bin_stakes,
        }
    }
}

impl QuorumSamplingStrategy for PartitionSampler {
    fn quorum_size(&self) -> usize {
        self.bins.len()
    }

    fn sample_quorum<R: Rng>(&self, rng: &mut R) -> Vec<ValidatorId> {
        let mut samples = Vec::new();
        for (bin, validators) in self.bins.iter().zip(self.bin_validators.iter()) {
            let i = bin.sample(rng);
            samples.push(validators[i]);
        }
        samples
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
pub struct FaitAccompli1Sampler<F: QuorumSamplingStrategy> {
    required_samples: Vec<ValidatorId>,
    pub fallback_sampler: F,
    k: usize,
}

impl FaitAccompli1Sampler<PartitionSampler> {
    /// Creates a new FA1-F sampler with a variance-reducing partition fallback sampler.
    ///
    /// See [`PartitionSampler`] for more details.
    #[must_use]
    pub fn new_with_partition_fallback(validators: Vec<ValidatorInfo>, k: u64) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let mut required_samples = Vec::new();
        let mut validators_truncated_stake = validators.clone();
        for v in &mut validators_truncated_stake {
            let frac_stake = v.stake.inner() as f64 / total_stake.inner() as f64;
            let samples = (frac_stake * k as f64).floor() as u64;
            v.stake -= Stake::new(samples * total_stake.inner() / k);
            required_samples.extend((0..samples).map(|_| v.id));
        }
        let all_zero = validators_truncated_stake
            .iter()
            .all(|v| v.stake == Stake::new(0));
        let k_prime = k as usize - required_samples.len();
        let fallback_sampler = if all_zero {
            PartitionSampler::new(validators, k_prime)
        } else {
            PartitionSampler::new(validators_truncated_stake, k_prime)
        };
        Self {
            required_samples,
            fallback_sampler,
            k: k as usize,
        }
    }
}

impl FaitAccompli1Sampler<IidQuorumSampler<StakeWeightedSampler>> {
    /// Creates a new FA1-F sampler with an IID stake-weighted fallback sampler.
    ///
    /// See [`StakeWeightedSampler`] for more details.
    #[must_use]
    pub fn new_with_stake_weighted_fallback(validators: Vec<ValidatorInfo>, k: u64) -> Self {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let mut required_samples = Vec::new();
        let mut validators_truncated_stake = validators.clone();
        for v in &mut validators_truncated_stake {
            let frac_stake = v.stake.inner() as f64 / total_stake.inner() as f64;
            let samples = (frac_stake * k as f64).floor() as u64;
            v.stake -= Stake::new(samples * total_stake.inner() / k);
            required_samples.extend((0..samples).map(|_| v.id));
        }
        let all_zero = validators_truncated_stake
            .iter()
            .all(|v| v.stake == Stake::new(0));
        let k_prime = k as usize - required_samples.len();
        let fallback_sampler = if all_zero {
            StakeWeightedSampler::new(validators).into_quorum_strategy(k_prime)
        } else {
            StakeWeightedSampler::new(validators_truncated_stake).into_quorum_strategy(k_prime)
        };
        Self {
            required_samples,
            fallback_sampler,
            k: k as usize,
        }
    }
}

impl<F: QuorumSamplingStrategy> QuorumSamplingStrategy for FaitAccompli1Sampler<F> {
    fn quorum_size(&self) -> usize {
        self.k
    }

    fn sample_quorum<R: Rng>(&self, rng: &mut R) -> Vec<ValidatorId> {
        let mut result = Vec::with_capacity(self.k);
        result.extend_from_slice(&self.required_samples);
        if result.len() < self.k {
            let k_prime = self.k - result.len();
            assert_eq!(k_prime, self.fallback_sampler.quorum_size());
            let additional_samples = self.fallback_sampler.sample_quorum(rng);
            result.extend_from_slice(&additional_samples);
        }
        result
    }
}

impl<F: QuorumSamplingStrategy + Clone> Clone for FaitAccompli1Sampler<F> {
    fn clone(&self) -> Self {
        Self {
            required_samples: self.required_samples.clone(),
            fallback_sampler: self.fallback_sampler.clone(),
            k: self.k,
        }
    }
}

/// A sampler that uses the FA2 committee sampling strategy.
///
/// See also: <https://dl.acm.org/doi/pdf/10.1145/3576915.3623194>
pub struct FaitAccompli2Sampler {
    required_samples: Vec<ValidatorId>,
    medium_nodes: Vec<(ValidatorId, f64)>,
    fallback_sampler: IidQuorumSampler<StakeWeightedSampler>,
    k: usize,
}

impl FaitAccompli2Sampler {
    /// Creates a new FA2 sampler instance.
    ///
    /// This is instantiated for a fixed number of samples `k`.
    /// To this end, the FA1 and FA2 pre-processing steps are applied,
    /// and also a stake-weighted IID fallback sampler is generated.
    pub fn new(validators: Vec<ValidatorInfo>, k: u64) -> Self {
        // FA1 step
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let mut required_samples = Vec::new();
        for v in &validators {
            let frac_stake = v.stake.inner() as f64 / total_stake.inner() as f64;
            let samples = (frac_stake * k as f64).floor() as u64;
            required_samples.extend((0..samples).map(|_| v.id));
        }

        // FA2 step
        let f = Self::minimize_f(&validators, k);
        let mut medium_nodes = Vec::new();
        for (i, fi) in f.iter().enumerate() {
            let rel_stake = validators[i].stake.inner() as f64 / total_stake.inner() as f64;
            if *fi > rel_stake {
                let p = 1.0 - (fi - rel_stake) * k as f64;
                medium_nodes.push((ValidatorId::new(i as u64), p));
            }
        }

        // generate stake-weighted IID fallback sampler
        let r: f64 = validators
            .iter()
            .enumerate()
            .filter(|(i, v)| v.stake.inner() as f64 / total_stake.inner() as f64 > f[*i])
            .map(|(i, v)| v.stake.inner() as f64 / total_stake.inner() as f64 - f[i])
            .sum();
        let new_stake_distribution: Vec<ValidatorInfo> = validators
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, mut v)| {
                if v.stake.inner() as f64 / total_stake.inner() as f64 > f[i] {
                    v.stake = Stake::new(
                        ((v.stake.inner() as f64 / total_stake.inner() as f64 - f[i]) / r
                            * total_stake.inner() as f64) as u64,
                    );
                } else {
                    v.stake = Stake::new(0);
                }
                v
            })
            .collect();
        // The fallback quorum size is an upper bound; FA2's sample_quorum may request
        // fewer samples depending on how many medium nodes were included.
        let fallback_k = k as usize - required_samples.len();
        let fallback_sampler = if r == 0.0 {
            StakeWeightedSampler::new(validators).into_quorum_strategy(fallback_k)
        } else {
            StakeWeightedSampler::new(new_stake_distribution).into_quorum_strategy(fallback_k)
        };

        Self {
            required_samples,
            medium_nodes,
            fallback_sampler,
            k: k as usize,
        }
    }

    fn minimize_f(validators: &[ValidatorInfo], k: u64) -> Vec<f64> {
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let f: Vec<f64> = validators
            .iter()
            .map(|v| {
                (v.stake.inner() as f64 / total_stake.inner() as f64 * k as f64).round() / k as f64
            })
            .collect();
        assert!(f.iter().sum::<f64>() <= 1.0);
        f
    }
}

impl QuorumSamplingStrategy for FaitAccompli2Sampler {
    fn quorum_size(&self) -> usize {
        self.k
    }

    fn sample_quorum<R: Rng>(&self, rng: &mut R) -> Vec<ValidatorId> {
        // add required FA1 samples
        let mut result = Vec::with_capacity(self.k);
        result.extend_from_slice(&self.required_samples);

        // sample medium nodes (FA2 step)
        for (validator, probability) in &self.medium_nodes {
            if rng.random_bool(*probability) {
                result.push(*validator);
            }
        }

        // sample remaining validators IID stake-weighted
        if result.len() < self.k {
            let k_prime = self.k - result.len();
            let additional_samples: Vec<_> = (0..k_prime)
                .map(|_| self.fallback_sampler.inner.sample(rng))
                .collect();
            result.extend_from_slice(&additional_samples);
        }

        result
    }
}

impl Clone for FaitAccompli2Sampler {
    fn clone(&self) -> Self {
        Self {
            required_samples: self.required_samples.clone(),
            medium_nodes: self.medium_nodes.clone(),
            fallback_sampler: self.fallback_sampler.clone(),
            k: self.k,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::ValidatorId;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::disseminator::turbine::WeightedShuffle;
    use crate::network::dontcare_sockaddr;
    use crate::network::simulated::stake_distribution::{VALIDATOR_DATA, ValidatorData};
    use crate::shredder::TOTAL_SHREDS;

    fn create_validator_info(count: u64) -> Vec<ValidatorInfo> {
        let mut validators = Vec::new();
        for i in 0..count {
            let sk = SecretKey::new(&mut rand::rng());
            let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
            validators.push(ValidatorInfo {
                id: ValidatorId::new(i),
                stake: Stake::new(1),
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: dontcare_sockaddr(),
                disseminator_address: dontcare_sockaddr(),
                repair_request_address: dontcare_sockaddr(),
                repair_response_address: dontcare_sockaddr(),
            });
        }
        validators
    }

    #[test]
    fn all_same_sampler() {
        let validators = create_validator_info(10);
        let sampler = AllSameSampler(validators[3].clone());
        let mut rng = rand::rng();
        for _ in 0..1000 {
            assert_eq!(sampler.sample(&mut rng), ValidatorId::new(3));
            assert_eq!(sampler.sample_info(&mut rng).id, ValidatorId::new(3));
        }

        let quorum = sampler.into_quorum_strategy(TOTAL_SHREDS);
        for _ in 0..10 {
            let sampled_vals = quorum.sample_quorum(&mut rng);
            for val in sampled_vals {
                assert_eq!(val, ValidatorId::new(3));
            }
        }
    }

    #[test]
    fn uniform_sampler() {
        // apply Hoeffding's bound to number of different samples
        let validators = create_validator_info(1000);
        let sampler = UniformSampler::new(validators).into_quorum_strategy(1000);
        let sampled = sampler.sample_quorum(&mut rand::rng());
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
        validators[0].stake = Stake::new(1_000_000_000);
        let sampler = UniformSampler::new(validators).into_quorum_strategy(1000);
        let sampled = sampler.sample_quorum(&mut rand::rng());
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
            validators[i].stake = Stake::new(1_000_000_000);
        }
        let sampler = UniformSampler::new(validators).into_quorum_strategy(1000);
        let sampled = sampler.sample_quorum(&mut rand::rng());
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
        let sampler = StakeWeightedSampler::new(validators).into_quorum_strategy(1000);
        let sampled = sampler.sample_quorum(&mut rand::rng());
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
        validators[0].stake = Stake::new(1_000_000_000);
        let sampler = StakeWeightedSampler::new(validators);
        assert_eq!(sampler.sample(&mut rand::rng()), ValidatorId::new(0));
        let quorum = sampler.into_quorum_strategy(100);
        let sampled = quorum.sample_quorum(&mut rand::rng());
        let sampled0 = sampled
            .into_iter()
            .filter(|v| *v == ValidatorId::new(0))
            .count();
        assert!(sampled0 == 100);
    }

    #[test]
    fn decaying_acceptance_sampler() {
        // max_samples = 1 equivalent to sampling w/o replacement
        let validators = create_validator_info(100);
        let sampler = DecayingAcceptanceSampler::new(validators, 1.0, 100);
        let sampled = sampler.sample_quorum(&mut rand::rng());
        let sampled_set: HashSet<_> = sampled.iter().copied().collect();
        assert_eq!(sampled_set.len(), 100);

        // heavy node sampled at most max_samples times
        let mut validators = create_validator_info(100);
        validators[0].stake = Stake::new(10_000);
        let sampler = DecayingAcceptanceSampler::new(validators, 5.0, 100);
        let sampled = sampler.sample_quorum(&mut rand::rng());
        let sampled0 = sampled
            .into_iter()
            .filter(|v| *v == ValidatorId::new(0))
            .count();
        assert!(sampled0 <= 5);

        // max_samples = inf equivalent to sampling with replacement
        let mut validators = create_validator_info(100);
        validators[0].stake = Stake::new(1_000_000_000);
        let sampler = DecayingAcceptanceSampler::new(validators, f64::INFINITY, 100);
        assert_eq!(sampler.sample_one(&mut rand::rng()), ValidatorId::new(0));
        sampler.reset();
        let sampled = sampler.sample_quorum(&mut rand::rng());
        let sampled0 = sampled
            .into_iter()
            .filter(|v| *v == ValidatorId::new(0))
            .count();
        assert_eq!(sampled0, 100);

        // test `clone` and `reset`
        // resetting after each iteration should behave the same as `max_samples = inf`
        let mut sampler = sampler.clone();
        sampler.max_samples = 5.0;
        for _ in 0..100 {
            sampler.reset();
            let id = sampler.sample_one(&mut rand::rng());
            assert_eq!(id, ValidatorId::new(0));
        }
    }

    #[test]
    #[ignore]
    fn turbine_sampler() {
        const SLICES: usize = 100_000;

        let mut rng = rand::rng();
        let mut validators = create_validator_info(1000);
        // two large nodes with roughly 5% of the stake each
        validators[0].stake = Stake::new(55);
        validators[1].stake = Stake::new(55);
        let total_stake =
            Stake::new(validators.len() as u64 - 2) + validators[0].stake + validators[1].stake;

        // calculate work expected with `TurbineSampler`
        let sampler =
            TurbineSampler::new(validators.clone()).into_quorum_strategy(TOTAL_SHREDS * SLICES);
        let sampled = sampler.sample_quorum(&mut rng);
        let appearances0 = sampled
            .iter()
            .filter(|v| **v == ValidatorId::new(0))
            .count();
        let appearances1 = sampled
            .iter()
            .filter(|v| **v == ValidatorId::new(1))
            .count();
        let work0 = ((TOTAL_SHREDS * SLICES) as u64 * validators[0].stake.inner()
            / total_stake.inner())
            + (appearances0 * (validators.len() - 2)) as u64;
        let work1 = ((TOTAL_SHREDS * SLICES) as u64 * validators[1].stake.inner()
            / total_stake.inner())
            + (appearances1 * (validators.len() - 2)) as u64;

        // simulate and count work required with actual `Turbine`
        let mut turbine_work = [0, 0];
        let mut rng = SmallRng::from_rng(&mut rand::rng());
        for _ in 0..TOTAL_SHREDS * SLICES {
            let mut weighted_shuffle = WeightedShuffle::new(validators.iter().map(|v| v.stake));
            let mut validator_ids = weighted_shuffle
                .shuffle(&mut rng)
                .map(|i| ValidatorId::new(i as u64));

            // leader work
            let leader = validator_ids.next().unwrap();
            if leader == ValidatorId::new(0) || leader == ValidatorId::new(1) {
                turbine_work[leader.as_index()] += 1;
            }
            // root work
            assert!(validators.len() > DEFAULT_FANOUT + 2);
            let root = validator_ids.next().unwrap();
            if root == ValidatorId::new(0) || root == ValidatorId::new(1) {
                turbine_work[root.as_index()] += DEFAULT_FANOUT;
            }
            // layer-1 work
            let mut validators_left = validators.len() - 2 - DEFAULT_FANOUT;
            for _ in 0..DEFAULT_FANOUT {
                let parent = validator_ids.next().unwrap().as_index();
                if parent == 0 || parent == 1 {
                    let work = DEFAULT_FANOUT.min(validators_left);
                    turbine_work[parent] += work;
                }
                if validators_left <= DEFAULT_FANOUT {
                    break;
                }
                validators_left -= DEFAULT_FANOUT;
            }
        }

        // compare the two
        const TOLERANCE: f64 = 0.05;
        let rel_workload0 = turbine_work[0] as f64 / work0 as f64;
        println!("{rel_workload0}");
        assert!(rel_workload0 > 1.0 - TOLERANCE);
        assert!(rel_workload0 < 1.0 + TOLERANCE);
        let rel_workload1 = turbine_work[1] as f64 / work1 as f64;
        println!("{rel_workload1}");
        assert!(rel_workload1 > 1.0 - TOLERANCE);
        assert!(rel_workload1 < 1.0 + TOLERANCE);
    }

    #[test]
    #[ignore]
    fn turbine_sampler_real_world() {
        const SLICES: usize = 100_000;

        // use real mainnet validator stake distribution
        let stakes = VALIDATOR_DATA
            .iter()
            .filter_map(ValidatorData::active_stake)
            .collect::<Vec<_>>();
        let total_stake: Stake = stakes.iter().copied().sum();
        let mut validators = create_validator_info(stakes.len() as u64);
        for (i, stake) in stakes.into_iter().enumerate() {
            validators[i].stake = stake;
        }

        // calculate work expected with `TurbineSampler`
        let mut rng = SmallRng::from_rng(&mut rand::rng());
        let sampler =
            TurbineSampler::new(validators.clone()).into_quorum_strategy(TOTAL_SHREDS * SLICES);
        let mut expected_work = vec![0; validators.len()];
        let relays = sampler.sample_quorum(&mut rng);
        for (v, stake) in validators.iter().map(|v| v.stake).enumerate() {
            let appearances = relays
                .iter()
                .filter(|val| **val == ValidatorId::new(v as u64))
                .count();
            let fractional_stake = stake.inner() as f64 / total_stake.inner() as f64;
            let leader_work = ((TOTAL_SHREDS * SLICES) as f64 * fractional_stake) as u64;
            let relay_work = (appearances * (validators.len() - 2)) as u64;
            expected_work[v] = leader_work + relay_work;
        }

        // simulate and count work required with actual `Turbine`
        let mut turbine_workload = vec![0; validators.len()];
        for _ in 0..TOTAL_SHREDS * SLICES {
            let mut weighted_shuffle = WeightedShuffle::new(validators.iter().map(|v| v.stake));
            let mut validator_ids = weighted_shuffle
                .shuffle(&mut rng)
                .map(|i| ValidatorId::new(i as u64));

            // leader work
            let leader = validator_ids.next().unwrap();
            turbine_workload[leader.as_index()] += 1;
            // root work
            assert!(validators.len() > DEFAULT_FANOUT + 2);
            let root = validator_ids.next().unwrap();
            turbine_workload[root.as_index()] += DEFAULT_FANOUT;
            // level-1 work
            let mut validators_left = validators.len() - 2 - DEFAULT_FANOUT;
            for _ in 0..DEFAULT_FANOUT {
                let parent = validator_ids.next().unwrap().as_index();
                turbine_workload[parent] += DEFAULT_FANOUT.min(validators_left);
                if validators_left < DEFAULT_FANOUT {
                    break;
                }
                validators_left -= DEFAULT_FANOUT;
            }
        }

        // compare the two
        const TOLERANCE: f64 = 0.05;
        for (tw, sw) in turbine_workload.into_iter().zip(expected_work) {
            // ignore very small validators
            if tw as f64 / (TOTAL_SHREDS * SLICES * (validators.len() - 1)) as f64 <= 0.001 {
                continue;
            }
            let rel_workload = tw as f64 / sw as f64;
            assert!(rel_workload > 1.0 - TOLERANCE);
            assert!(rel_workload < 1.0 + TOLERANCE);
        }
    }

    #[test]
    fn partition_sampler() {
        // with k equal-weight nodes this deterministically selects all nodes
        let validators = create_validator_info(64);
        let sampler = PartitionSampler::new(validators, 64);
        assert_eq!(sampler.quorum_size(), 64);
        let sampled = sampler.sample_quorum(&mut rand::rng());
        assert_eq!(sampled.len(), 64);
        let sampled: HashSet<_> = sampled.into_iter().collect();
        assert_eq!(sampled.len(), 64);
        for id in 0..64 {
            assert!(sampled.contains(&ValidatorId::new(id)));
        }
    }

    #[test]
    fn fa1_sampler() {
        // with k equal-weight nodes this deterministically selects all nodes
        let validators = create_validator_info(64);
        let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators, 64);
        assert_eq!(sampler.quorum_size(), 64);
        let sampled = sampler.sample_quorum(&mut rand::rng());
        assert_eq!(sampled.len(), 64);
        let sampled: HashSet<_> = sampled.into_iter().collect();
        assert_eq!(sampled.len(), 64);
        for id in 0..64 {
            assert!(sampled.contains(&ValidatorId::new(id)));
        }

        // with k equal-weight nodes this deterministically selects all nodes
        // (also for partitioning fallback sampler)
        let validators = create_validator_info(64);
        let sampler = FaitAccompli1Sampler::new_with_partition_fallback(validators, 64);
        assert_eq!(sampler.quorum_size(), 64);
        let sampled = sampler.sample_quorum(&mut rand::rng());
        assert_eq!(sampled.len(), 64);
        let sampled: HashSet<_> = sampled.into_iter().collect();
        assert_eq!(sampled.len(), 64);
        for id in 0..64 {
            assert!(sampled.contains(&ValidatorId::new(id)));
        }

        // with many low-stake nodes this becomes the underlying fallback distribution
        let mut avg_max_appearances = 0.0;
        for _ in 0..20 {
            let validators = create_validator_info(1000);
            let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators, 64);
            let sampled = sampler.sample_quorum(&mut rand::rng());
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
        validators[0].stake = Stake::new(52);
        validators[1].stake = Stake::new(52);
        let sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators, 64);
        let sampled = sampler.sample_quorum(&mut rand::rng());
        assert_eq!(sampled.len(), 64);
        let sampled0 = sampled
            .iter()
            .filter(|v| **v == ValidatorId::new(0))
            .count();
        let sampled1 = sampled
            .iter()
            .filter(|v| **v == ValidatorId::new(1))
            .count();
        assert!(sampled0 >= 3);
        assert!(sampled1 >= 3);
    }

    #[test]
    fn fa2_sampler() {
        // with k equal-weight nodes this deterministically selects all nodes
        let validators = create_validator_info(64);
        let sampler = FaitAccompli2Sampler::new(validators, 64);
        assert_eq!(sampler.quorum_size(), 64);
        let sampled = sampler.sample_quorum(&mut rand::rng());
        assert_eq!(sampled.len(), 64);
        let sampled: HashSet<_> = sampled.into_iter().collect();
        assert_eq!(sampled.len(), 64);
        for id in 0..64 {
            assert!(sampled.contains(&ValidatorId::new(id)));
        }
    }

    #[test]
    fn iid_quorum_sampler() {
        // wrapping a stake-weighted sampler with a fixed quorum size
        let validators = create_validator_info(100);
        let sampler = StakeWeightedSampler::new(validators).into_quorum_strategy(32);
        assert_eq!(sampler.quorum_size(), 32);
        let sampled = sampler.sample_quorum(&mut rand::rng());
        assert_eq!(sampled.len(), 32);

        // IidQuorumSampler also forwards single-node sampling
        let validators = create_validator_info(100);
        let sampler = StakeWeightedSampler::new(validators).into_quorum_strategy(32);
        let mut rng = rand::rng();
        let id = sampler.sample(&mut rng);
        assert!(id.as_index() < 100);
    }

    #[test]
    fn completeness() {
        let validators = create_validator_info(10);
        sample_all_validators(&UniformSampler::new(validators.clone()));
        sample_all_validators(&StakeWeightedSampler::new(validators.clone()));
        sample_all_validators(&TurbineSampler::new(validators.clone()));
    }

    fn sample_all_validators<S: SamplingStrategy>(sampler: &S) {
        let mut rng = rand::rng();
        let mut sampled1 = HashSet::new();
        let mut sampled2 = HashSet::new();
        for _ in 0..1000 {
            sampled1.insert(sampler.sample(&mut rng));
            sampled2.insert(sampler.sample_info(&mut rng).id);
        }
        for id in 0..10 {
            assert!(sampled1.contains(&ValidatorId::new(id)));
            assert!(sampled2.contains(&ValidatorId::new(id)));
        }
    }
}
