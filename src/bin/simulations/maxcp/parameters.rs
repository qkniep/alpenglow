// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parameters for MaxCP, the MCP protocol.
//!
//!

use std::time::Duration;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use log::info;
use rand::prelude::*;
use statrs::distribution::{Binomial, DiscreteCDF};

use crate::discrete_event_simulator::Builder;

/// Parameters for the MaxCP MCP protocol.
#[derive(Clone, Copy, Debug)]
pub struct MaxcpParameters {
    pub num_proposers: u64,
    pub num_attestors: u64,
    pub num_relays: u64,
    pub can_decode_proposal_threshold: u64,
    pub can_decode_block_threshold: u64,
    pub should_decode_threshold: u64,
    pub attestations_threshold: u64,
    pub slot_time: Duration,
    pub num_batches: u64,
    pub slices_per_batch: u64,
    pub quick_release: bool,
}

/// Specific instance of the MaxCP protocol.
pub struct MaxcpInstance {
    pub leader: ValidatorId,
    pub proposers: Vec<ValidatorId>,
    pub relays: Vec<ValidatorId>,
    pub params: MaxcpParameters,
}

/// Builder for MaxCP instances with a specific set of parameters.
pub struct MaxcpInstanceBuilder<
    L: SamplingStrategy,
    P: SamplingStrategy,
    A: SamplingStrategy,
    R: SamplingStrategy,
> {
    leader_sampler: L,
    proposer_sampler: P,
    attestor_sampler: A,
    relay_sampler: R,
    params: MaxcpParameters,
}

impl<L, P, A, R> MaxcpInstanceBuilder<L, P, A, R>
where
    L: SamplingStrategy,
    P: SamplingStrategy,
    A: SamplingStrategy,
    R: SamplingStrategy,
{
    /// Creates a new builder instance, with the provided sampling strategies.
    pub fn new(
        leader_sampler: L,
        proposer_sampler: P,
        attestor_sampler: A,
        relay_sampler: R,
        params: MaxcpParameters,
    ) -> Self {
        Self {
            leader_sampler,
            proposer_sampler,
            attestor_sampler,
            relay_sampler,
            params,
        }
    }
}

impl<L, P, A, R> Builder for MaxcpInstanceBuilder<L, P, A, R>
where
    L: SamplingStrategy,
    P: SamplingStrategy,
    A: SamplingStrategy,
    R: SamplingStrategy,
{
    type Params = MaxcpParameters;
    type Instance = MaxcpInstance;

    fn build(&self, rng: &mut impl Rng) -> MaxcpInstance {
        MaxcpInstance {
            leader: self.leader_sampler.sample(rng),
            proposers: self
                .proposer_sampler
                .sample_multiple(self.params.num_proposers as usize, rng),
            relays: self
                .relay_sampler
                .sample_multiple(self.params.num_relays as usize, rng),
            params: self.params,
        }
    }

    fn params(&self) -> &Self::Params {
        &self.params
    }
}

/// Adversary strength.
#[derive(Clone, Copy, Debug)]
pub struct AdversaryStrength {
    pub crashed: f64,
    pub byzantine: f64,
}

impl MaxcpParameters {
    /// Generates a new balanced parameter set, equally resistant against all attacks.
    pub fn new(num_proposers: u64, num_attestors: u64, num_relays: u64) -> Self {
        Self {
            num_proposers,
            num_attestors,
            num_relays,
            can_decode_proposal_threshold: (num_attestors * 25).div_ceil(100),
            can_decode_block_threshold: (num_relays * 50).div_ceil(100),
            should_decode_threshold: (num_attestors * 25).div_ceil(100),
            attestations_threshold: (num_attestors * 50).div_ceil(100),
            slot_time: Duration::from_millis(400),
            num_batches: 20,
            slices_per_batch: 1,
            quick_release: false,
        }
    }

    /// Generates a new parameter set where attestors release shreds themselves.
    pub fn new_quick_release(num_proposers: u64, num_attestors: u64, num_relays: u64) -> Self {
        Self {
            num_proposers,
            num_attestors,
            num_relays,
            can_decode_proposal_threshold: (num_attestors * 40).div_ceil(100),
            can_decode_block_threshold: (num_relays * 50).div_ceil(100),
            should_decode_threshold: (num_attestors * 60).div_ceil(100),
            attestations_threshold: (num_attestors * 80).div_ceil(100),
            slot_time: Duration::from_millis(400),
            num_batches: 20,
            slices_per_batch: 1,
            quick_release: true,
        }
    }

    /// Proobability that the adversary can break the hiding property in a slot.
    pub fn break_hiding_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that the adversary controls enough attestors to decrypt
        let byzantine = adv_strength.byzantine;
        let attestors_dist = Binomial::new(byzantine, self.num_attestors).unwrap();
        let attestors_needed = self.can_decode_proposal_threshold;
        1.0 - attestors_dist.cdf(attestors_needed - 1)
    }

    /// Probability that the adversary can selectively censor proposers in a slot.
    //
    // just as hard with `num_relays - attestations_threshold` crashed nodes
    pub fn selective_censorship_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that only the adversary proposes
        let failed = adv_strength.crashed + adv_strength.byzantine;
        let proposers_dist = Binomial::new(failed, self.num_proposers).unwrap();
        let prob_all_proposers = 1.0 - proposers_dist.cdf(self.num_proposers - 1);

        // probability that the adversary can exclude all proposers
        let byzantine = adv_strength.byzantine;
        let attestors_dist = Binomial::new(byzantine, self.num_attestors).unwrap();
        let attestors_needed = self.attestations_threshold - self.should_decode_threshold;
        let prob_censor_attestors = 1.0 - attestors_dist.cdf(attestors_needed - 1);

        // probability that either attack works
        1.0 - (1.0 - prob_all_proposers) * (1.0 - prob_censor_attestors)
    }

    /// Probability that the adversary can cause a temporary liveness failure in a slot.
    pub fn temporary_liveness_failure_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that only the adversary proposes
        let failed = adv_strength.crashed + adv_strength.byzantine;
        let proposers_dist = Binomial::new(failed, self.num_proposers).unwrap();
        let prob_no_proposals = 1.0 - proposers_dist.cdf(self.num_proposers - 1);

        // probability that the adversary can prevent the leader from producing a non-empty block
        let attestors_dist = Binomial::new(failed, self.num_attestors).unwrap();
        let attestors_to_hold_protocol =
            self.should_decode_threshold - self.can_decode_proposal_threshold;
        let attestors_to_censor_proposers =
            self.attestations_threshold - self.should_decode_threshold;
        let attestors_to_censor_leader = self.num_attestors - self.attestations_threshold;
        let attestors_needed = attestors_to_hold_protocol
            .min(attestors_to_censor_proposers)
            .min(attestors_to_censor_leader);
        let prob_censor_attestors = 1.0 - attestors_dist.cdf(attestors_needed - 1);

        // probability that the adversary can prevent Rotor from forwarding block
        let relays_dist = Binomial::new(failed, self.num_relays).unwrap();
        let relays_needed = self.num_relays - self.can_decode_block_threshold;
        let prob_censor_relays = 1.0 - relays_dist.cdf(relays_needed - 1);

        // probability that any attack works
        1.0 - (1.0 - prob_no_proposals) * (1.0 - prob_censor_attestors) * (1.0 - prob_censor_relays)
    }

    /// Calculates and prints attack sucess probabilities.
    ///
    /// Capabilities of the adversary are specified in the `adv_strength` parameter.
    pub fn print_failure_probabilities(&self, adv_strength: AdversaryStrength) {
        info!(
            "MaxCP parameters: proposers={}, relays={}, {:.2}/{:.2}/{:.2}/{:.2}",
            self.num_proposers,
            self.num_relays,
            self.can_decode_proposal_threshold as f64 / self.num_relays as f64 * 100.0,
            self.can_decode_block_threshold as f64 / self.num_relays as f64 * 100.0,
            self.should_decode_threshold as f64 / self.num_relays as f64 * 100.0,
            self.attestations_threshold as f64 / self.num_relays as f64 * 100.0
        );
        info!(
            "successful attack probabilities (crashed={}, byzantine={}):",
            adv_strength.crashed, adv_strength.byzantine
        );
        info!(
            "break hiding: {:.2}",
            self.break_hiding_probability(adv_strength).log10()
        );
        info!(
            "selective censorship: {:.2}",
            self.selective_censorship_probability(adv_strength).log10()
        );
        info!(
            "temporary liveness failure: {:.2}",
            self.temporary_liveness_failure_probability(adv_strength)
                .log10()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_maxcp_params() {
        let params = MaxcpParameters::new(2, 100, 50);
        assert_eq!(params.num_proposers, 2);
        assert_eq!(params.num_attestors, 100);
        assert_eq!(params.num_relays, 50);
        assert_eq!(params.can_decode_proposal_threshold, 25);
        assert_eq!(params.can_decode_block_threshold, 25);
        assert_eq!(params.should_decode_threshold, 25);
        assert_eq!(params.attestations_threshold, 50);
    }

    #[test]
    fn test_maxcp_quick_release_params() {
        let params = MaxcpParameters::new_quick_release(2, 100, 50);
        assert_eq!(params.num_proposers, 2);
        assert_eq!(params.num_attestors, 100);
        assert_eq!(params.num_relays, 50);
        assert_eq!(params.can_decode_proposal_threshold, 20);
        assert_eq!(params.can_decode_block_threshold, 25);
        assert_eq!(params.should_decode_threshold, 40);
        assert_eq!(params.attestations_threshold, 60);
    }
}
