// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parameters for Ryse, the MCP protocol.
//!
//!

use alpenglow::{ValidatorId, disseminator::rotor::SamplingStrategy};
use log::info;
use rand::prelude::*;
use statrs::distribution::{Binomial, DiscreteCDF};

use crate::discrete_event_simulator::Builder;

/// Parameters for the Ryse MCP protocol.
#[derive(Clone, Copy, Debug)]
pub struct RyseParameters {
    num_leaders: u64,
    num_relays: u64,
    can_decode_threshold: u64,
    should_decode_threshold: u64,
}

pub struct RyseInstance {
    leaders: Vec<ValidatorId>,
    relays: Vec<ValidatorId>,
    params: RyseParameters,
}

pub struct RyseInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    leader_sampler: L,
    relay_sampler: R,
    params: RyseParameters,
}

impl<L: SamplingStrategy, R: SamplingStrategy> RyseInstanceBuilder<L, R> {
    /// Creates a new builder instance, with the provided sampling strategies.
    pub fn new(leader_sampler: L, relay_sampler: R, params: RyseParameters) -> Self {
        Self {
            leader_sampler,
            relay_sampler,
            params,
        }
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> Builder for RyseInstanceBuilder<L, R> {
    type Params = RyseParameters;
    type Instance = RyseInstance;

    fn build(&self, rng: &mut impl Rng) -> RyseInstance {
        RyseInstance {
            leaders: self
                .leader_sampler
                .sample_multiple(self.params.num_leaders as usize, rng),
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

/// Specific instantiation of the adversary's strength for MPC.
#[derive(Clone, Copy, Debug)]
pub struct SpecificAdversaryStrength {
    is_leader: bool,
    crashed_proposers: u64,
    byzantine_proposers: u64,
    crashed_relays: u64,
    byzantine_relays: u64,
}

impl RyseParameters {
    /// Generates a new balanced parameter set, equally resistant against all attacks.
    pub fn new(num_leaders: u64, num_relays: u64) -> Self {
        Self {
            num_leaders,
            num_relays,
            can_decode_threshold: (num_relays * 50).div_ceil(100),
            should_decode_threshold: (num_relays * 60).div_ceil(100),
        }
    }

    /// Proobability that the adversary can break the hiding property in a slot.
    pub fn break_hiding_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that the adversary controls enough relays to decrypt
        let byzantine = adv_strength.byzantine;
        let relays_dist = Binomial::new(byzantine, self.num_relays).unwrap();
        let relays_needed = self.should_decode_threshold - self.can_decode_threshold;
        1.0 - relays_dist.cdf(relays_needed - 1)
    }

    /// Probability that the adversary can selectively censor proposers in a slot.
    pub fn selective_censorship_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that only the adversary proposes
        let failed = adv_strength.crashed + adv_strength.byzantine;
        let proposers_dist = Binomial::new(failed, self.num_leaders).unwrap();
        let prob_all_proposers = 1.0 - proposers_dist.cdf(self.num_leaders - 1);

        // probability that the adversary can exclude all proposers
        let relays_dist = Binomial::new(failed, self.num_relays).unwrap();
        let relays_needed = self.num_relays - self.should_decode_threshold;
        let prob_censor_relays = 1.0 - relays_dist.cdf(relays_needed - 1);

        // probability that either attack works
        1.0 - (1.0 - prob_all_proposers) * (1.0 - prob_censor_relays)
    }

    /// Probability that the adversary can cause a temporary liveness failure in a slot.
    pub fn temporary_liveness_failure_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // there is no better liveness attack than the selective-censorship attack
        self.selective_censorship_probability(adv_strength)
    }

    ///
    pub fn print_failure_probabilities(&self, adv_strength: AdversaryStrength) {
        info!(
            "Ryse parameters: leaders={}, relays={}, {:.2}/{:.2}",
            self.num_leaders,
            self.num_relays,
            self.can_decode_threshold as f64 / self.num_relays as f64 * 100.0,
            self.should_decode_threshold as f64 / self.num_relays as f64 * 100.0,
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
    fn test_mcp_parameters() {
        let params = RyseParameters::new(2, 5);
        assert_eq!(params.num_leaders, 2);
        assert_eq!(params.num_relays, 5);
        assert_eq!(params.can_decode_threshold, 2);
        assert_eq!(params.should_decode_threshold, 3);
    }
}
