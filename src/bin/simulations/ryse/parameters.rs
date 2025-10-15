// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parameters for Ryse, the MCP protocol.
//!
//!

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use log::info;
use rand::prelude::*;
use statrs::distribution::{Binomial, DiscreteCDF};

use crate::discrete_event_simulator::Builder;

/// Parameters for the Ryse MCP protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RyseParameters {
    /// Number of slices in a block.
    pub num_slices: u64,
    /// Number of leaders concurrently proposing in each slot.
    pub num_leaders: u64,
    /// Number of relays to use in the modified Rotor disseminator.
    pub num_relays: u64,
    /// Number of shreds required to successfully decode a block.
    pub decode_threshold: u64,
    /// Number of relays' signatures required for a block to become notarized.
    pub relay_notar_threshold: u64,
}

/// Specific instance of the Ryse protocol.
#[derive(Clone, Debug)]
pub struct RyseInstance {
    pub leaders: Vec<ValidatorId>,
    pub relays: Vec<Vec<ValidatorId>>,
}

/// Builder for Ryse instances with a specific set of parameters.
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
            relays: (0..self.params.num_slices)
                .map(|_| {
                    self.relay_sampler
                        .sample_multiple(self.params.num_relays as usize, rng)
                })
                .collect(),
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

impl RyseParameters {
    /// Generates a new balanced parameter set, equally resistant against all attacks.
    pub fn new(num_leaders: u64, num_relays: u64) -> Self {
        Self {
            num_leaders,
            num_relays,
            num_slices: 1,
            decode_threshold: (num_relays * 50).div_ceil(100),
            relay_notar_threshold: (num_relays * 60).div_ceil(100),
        }
    }

    /// Creates a new builder instance, with the provided sampling strategies.
    pub fn optmize(&self, adv_strength: AdversaryStrength) -> Self {
        let mut optimal_params = *self;
        let mut optimal_attack_prob = self.any_attack_probability(adv_strength);

        for relay_notar_threshold in 1..self.num_relays {
            for decode_threshold in 1..relay_notar_threshold {
                let new_params = RyseParameters {
                    num_leaders: self.num_leaders,
                    num_relays: self.num_relays,
                    num_slices: self.num_slices,
                    decode_threshold,
                    relay_notar_threshold,
                };
                let attack_prob = new_params.any_attack_probability(adv_strength);
                if attack_prob < optimal_attack_prob {
                    optimal_params = new_params;
                    optimal_attack_prob = attack_prob;
                }
            }
        }

        optimal_params
    }

    /// Returns the probability that the adversary can make any attack in a slot.
    pub fn any_attack_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        self.break_hiding_probability(adv_strength)
            .max(self.selective_censorship_probability(adv_strength))
            .max(self.temporary_liveness_failure_probability(adv_strength))
    }

    /// Probability that the adversary can break the hiding property in a slot.
    ///
    /// This attack is easier for the adversary if no nodes are crashed.
    /// So, this is the case that we consider here to get a worst-case analysis.
    pub fn break_hiding_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that the adversary controls enough relays to decrypt before proposing
        let byzantine = adv_strength.byzantine;
        let relays_dist = Binomial::new(byzantine, self.num_relays).unwrap();
        let relays_needed =
            (self.relay_notar_threshold + self.decode_threshold).saturating_sub(self.num_relays);
        1.0 - relays_dist.cdf(relays_needed.saturating_sub(1))
    }

    /// Probability that the adversary can selectively censor leaders in a slot.
    pub fn selective_censorship_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that only the adversary proposes
        let failed = adv_strength.crashed + adv_strength.byzantine;
        let leaders_dist = Binomial::new(failed, self.num_leaders).unwrap();
        let prob_all_leaders = 1.0 - leaders_dist.cdf(self.num_leaders - 1);

        // probability that the adversary can exclude all leaders
        let relays_dist = Binomial::new(failed, self.num_relays).unwrap();
        let relays_needed = self.num_relays - self.relay_notar_threshold;
        let prob_censor_relays = 1.0 - relays_dist.cdf(relays_needed - 1);

        // probability that either attack works
        1.0 - (1.0 - prob_all_leaders) * (1.0 - prob_censor_relays)
    }

    /// Probability that the adversary can cause a temporary liveness failure in a slot.
    pub fn temporary_liveness_failure_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // there is no better liveness attack than the selective-censorship attack
        self.selective_censorship_probability(adv_strength)
    }

    /// Calculates the attack probabilities and prints them.
    ///
    /// Capabilities of the adversary are specified in the `adv_strength` parameter.
    pub fn print_failure_probabilities(&self, adv_strength: AdversaryStrength) {
        info!(
            "Ryse parameters: leaders={}, relays={}, {:.2}/{:.2}",
            self.num_leaders,
            self.num_relays,
            self.decode_threshold as f64 / self.num_relays as f64 * 100.0,
            self.relay_notar_threshold as f64 / self.num_relays as f64 * 100.0,
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
        let params = RyseParameters::new(2, 10);
        assert_eq!(params.num_leaders, 2);
        assert_eq!(params.num_relays, 10);
        assert_eq!(params.decode_threshold, 5);
        assert_eq!(params.relay_notar_threshold, 6);
    }
}
