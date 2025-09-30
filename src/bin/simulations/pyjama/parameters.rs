// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parameters for Pyjama, the MCP protocol.
//!
//!

use alpenglow::{ValidatorId, disseminator::rotor::SamplingStrategy};
use log::info;
use statrs::distribution::{Binomial, DiscreteCDF};

/// Parameters for the MCP protocol.
#[derive(Clone, Copy, Debug)]
pub struct PyjamaParameters {
    num_proposers: u64,
    num_relays: u64,
    can_decode_threshold: u64,
    should_decode_threshold: u64,
    attestations_threshold: u64,
}

pub struct PyjamaInstance {
    proposers: Vec<ValidatorId>,
    relays: Vec<ValidatorId>,
    params: PyjamaParameters,
}

pub struct PyjamaInstanceBuilder<L: SamplingStrategy, P: SamplingStrategy, R: SamplingStrategy> {
    leader_sampler: L,
    proposer_sampler: P,
    relay_sampler: R,
    params: PyjamaParameters,
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

impl PyjamaParameters {
    /// Generates a new balanced parameter set, equally resistant against all attacks.
    pub fn new(num_proposers: u64, num_relays: u64) -> Self {
        Self {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 25).div_ceil(100),
            should_decode_threshold: (num_relays * 50).div_ceil(100),
            attestations_threshold: (num_relays * 75).div_ceil(100),
        }
    }

    /// Generates a new parameter set based on the first ones proposed in the PJM paper.
    pub fn new_paper1(num_proposers: u64, num_relays: u64) -> Self {
        Self {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 40).div_ceil(100),
            should_decode_threshold: (num_relays * 60).div_ceil(100),
            attestations_threshold: (num_relays * 80).div_ceil(100),
        }
    }

    /// Generates a new parameter set based on the second ones proposed in the PJM paper.
    pub fn new_paper2(num_proposers: u64, num_relays: u64) -> Self {
        Self {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 30).div_ceil(100),
            should_decode_threshold: (num_relays * 60).div_ceil(100),
            attestations_threshold: (num_relays * 80).div_ceil(100),
        }
    }

    /// Generates a new parameter set prioritizing hiding over liveness.
    pub fn new_hiding(num_proposers: u64, num_relays: u64) -> Self {
        Self {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 40).div_ceil(100),
            should_decode_threshold: (num_relays * 60).div_ceil(100),
            attestations_threshold: (num_relays * 80).div_ceil(100),
        }
    }

    /// Generates a new parameter set prioritizing liveness over hiding.
    pub fn new_liveness(num_proposers: u64, num_relays: u64) -> Self {
        Self {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 20).div_ceil(100),
            should_decode_threshold: (num_relays * 47).div_ceil(100),
            attestations_threshold: (num_relays * 73).div_ceil(100),
        }
    }

    /// Generates a new parameter set prioritizing permanent liveness failures over all others.
    pub fn new_permanent_liveness(num_proposers: u64, num_relays: u64) -> Self {
        Self {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 23).div_ceil(100),
            should_decode_threshold: (num_relays * 53).div_ceil(100),
            attestations_threshold: (num_relays * 76).div_ceil(100),
        }
    }

    /// Proobability that the adversary can break the hiding property in a slot.
    pub fn break_hiding_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that the adversary controls enough relays to decrypt
        let byzantine = adv_strength.byzantine;
        let relays_dist = Binomial::new(byzantine, self.num_relays).unwrap();
        let relays_needed = self.can_decode_threshold;
        1.0 - relays_dist.cdf(relays_needed - 1)
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
        let relays_dist = Binomial::new(byzantine, self.num_relays).unwrap();
        let relays_needed = self.attestations_threshold - self.should_decode_threshold;
        let prob_censor_relays = 1.0 - relays_dist.cdf(relays_needed - 1);

        // probability that either attack works
        1.0 - (1.0 - prob_all_proposers) * (1.0 - prob_censor_relays)
    }

    /// Probability that the adversary can cause a temporary liveness failure in a slot.
    pub fn temporary_liveness_failure_probability(&self, adv_strength: AdversaryStrength) -> f64 {
        // probability that only the adversary proposes
        let failed = adv_strength.crashed + adv_strength.byzantine;
        let proposers_dist = Binomial::new(failed, self.num_proposers).unwrap();
        let prob_no_proposals = 1.0 - proposers_dist.cdf(self.num_proposers - 1);

        // probability that the adversary can prevent the leader from producing a non-empty block
        let relays_dist = Binomial::new(failed, self.num_relays).unwrap();
        let relays_to_hold_protocol = self.should_decode_threshold - self.can_decode_threshold;
        let relays_to_censor_proposers = self.attestations_threshold - self.should_decode_threshold;
        let relays_to_censor_leader = self.num_relays - self.attestations_threshold;
        let relays_needed = relays_to_hold_protocol
            .min(relays_to_censor_proposers)
            .min(relays_to_censor_leader);
        let prob_censor_relays = 1.0 - relays_dist.cdf(relays_needed - 1);

        // probability that either attack works
        1.0 - (1.0 - prob_no_proposals) * (1.0 - prob_censor_relays)
    }

    /// Probability that the adversary can cause a permanent liveness failure.
    ///
    /// The adversary can achieve this by withholding enough shreds that should be revealed.
    /// This analyzes the worst case where a batch got `self.should_decode_threshold` attestations.
    pub fn permanent_liveness_failure_probability(&self, adv_stength: AdversaryStrength) -> f64 {
        // probability that the adversary can withhold enough shreds
        let byzantine = adv_stength.byzantine;
        let relays_dist = Binomial::new(byzantine, self.num_relays).unwrap();
        let relays_needed = self.should_decode_threshold - self.can_decode_threshold;
        1.0 - relays_dist.cdf(relays_needed - 1)
    }

    pub fn print_failure_probabilities(&self, adv_strength: AdversaryStrength) {
        info!(
            "MCP parameters: proposers={}, relays={}, {:.2}/{:.2}/{:.2}",
            self.num_proposers,
            self.num_relays,
            self.can_decode_threshold as f64 / self.num_relays as f64 * 100.0,
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
        info!(
            "permanent liveness failure: {:.2}",
            self.permanent_liveness_failure_probability(adv_strength)
                .log10()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mcp_parameters() {
        let params = PyjamaParameters::new(2, 5);
        assert_eq!(params.num_proposers, 2);
        assert_eq!(params.num_relays, 5);
        assert_eq!(params.can_decode_threshold, 2);
        assert_eq!(params.should_decode_threshold, 3);
        assert_eq!(params.attestations_threshold, 4);
    }
}
