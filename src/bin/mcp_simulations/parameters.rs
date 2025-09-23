// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parameters for the MCP protocol.
//!
//!

use statrs::distribution::{Binomial, DiscreteCDF};

pub struct McpParameters {
    num_proposers: u64,
    num_relays: u64,
    can_decode_threshold: u64,
    should_decode_threshold: u64,
    attestations_threshold: u64,
}

struct AdversaryStrength {
    crashed: f64,
    byzantine: f64,
}

struct SpecificAdversaryStrength {
    is_leader: bool,
    crashed_proposers: u64,
    byzantine_proposers: u64,
    crashed_relays: u64,
    byzantine_relays: u64,
}

impl McpParameters {
    /// Generates a new balanced parameter set, equally resistant against all attacks.
    pub fn new(num_proposers: u64, num_relays: u64) -> Self {
        McpParameters {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 25).div_ceil(100),
            should_decode_threshold: (num_relays * 50).div_ceil(100),
            attestations_threshold: (num_relays * 75).div_ceil(100),
        }
    }

    /// Generates a new parameter set based on the first ones proposed in the PJM paper.
    pub fn new_paper1(num_proposers: u64, num_relays: u64) -> Self {
        McpParameters {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 40).div_ceil(100),
            should_decode_threshold: (num_relays * 60).div_ceil(100),
            attestations_threshold: (num_relays * 80).div_ceil(100),
        }
    }

    /// Generates a new parameter set based on the second ones proposed in the PJM paper.
    pub fn new_paper2(num_proposers: u64, num_relays: u64) -> Self {
        McpParameters {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 30).div_ceil(100),
            should_decode_threshold: (num_relays * 60).div_ceil(100),
            attestations_threshold: (num_relays * 80).div_ceil(100),
        }
    }

    /// Generates a new parameter set prioritizing hiding over liveness.
    pub fn new_hiding(num_proposers: u64, num_relays: u64) -> Self {
        McpParameters {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 40).div_ceil(100),
            should_decode_threshold: (num_relays * 60).div_ceil(100),
            attestations_threshold: (num_relays * 80).div_ceil(100),
        }
    }

    /// Generates a new parameter set prioritizing liveness over hiding.
    pub fn new_liveness(num_proposers: u64, num_relays: u64) -> Self {
        McpParameters {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 20).div_ceil(100),
            should_decode_threshold: (num_relays * 50).div_ceil(100),
            attestations_threshold: (num_relays * 80).div_ceil(100),
        }
    }

    /// Generates a new parameter set prioritizing permanent liveness failures over all others.
    pub fn new_permanent_liveness(num_proposers: u64, num_relays: u64) -> Self {
        McpParameters {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 23).div_ceil(100),
            should_decode_threshold: (num_relays * 53).div_ceil(100),
            attestations_threshold: (num_relays * 76).div_ceil(100),
        }
    }

    // just as hard with `num_relays - attestations_threshold` crashed nodes
    pub fn selective_censorship_probability(&self, adv_strength: f64) -> f64 {
        let proposers_dist = Binomial::new(adv_strength, self.num_proposers).unwrap();
        let prob_all_proposers = 1.0 - proposers_dist.cdf(self.num_proposers - 1);

        let relays_dist = Binomial::new(adv_strength, self.num_relays).unwrap();
        let relays_needed = self.attestations_threshold - self.should_decode_threshold;
        let prob_censor_relays = 1.0 - relays_dist.cdf(relays_needed - 1);

        // prob: prob_all_proposers OR prob_censor_relays
        1.0 - (1.0 - prob_all_proposers) * (1.0 - prob_censor_relays)
    }

    pub fn break_hiding_probability(&self, adv_strength: f64) -> f64 {
        let relays_dist = Binomial::new(adv_strength, self.num_relays).unwrap();
        let relays_needed = self.can_decode_threshold;
        1.0 - relays_dist.cdf(relays_needed - 1)
    }

    pub fn temporary_liveness_failure_probability(&self, adv_strength: f64) -> f64 {
        let proposers_dist = Binomial::new(adv_strength, self.num_proposers).unwrap();
        let prob_no_proposals = 1.0 - proposers_dist.cdf(self.num_proposers - 1);

        let relays_dist = Binomial::new(adv_strength, self.num_relays).unwrap();
        let relays_to_hold_protocol = self.should_decode_threshold - self.can_decode_threshold;
        let relays_to_censor_leader = self.attestations_threshold - self.should_decode_threshold;
        let relays_needed = relays_to_hold_protocol.min(relays_to_censor_leader);
        let prob_censor_relays = 1.0 - relays_dist.cdf(relays_needed - 1);

        // prob: prob_no_proposals OR prob_censor_relays
        1.0 - (1.0 - prob_no_proposals) * (1.0 - prob_censor_relays)
    }

    pub fn permanent_liveness_failure_probability(&self, adv_stength: f64) -> f64 {
        let relays_dist = Binomial::new(adv_stength, self.num_relays).unwrap();
        let relays_needed = self.should_decode_threshold - self.can_decode_threshold;
        1.0 - relays_dist.cdf(relays_needed - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mcp_parameters() {
        let params = McpParameters::new(2, 5);
        assert_eq!(params.num_proposers, 2);
        assert_eq!(params.num_relays, 5);
        assert_eq!(params.can_decode_threshold, 2);
        assert_eq!(params.should_decode_threshold, 3);
        assert_eq!(params.attestations_threshold, 4);
    }
}
