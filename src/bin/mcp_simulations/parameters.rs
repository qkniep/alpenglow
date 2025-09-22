// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parameters for the MCP protocol.
//!
//!

struct McpParameters {
    num_proposers: usize,
    num_relays: usize,
    can_decode_threshold: usize,
    should_decode_threshold: usize,
    attestations_threshold: usize,
}

struct AdversaryStrength {
    crashed: f64,
    byzantine: f64,
}

struct SpecificAdversaryStrength {
    is_leader: bool,
    crashed_proposers: usize,
    byzantine_proposers: usize,
    crashed_relays: usize,
    byzantine_relays: usize,
}

impl McpParameters {
    fn new(num_proposers: usize, num_relays: usize) -> Self {
        McpParameters {
            num_proposers,
            num_relays,
            can_decode_threshold: (num_relays * 2).div_ceil(5),
            should_decode_threshold: (num_relays * 3).div_ceil(5),
            attestations_threshold: (num_relays * 4).div_ceil(5),
        }
    }

    // just as hard with `num_relays - attestations_threshold` crashed nodes
    fn selective_censorship_probability(&self, adv_strength: f64) -> f64 {
        // let prob_all_proposers = binomial_cdf(self.num_proposers, self.num_proposers, adv_strength);

        let relays_needed = self.attestations_threshold - self.should_decode_threshold;
        // let prob_censor_relays = binomial_cdf(relays_needed, self.num_relays, adv_strength);

        // prob: prob_all_proposers OR prob_censor_relays
    }

    fn break_hiding_probability(&self, adv_strength: f64) -> f64 {
        let relays_needed = self.can_decode_threshold;
        // binomial_cdf(relays_needed, self.num_relays, adv_strength)
    }

    fn temporary_liveness_failure_probability(&self, adv_strength: f64) -> f64 {
        // let prob_no_proposals = binomial_cdf(self.num_proposers, self.num_proposers, adv_strength);

        let relays_to_hold_protocol = self.should_decode_threshold - self.can_decode_threshold;
        let relays_to_censor_leader = self.attestations_threshold - self.should_decode_threshold;
        let relays_needed = relays_to_hold_protocol.min(relays_to_censor_leader);
        // binomial_cdf(relays_needed, self.num_relays, adv_strength)
    }

    fn permanent_liveness_failure_probability(&self, adv_stength: f64) -> f64 {
        let relays_needed = self.should_decode_threshold - self.can_decode_threshold;
        // binomial_cdf(relays_needed, self.num_relays, adv_strength)
    }
}
