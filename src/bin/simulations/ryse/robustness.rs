// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Calculations about the robustness of the Ryse MCP protocol.
//!
//! Currently, this just runs some static calculations on the set of parameters.
//!
//! In the future, this would also simulate attack scenarios for a specific stake distribution.
//! This is analogous to what is done for Rotor in [`crate::rotor::robustness`];

use std::fs::File;

use alpenglow::disseminator::rotor::FaitAccompli1Sampler;
use alpenglow::network::simulated::stake_distribution::{
    VALIDATOR_DATA, validators_from_validator_data,
};
use color_eyre::Result;

use super::parameters::{AdversaryStrength, RyseParameters};
use crate::quorum_robustness::{QuorumAttack, QuorumRobustnessTest, QuorumThreshold};

const NUM_PROPOSERS: u64 = 16;
const NUM_RELAYS: u64 = 512;
const ADVERSARY_STRENGTH: AdversaryStrength = AdversaryStrength {
    crashed: 0.0,
    byzantine: 0.2,
};

pub fn run_robustness_tests() -> Result<()> {
    let params = RyseParameters::new(NUM_PROPOSERS, NUM_RELAYS);
    params.print_failure_probabilities(ADVERSARY_STRENGTH);
    let optimal_params = params.optmize(ADVERSARY_STRENGTH);
    optimal_params.print_failure_probabilities(ADVERSARY_STRENGTH);

    // TODO: extend with robustness tests for actual stake distribution
    //       and different sampling strategies (analogous to `rotor/robustness`)

    Ok(())
}

pub fn run_ryse_robustness_test(total_shreds: u64) {
    let (validators, _with_pings) = validators_from_validator_data(&VALIDATOR_DATA);
    let proposer_sampler =
        FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators.clone(), NUM_PROPOSERS);
    let relay_sampler =
        FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators.clone(), total_shreds);
    let params = RyseParameters::new(NUM_PROPOSERS, total_shreds);

    let hiding_threshold = QuorumThreshold::Simple {
        quorum: 1,
        threshold: (params.relay_notar_threshold + params.decode_threshold)
            .saturating_sub(params.num_relays) as usize,
        is_crash_enough: false,
    };
    let hiding_attack = QuorumAttack {
        name: "hiding".to_string(),
        quorum: hiding_threshold,
    };

    let censorship_proposer_threshold = QuorumThreshold::Simple {
        quorum: 0,
        threshold: params.num_leaders as usize,
        is_crash_enough: true,
    };
    let censorship_relay_threshold = QuorumThreshold::Simple {
        quorum: 1,
        threshold: (params.num_relays - params.relay_notar_threshold) as usize,
        is_crash_enough: true,
    };
    let censorship_attack = QuorumAttack {
        name: "censorship".to_string(),
        quorum: QuorumThreshold::Any(vec![
            censorship_proposer_threshold,
            censorship_relay_threshold,
        ]),
    };

    let test = QuorumRobustnessTest::new(
        validators,
        "solana".to_string(),
        relay_sampler,
        vec![NUM_PROPOSERS as usize, NUM_RELAYS as usize],
        vec![hiding_attack, censorship_attack],
    );
    let adversary_strength = crate::quorum_robustness::AdversaryStrength {
        crashed: 0.0,
        byzantine: 0.1,
    };

    let filename = format!("ryse_robustness_{}_{}", params.num_leaders, total_shreds);
    let path = std::path::Path::new("data")
        .join("output")
        .join(filename)
        .with_extension("csv");
    let file = File::create(path).unwrap();
    let mut csv_file = csv::Writer::from_writer(file);

    test.run(adversary_strength, &mut csv_file);
}
