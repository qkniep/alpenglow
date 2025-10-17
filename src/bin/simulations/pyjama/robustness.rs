// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Calculations about the robustness of the Pyjama MCP protocol.
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

use super::parameters::{AdversaryStrength, PyjamaParameters};
use crate::quorum_robustness::{QuorumRobustnessTest, QuorumThreshold};

const NUM_PROPOSERS: u64 = 16;
const NUM_RELAYS: u64 = 512;
const ADVERSARY_STRENGTH: AdversaryStrength = AdversaryStrength {
    crashed: 0.0,
    byzantine: 0.18,
};

pub fn run_robustness_tests() {
    PyjamaParameters::new(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_paper1(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_paper2(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_hiding(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_liveness(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_permanent_liveness(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
}

pub fn run_pyjama_robustness_test(total_shreds: u64) -> Result<()> {
    let (validators, _with_pings) = validators_from_validator_data(&VALIDATOR_DATA);
    let leader_sampler =
        FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators.clone(), 1);
    let proposer_sampler =
        FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators.clone(), NUM_PROPOSERS);
    let relay_sampler =
        FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators.clone(), total_shreds);
    let params = PyjamaParameters::new(NUM_PROPOSERS, total_shreds);

    let hiding_threshold = QuorumThreshold::Simple {
        quorum: 2,
        threshold: params.can_decode_threshold as usize,
        is_crash_enough: false,
    };
    let hiding_attack = hiding_threshold.into_attack("hiding");

    let all_proposers_threshold = QuorumThreshold::Simple {
        quorum: 1,
        threshold: params.num_proposers as usize,
        is_crash_enough: true,
    };
    let relays_to_censor_proposers_threshold = QuorumThreshold::Simple {
        quorum: 2,
        threshold: (params.attestations_threshold - params.should_decode_threshold) as usize,
        is_crash_enough: true,
    };
    let censorship_attack = all_proposers_threshold
        .clone()
        .or(relays_to_censor_proposers_threshold.clone())
        .into_attack("censorship");

    let relays_to_hold_protocol_threshold = QuorumThreshold::Simple {
        quorum: 2,
        threshold: (params.should_decode_threshold - params.can_decode_threshold) as usize,
        is_crash_enough: true,
    };
    let relays_to_censor_leader_threshold = QuorumThreshold::Simple {
        quorum: 2,
        threshold: (params.num_relays - params.attestations_threshold) as usize,
        is_crash_enough: true,
    };
    let temporary_liveness_attack = QuorumThreshold::Any(vec![
        all_proposers_threshold,
        relays_to_hold_protocol_threshold,
        relays_to_censor_proposers_threshold,
        relays_to_censor_leader_threshold,
    ])
    .into_attack("temporary_liveness");

    let permanent_liveness_threshold = QuorumThreshold::Simple {
        quorum: 2,
        threshold: (params.should_decode_threshold - params.can_decode_threshold) as usize,
        is_crash_enough: false,
    };
    let permanent_liveness_attack =
        QuorumThreshold::Any(vec![permanent_liveness_threshold]).into_attack("permanent_liveness");

    let test = QuorumRobustnessTest::new(
        validators,
        "solana".to_string(),
        vec![leader_sampler, proposer_sampler, relay_sampler],
        vec![0, 1, 2],
        vec![1, params.num_proposers as usize, params.num_relays as usize],
        vec![
            hiding_attack,
            censorship_attack,
            temporary_liveness_attack,
            permanent_liveness_attack,
        ],
    );
    let adversary_strength = crate::quorum_robustness::AdversaryStrength {
        crashed: 0.05,
        byzantine: 0.2,
    };

    let filename = format!(
        "pyjama_robustness_{}_{}",
        params.num_proposers, total_shreds
    );
    let path = std::path::Path::new("data")
        .join("output")
        .join(filename)
        .with_extension("csv");
    let file = File::create(path).unwrap();
    let mut csv_file = csv::Writer::from_writer(file);

    test.run(adversary_strength, &mut csv_file)
}
