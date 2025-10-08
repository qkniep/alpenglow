// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Calculations about the robustness of the Rotor block dissemination protocol.
//!
//! This implements two main attack scenarios:
//! - Equivocation attack: Less than 20% of stake is Byzantine.
//! - Censorship attack: Up to 40% of stake is crashed.
//!
//! For each attack scenario multiple adversary strategies are simulated:
//! - Random: Corrupt a random subset of validators.
//! - Small: Corrupt as many of the smallest validators as possible.
//! - Large: Corrupt as many of the largest validators as possible.

use std::fs::File;

use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::network::simulated::stake_distribution::{
    VALIDATOR_DATA, validators_from_validator_data,
};
use alpenglow::shredder::{DATA_SHREDS, TOTAL_SHREDS};

use super::{RotorInstanceBuilder, RotorParams};
use crate::quorum_robustness::{
    AdversaryStrength, QuorumAttack, QuorumRobustnessTest, QuorumThreshold,
};

// TODO: support different: stake distributions, sampling strategies, Rotor params

pub fn run_rotor_robustness_test() {
    let (validators, _with_pings) = validators_from_validator_data(&VALIDATOR_DATA);
    let leader_sampler = StakeWeightedSampler::new(validators.clone());
    let rotor_sampler = StakeWeightedSampler::new(validators.clone());

    let params = RotorParams {
        num_data_shreds: DATA_SHREDS,
        num_shreds: TOTAL_SHREDS,
        num_slices: 1,
    };
    let builder = RotorInstanceBuilder::new(leader_sampler, rotor_sampler.clone(), params);

    let equivocation_thresholds = (0..params.num_slices)
        .map(|slice| QuorumThreshold::Simple {
            quorum: slice,
            threshold: params.num_data_shreds,
            is_crash_enough: false,
        })
        .collect::<Vec<_>>();
    let equivocation_attack = QuorumAttack {
        name: "equivocation".to_string(),
        quorum: QuorumThreshold::Any(equivocation_thresholds),
    };

    let censorship_thresholds = (0..params.num_slices)
        .map(|slice| QuorumThreshold::Simple {
            quorum: slice,
            threshold: params.num_shreds - params.num_data_shreds,
            is_crash_enough: true,
        })
        .collect::<Vec<_>>();
    let censorship_attack = QuorumAttack {
        name: "censorship".to_string(),
        quorum: QuorumThreshold::Any(censorship_thresholds),
    };

    let test = QuorumRobustnessTest::new(
        validators,
        "solana".to_string(),
        rotor_sampler,
        vec![params.num_shreds; params.num_slices],
        vec![equivocation_attack, censorship_attack],
    );
    let adversary_strength = AdversaryStrength {
        crashed: 0.2,
        byzantine: 0.2,
    };

    let file = File::create("data/output/rotor_robustness.csv").unwrap();
    let mut csv_file = csv::Writer::from_writer(file);

    test.run(adversary_strength, &mut csv_file);
}
