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

use alpenglow::disseminator::rotor::StakeWeightedSampler;
use alpenglow::network::simulated::stake_distribution::{
    VALIDATOR_DATA, validators_from_validator_data,
};
use color_eyre::Result;

use super::RotorParams;
use crate::quorum_robustness::{AdversaryStrength, QuorumRobustnessTest, QuorumThreshold};

// TODO: support different: stake distributions, sampling strategies, Rotor params

pub fn run_rotor_robustness_test(data_shreds: usize, total_shreds: usize) -> Result<()> {
    let (validators, _with_pings) = validators_from_validator_data(&VALIDATOR_DATA);
    let leader_sampler = StakeWeightedSampler::new(validators.clone());
    let rotor_sampler = StakeWeightedSampler::new(validators.clone());

    let params = RotorParams {
        data_shreds,
        shreds: total_shreds,
        slices: 40,
    };

    let equivocation_thresholds = (0..params.slices)
        .map(|slice| QuorumThreshold::Simple {
            quorum: slice,
            threshold: params.data_shreds,
            is_crash_enough: false,
        })
        .collect::<Vec<_>>();
    let equivocation_attack =
        QuorumThreshold::Any(equivocation_thresholds).into_attack("equivocation");

    let censorship_thresholds = (0..params.slices)
        .map(|slice| QuorumThreshold::Simple {
            quorum: slice,
            threshold: params.shreds - params.data_shreds,
            is_crash_enough: true,
        })
        .collect::<Vec<_>>();
    let censorship_attack = QuorumThreshold::Any(censorship_thresholds).into_attack("censorship");

    let test = QuorumRobustnessTest::new(
        validators,
        "solana".to_string(),
        vec![leader_sampler, rotor_sampler],
        vec![1; params.slices],
        vec![params.shreds; params.slices],
        vec![equivocation_attack, censorship_attack],
    );
    let adversary_strength = AdversaryStrength {
        crashed: 0.2,
        byzantine: 0.2,
    };

    let filename = format!("rotor_robustness_{data_shreds}_{total_shreds}");
    let path = std::path::Path::new("data")
        .join("output")
        .join(filename)
        .with_extension("csv");
    let file = File::create(path).unwrap();
    let mut csv_file = csv::Writer::from_writer(file);

    test.run(adversary_strength, &mut csv_file)
}
