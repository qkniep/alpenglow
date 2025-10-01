// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//!
//!
//!

use alpenglow::ValidatorInfo;
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::network::simulated::ping_data::PingServer;
use alpenglow::network::simulated::stake_distribution::validators_from_validator_data;
use color_eyre::Result;

use super::latency::LatencyTestStage;
use super::parameters::{AdversaryStrength, RyseParameters};

const NUM_PROPOSERS: u64 = 16;
const NUM_RELAYS: u64 = 512;
const ADVERSARY_STRENGTH: AdversaryStrength = AdversaryStrength {
    crashed: 0.2,
    byzantine: 0.18,
};

pub fn run_robustness_tests() -> Result<()> {
    let params = RyseParameters::new(NUM_PROPOSERS, NUM_RELAYS);
    params.print_failure_probabilities(ADVERSARY_STRENGTH);
    let optimal_params = params.optmize(ADVERSARY_STRENGTH);
    optimal_params.print_failure_probabilities(ADVERSARY_STRENGTH);

    // run_tests_for_stake_distribution("solana", &VALIDATOR_DATA);

    Ok(())
}

// fn run_tests_for_stake_distribution(distribution_name: &str, validator_data: &[ValidatorData]) {
//     // load validator and ping data
//     let (validators, validators_and_ping_servers) = validators_from_validator_data(validator_data);
//     let validators_with_pings: Vec<ValidatorInfo> = validators_and_ping_servers
//         .iter()
//         .map(|(v, _)| v.clone())
//         .collect();
//
//     // run all tests for the different sampling strategies
//     let sampling_strat = "stake_weighted";
//     let test_name = format!("{distribution_name}-{sampling_strat}");
//     let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
//     let ping_proposer_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
//     let ping_rotor_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
//     run_tests(
//         &test_name,
//         &validators_and_ping_servers,
//         &ping_leader_sampler,
//         &ping_proposer_sampler,
//         &ping_rotor_sampler,
//     )
// }
//
// fn run_tests<
//     L: SamplingStrategy + Sync + Send + Clone,
//     P: SamplingStrategy + Sync + Send + Clone,
//     R: SamplingStrategy + Sync + Send + Clone,
// >(
//     test_name: &str,
//     validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
//     ping_leader_sampler: &L,
//     ping_proposer_sampler: &P,
//     ping_rotor_sampler: &R,
// ) {
//     // latency experiments with random leaders
//     for (n, k) in [(32, 64)] {
//         info!("{test_name} latency tests (random leaders, n={n}, k={k})");
//         let tester = LatencyTest::new(
//             validators_with_ping_data,
//             ping_leader_sampler.clone(),
//             ping_proposer_sampler.clone(),
//             ping_rotor_sampler.clone(),
//             n,
//             k,
//         );
//         let test_name = format!("{test_name}-{n}-{k}");
//         tester.run_many(&test_name, 1000, LatencyTestStage::Reconstruct);
//     }
// }
