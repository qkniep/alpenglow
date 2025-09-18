// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for MCP.
//!
//! This module provides a binary for simulating MCP with Rotor and Alpenglow.

mod latency;
mod parameters;

use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::network::simulated::ping_data::PingServer;
use alpenglow::network::simulated::stake_distribution::{
    VALIDATOR_DATA, ValidatorData, validators_from_validator_data,
};
use alpenglow::{ValidatorInfo, logging};
use color_eyre::Result;
use log::info;

use self::latency::{LatencyTest, LatencyTestStage};

const NUM_PROPOSERS: u64 = 8;
const NUM_RELAYS: u64 = 512;

fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages + `logforth` logging
    color_eyre::install()?;
    logging::enable_logforth();

    run_tests_for_stake_distribution("solana", &VALIDATOR_DATA);

    Ok(())
}

fn run_tests_for_stake_distribution(distribution_name: &str, validator_data: &[ValidatorData]) {
    // load validator and ping data
    let (validators, validators_and_ping_servers) = validators_from_validator_data(validator_data);
    let validators_with_pings: Vec<ValidatorInfo> = validators_and_ping_servers
        .iter()
        .map(|(v, _)| v.clone())
        .collect();

    // TODO: indicatif progress bar

    // run all tests for the different sampling strategies
    let sampling_strat = "stake_weighted";
    let test_name = format!("{distribution_name}-{sampling_strat}");
    let leader_sampler = StakeWeightedSampler::new(validators.clone());
    let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
    let proposer_sampler = StakeWeightedSampler::new(validators.clone());
    let ping_proposer_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
    let rotor_sampler = StakeWeightedSampler::new(validators.clone());
    let ping_rotor_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
    run_tests(
        &test_name,
        &validators,
        &validators_and_ping_servers,
        &leader_sampler,
        &proposer_sampler,
        &rotor_sampler,
        &ping_leader_sampler,
        &ping_proposer_sampler,
        &ping_rotor_sampler,
    )
}

fn run_tests<
    L: SamplingStrategy + Sync + Send + Clone,
    P: SamplingStrategy + Sync + Send + Clone,
    R: SamplingStrategy + Sync + Send + Clone,
>(
    test_name: &str,
    validators: &[ValidatorInfo],
    validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
    leader_sampler: &L,
    proposer_sampler: &P,
    rotor_sampler: &R,
    ping_leader_sampler: &L,
    ping_proposer_sampler: &P,
    ping_rotor_sampler: &R,
) {
    // latency experiments with random leaders
    for (n, k) in [(32, 64)] {
        info!("{test_name} latency tests (random leaders, n={n}, k={k})");
        let tester = LatencyTest::new(
            validators_with_ping_data,
            ping_leader_sampler.clone(),
            ping_proposer_sampler.clone(),
            ping_rotor_sampler.clone(),
            n,
            k,
        );
        let test_name = format!("{test_name}-{n}-{k}");
        tester.run_many(&test_name, 1000, LatencyTestStage::Reconstruct);
    }

    // // latency experiments with fixed leaders
    // let cities = if test_name.starts_with("solana") {
    //     vec![
    //         "Westpoort",
    //         "Frankfurt",
    //         "London",
    //         "Zurich",
    //         "New York City",
    //         "Los Angeles",
    //         "Tokyo",
    //         "Singapore",
    //         "Cape Town",
    //         "Buenos Aires",
    //     ]
    // } else {
    //     unimplemented!()
    // };
    //
    // for (n, k) in &SHRED_COMBINATIONS {
    //     cities.par_iter().for_each(|city| {
    //         info!("{test_name} latency tests (fixed leader in {city}, n={n}, k={k})");
    //         let leader = find_leader_in_city(validators_with_ping_data, city);
    //         let tester = LatencyTest::new(
    //             validators_with_ping_data,
    //             ping_leader_sampler.clone(),
    //             ping_rotor_sampler.clone(),
    //             *n,
    //             *k,
    //         );
    //         let test_name = format!("{test_name}-{n}-{k}");
    //         tester.run_many_with_leader(&test_name, 1000, LatencyTestStage::Reconstruct, leader);
    //     });
    // }
}

fn find_leader_in_city(
    validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
    city: &str,
) -> ValidatorInfo {
    for (v, p) in validators_with_ping_data {
        if p.location == city {
            return v.clone();
        }
    }
    panic!("leader not found in {city}");
}
