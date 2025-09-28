// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for Rotor and Alpenglow.
//!
//! This module provides a binary for simulating Rotor and Alpenglow.
//!
//! Currently three major simulations are implemented:
//! 1. Bandwidth (Rotor, workload per node, maximum supported throughput)
//! 2. Latency (all stages of Alpenglow)
//! 3. Rotor robustness (Rotor, 40% crash, 20% byzantine)
//!
//! For parallelization of these simulations, [`rayon`] is used in most places.
//!
//! All of these simulations are evaluated on different stake distributions, namely:
//! - Solana mainnet (real-world data)
//! - Sui mainnet (real-world data)
//! - 5 hubs (five major cities, globally distributed, equal stake each)
//! - Stock exchanges (top 10 global stock exchange locations)
//!
//! Also, all simulations are evaluated for different sampling strategies, namely:
//! - Uniform
//! - Stake-weighted
//! - Fait Accompli 1 + Stake-weighted
//! - Fait Accompli 1 + Bin-packing
//! - Decaying acceptance (with 3.0 max samples)
//! - Turbine
//!
//! The global constants [`RUN_BANDWIDTH_TESTS`], [`RUN_LATENCY_TESTS`],
//! [`RUN_CRASH_ROTOR_TESTS`], and [`RUN_BYZANTINE_ROTOR_TESTS`]
//! control which tests to run.
//! Further, the global constants [`SAMPLING_STRATEGIES`], [`MAX_BANDWIDTHS`],
//! and [`SHRED_COMBINATIONS`] control the parameters for some tests.

mod alpenglow;
mod discrete_event_simulator;
mod rotor;

use std::fs::File;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use ::alpenglow::disseminator::rotor::sampling_strategy::{
    DecayingAcceptanceSampler, FaitAccompli1Sampler, FaitAccompli2Sampler, TurbineSampler,
    UniformSampler,
};
use ::alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use ::alpenglow::network::simulated::ping_data::PingServer;
use ::alpenglow::network::simulated::stake_distribution::{
    VALIDATOR_DATA, ValidatorData, validators_from_validator_data,
};
use ::alpenglow::{Stake, ValidatorInfo, logging};
use color_eyre::Result;
use log::info;
use rayon::prelude::*;

use self::alpenglow::{BandwidthTest, LatencyTest, LatencyTestStage};
use self::rotor::RotorRobustnessTest;
use crate::discrete_event_simulator::{SimulationEngine, SimulationEnvironment};
use crate::rotor::{RotorInstanceBuilder, RotorLatencySimulation, RotorParams};

const RUN_BANDWIDTH_TESTS: bool = false;
const RUN_LATENCY_TESTS: bool = true;
const RUN_CRASH_ROTOR_TESTS: bool = false;
const RUN_BYZANTINE_ROTOR_TESTS: bool = false;

const SAMPLING_STRATEGIES: [&str; 1] = [
    // "uniform",
    "stake_weighted",
    // "fa1_iid",
    // "fa2",
    // "fa1_partition",
    // "decaying_acceptance",
    // "turbine",
];

const MAX_BANDWIDTHS: [u64; 4] = [
    100_000_000,     // 100 Mbps
    1_000_000_000,   // 1 Gbps
    10_000_000_000,  // 10 Gbps
    100_000_000_000, // 100 Gbps
];

const TOTAL_SHREDS_FA1: u64 = 64;
const SHRED_COMBINATIONS: [(usize, usize); 1] = [
    // (32, 54),
    (32, 64),
    // (32, 80),
    // (32, 96),
    // (32, 320),
    // (64, 128),
    // (128, 256),
    // (256, 512),
];

fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    logging::enable_logforth();

    if RUN_BANDWIDTH_TESTS {
        // create bandwidth evaluation files
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth")
            .join("bandwidth_supported")
            .with_extension("csv");
        if let Some(parent) = filename.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        let _ = File::create(filename).unwrap();
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth")
            .join("bandwidth_usage")
            .with_extension("csv");
        if let Some(parent) = filename.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        let _ = File::create(filename).unwrap();
    }

    if RUN_CRASH_ROTOR_TESTS || RUN_BYZANTINE_ROTOR_TESTS {
        // create saftey evaluation file
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("rotor_robustness")
            .join("rotor_robustness")
            .with_extension("csv");
        if let Some(parent) = filename.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        let _ = File::create(filename).unwrap();
    }

    // run tests for different stake distributions
    run_tests_for_stake_distribution("solana", &VALIDATOR_DATA);
    // run_tests_for_stake_distribution("sui", &SUI_VALIDATOR_DATA);
    // run_tests_for_stake_distribution("5hubs", &FIVE_HUBS_VALIDATOR_DATA);
    // run_tests_for_stake_distribution("stock_exchanges", &STOCK_EXCHANGES_VALIDATOR_DATA);

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
    for sampling_strat in SAMPLING_STRATEGIES {
        let test_name = format!("{distribution_name}-{sampling_strat}");
        if sampling_strat == "uniform" {
            let leader_sampler = UniformSampler::new(validators.clone());
            let ping_leader_sampler = UniformSampler::new(validators_with_pings.clone());
            let rotor_sampler = UniformSampler::new(validators.clone());
            let ping_rotor_sampler = UniformSampler::new(validators_with_pings.clone());
            run_tests(
                &test_name,
                &validators,
                &validators_and_ping_servers,
                &leader_sampler,
                &rotor_sampler,
                &ping_leader_sampler,
                &ping_rotor_sampler,
            );
        } else if sampling_strat == "stake_weighted" {
            let leader_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            let rotor_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_rotor_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            run_tests(
                &test_name,
                &validators,
                &validators_and_ping_servers,
                &leader_sampler,
                &rotor_sampler,
                &ping_leader_sampler,
                &ping_rotor_sampler,
            )
        } else if sampling_strat == "fa1_iid" {
            let leader_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            let rotor_sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(
                validators.clone(),
                TOTAL_SHREDS_FA1,
            );
            let ping_rotor_sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(
                validators_with_pings.clone(),
                TOTAL_SHREDS_FA1,
            );
            run_tests(
                &test_name,
                &validators,
                &validators_and_ping_servers,
                &leader_sampler,
                &rotor_sampler,
                &ping_leader_sampler,
                &ping_rotor_sampler,
            )
        } else if sampling_strat == "fa2" {
            let leader_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            let rotor_sampler = FaitAccompli2Sampler::new(validators.clone(), TOTAL_SHREDS_FA1);
            let ping_rotor_sampler =
                FaitAccompli2Sampler::new(validators_with_pings.clone(), TOTAL_SHREDS_FA1);
            run_tests(
                &test_name,
                &validators,
                &validators_and_ping_servers,
                &leader_sampler,
                &rotor_sampler,
                &ping_leader_sampler,
                &ping_rotor_sampler,
            )
        } else if sampling_strat == "fa1_partition" {
            let leader_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            let rotor_sampler = FaitAccompli1Sampler::new_with_partition_fallback(
                validators.clone(),
                TOTAL_SHREDS_FA1,
            );
            let ping_rotor_sampler = FaitAccompli1Sampler::new_with_partition_fallback(
                validators_with_pings.clone(),
                TOTAL_SHREDS_FA1,
            );
            run_tests(
                &test_name,
                &validators,
                &validators_and_ping_servers,
                &leader_sampler,
                &rotor_sampler,
                &ping_leader_sampler,
                &ping_rotor_sampler,
            )
        } else if sampling_strat == "decaying_acceptance" {
            let leader_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            let rotor_sampler = DecayingAcceptanceSampler::new(validators.clone(), 3.0);
            let ping_rotor_sampler =
                DecayingAcceptanceSampler::new(validators_with_pings.clone(), 3.0);
            run_tests(
                &test_name,
                &validators,
                &validators_and_ping_servers,
                &leader_sampler,
                &rotor_sampler,
                &ping_leader_sampler,
                &ping_rotor_sampler,
            )
        } else if sampling_strat == "turbine" {
            let leader_sampler = TurbineSampler::new(validators.clone());
            let ping_leader_sampler = TurbineSampler::new(validators_with_pings.clone());
            let rotor_sampler = TurbineSampler::new(validators.clone());
            let ping_rotor_sampler = TurbineSampler::new(validators_with_pings.clone());
            run_tests(
                &test_name,
                &validators,
                &validators_and_ping_servers,
                &leader_sampler,
                &rotor_sampler,
                &ping_leader_sampler,
                &ping_rotor_sampler,
            )
        }
    }
}

fn run_tests<
    L: SamplingStrategy + Sync + Send + Clone,
    R: SamplingStrategy + Sync + Send + Clone,
>(
    test_name: &str,
    validators: &[ValidatorInfo],
    validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
    leader_sampler: &L,
    rotor_sampler: &R,
    ping_leader_sampler: &L,
    ping_rotor_sampler: &R,
) {
    if RUN_BANDWIDTH_TESTS {
        // TODO: clean up code
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth")
            .join("bandwidth_supported")
            .with_extension("csv");
        let file = File::options().append(true).open(filename).unwrap();
        let writer = csv::Writer::from_writer(file);
        let writer = Arc::new(Mutex::new(writer));
        let supported_writer_ref = &writer;
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth")
            .join("bandwidth_usage")
            .with_extension("csv");
        let file = File::options().append(true).open(filename).unwrap();
        let writer = csv::Writer::from_writer(file);
        let writer = Arc::new(Mutex::new(writer));
        let usage_writer_ref = &writer;

        // bandwidth experiment
        MAX_BANDWIDTHS.into_par_iter().for_each(|max_bandwidth| {
            let bandwidths = vec![max_bandwidth; validators.len()];
            let mut tester = BandwidthTest::new(
                validators,
                max_bandwidth,
                bandwidths,
                leader_sampler.clone(),
                rotor_sampler.clone(),
                64,
            );
            for shreds in [64, 128, 256, 512] {
                info!(
                    "{test_name} bandwidth test ({:.1} Gbps, {shreds} shreds)",
                    max_bandwidth as f64 / 1e9,
                );
                tester.set_num_shreds(shreds);
                tester.reset();
                tester.run_multiple(1_000_000);
                tester.evaluate_supported(test_name, supported_writer_ref.clone());
                tester.evaluate_usage(test_name, usage_writer_ref.clone());
            }
        });
    }

    if RUN_LATENCY_TESTS {
        let params = RotorParams::new(32, 64, 10);
        let builder = RotorInstanceBuilder::new(
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            params,
        );
        let leader_bandwidth = 1_000_000_000; // 1 Gbps
        let bandwidths = vec![leader_bandwidth; validators.len()];
        let environment =
            SimulationEnvironment::from_validators_with_ping_data(validators_with_ping_data)
                .with_bandwidths(leader_bandwidth, bandwidths);
        let engine = SimulationEngine::<RotorLatencySimulation<_, _>>::new(builder, environment);
        info!("rotor latency sim (sequential)");
        engine.run_many_sequential(1000);
        // info!("rotor latency sim (parallel)");
        // engine.run_many_parallel(1000);

        // latency experiments with random leaders
        for (n, k) in SHRED_COMBINATIONS {
            info!("{test_name} latency tests (random leaders, n={n}, k={k})");
            let leader_bandwidth = 1_000_000_000;
            let bandwidths = vec![leader_bandwidth; validators.len()];
            let tester = LatencyTest::new(
                validators_with_ping_data,
                ping_leader_sampler.clone(),
                ping_rotor_sampler.clone(),
                n,
                k,
            )
            .with_bandwidths(leader_bandwidth, bandwidths);
            let test_name = format!("{test_name}-{n}-{k}");
            tester.run_many(&test_name, 1000, LatencyTestStage::Final2);
        }

        // latency experiments with fixed leaders
        let cities = if test_name.starts_with("solana") {
            vec![
                "Westpoort",
                "Frankfurt",
                "London",
                "Zurich",
                "New York City",
                "Los Angeles",
                "Tokyo",
                "Singapore",
                "Cape Town",
                "Buenos Aires",
            ]
        } else if test_name.starts_with("sui") {
            vec![
                "Los Angeles",
                // "New Jersey",
                "Dublin",
                "London",
                "Paris",
                "Frankfurt",
                "Singapore",
                "Tokyo",
            ]
        } else if test_name.starts_with("5hubs") {
            vec![
                "San Francisco",
                "New York City",
                "London",
                "Shanghai",
                "Tokyo",
            ]
        } else if test_name.starts_with("stock_exchanges") {
            vec![
                "Toronto",
                "New York City",
                "Westpoort",
                "Taipei",
                "Pune",
                "Shanghai",
                "Hong Kong",
                "Tokyo",
            ]
        } else {
            unimplemented!()
        };

        for (n, k) in &SHRED_COMBINATIONS {
            cities.par_iter().for_each(|city| {
                info!("{test_name} latency tests (fixed leader in {city}, n={n}, k={k})");
                let leader = find_leader_in_city(validators_with_ping_data, city);
                let tester = LatencyTest::new(
                    validators_with_ping_data,
                    ping_leader_sampler.clone(),
                    ping_rotor_sampler.clone(),
                    *n,
                    *k,
                );
                let test_name = format!("{test_name}-{n}-{k}");
                tester.run_many_with_leader(&test_name, 1000, LatencyTestStage::Final2, leader);
            });
        }
    }

    if RUN_CRASH_ROTOR_TESTS || RUN_BYZANTINE_ROTOR_TESTS {
        // TODO: clean up code
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("rotor_robustness")
            .join("rotor_robustness")
            .with_extension("csv");
        let file = File::options().append(true).open(filename).unwrap();
        let mut writer = csv::Writer::from_writer(file);

        if RUN_CRASH_ROTOR_TESTS {
            // Rotor robustness experiments (Crash + Byz., 40%)
            for (n, k) in &SHRED_COMBINATIONS {
                info!("{test_name} robustness test (crash=0.4, n={n}, k={k})");
                let tester =
                    RotorRobustnessTest::new(validators.to_vec(), rotor_sampler.clone(), *n, *k);
                tester.run(test_name, 0.4, &mut writer);
            }
        }

        if RUN_BYZANTINE_ROTOR_TESTS {
            // Rotor robustness experiments (Byzantine only, 20%)
            for (n, k) in &SHRED_COMBINATIONS {
                info!("{test_name} robustness test (byz=0.2, n={n}, k={k})");
                let tester =
                    RotorRobustnessTest::new(validators.to_vec(), rotor_sampler.clone(), *n, *k);
                tester.run(test_name, 0.2, &mut writer);
            }
        }
    }
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
