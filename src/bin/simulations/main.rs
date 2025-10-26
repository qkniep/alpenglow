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
//! The global constants [`RUN_BANDWIDTH_TESTS`], [`RUN_LATENCY_TESTS`], and
//! [`RUN_ROTOR_ROBUSTNESS_TESTS`] control which tests to run.
//! Further, the global constants [`SAMPLING_STRATEGIES`], [`MAX_BANDWIDTHS`],
//! and [`SHRED_COMBINATIONS`] control the parameters for some tests.

#![deny(rustdoc::broken_intra_doc_links)]

mod alpenglow;
mod discrete_event_simulator;
mod pyjama;
mod quorum_robustness;
mod rotor;
mod ryse;

use std::cmp::Reverse;
use std::fs::File;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use ::alpenglow::disseminator::rotor::sampling_strategy::{
    AllSameSampler, DecayingAcceptanceSampler, FaitAccompli1Sampler, FaitAccompli2Sampler,
    TurbineSampler, UniformSampler,
};
use ::alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use ::alpenglow::network::simulated::ping_data::PingServer;
use ::alpenglow::network::simulated::stake_distribution::{
    VALIDATOR_DATA, ValidatorData, validators_from_validator_data,
};
use ::alpenglow::{Stake, ValidatorId, ValidatorInfo, logging};
use color_eyre::Result;
use log::info;
use rayon::prelude::*;

use crate::alpenglow::{
    AlpenglowLatencySimulation, BandwidthTest, LatencySimInstanceBuilder, LatencySimParams,
};
use crate::discrete_event_simulator::{SimulationEngine, SimulationEnvironment};
use crate::pyjama::{
    PyjamaInstanceBuilder, PyjamaLatencySimulation, PyjamaParams, run_pyjama_robustness_test,
};
use crate::rotor::{
    RotorInstanceBuilder, RotorLatencySimulation, RotorParams, run_rotor_robustness_test,
};
use crate::ryse::{
    RyseInstanceBuilder, RyseLatencySimulation, RyseParameters, run_ryse_robustness_test,
};

const RUN_BANDWIDTH_TESTS: bool = false;
const RUN_LATENCY_TESTS: bool = true;
const RUN_ROTOR_ROBUSTNESS_TESTS: bool = true;

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

    crate::ryse::run_robustness_tests();
    crate::pyjama::run_robustness_tests();

    for k in [64, 128, 256, 512] {
        run_ryse_robustness_test(k)?;
        run_pyjama_robustness_test(k)?;
    }

    if RUN_BANDWIDTH_TESTS {
        // create bandwidth evaluation files
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth")
            .join("bandwidth_supported")
            .with_extension("csv");
        if let Some(parent) = filename.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let _ = File::create(filename)?;
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth")
            .join("bandwidth_usage")
            .with_extension("csv");
        if let Some(parent) = filename.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let _ = File::create(filename)?;
    }

    if RUN_ROTOR_ROBUSTNESS_TESTS {
        // create saftey evaluation file
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("rotor_robustness")
            .join("rotor_robustness")
            .with_extension("csv");
        if let Some(parent) = filename.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let _ = File::create(filename)?;
    }

    // run tests for different stake distributions
    run_tests_for_stake_distribution("solana", &VALIDATOR_DATA)?;
    // run_tests_for_stake_distribution("sui", &SUI_VALIDATOR_DATA);
    // run_tests_for_stake_distribution("5hubs", &FIVE_HUBS_VALIDATOR_DATA);
    // run_tests_for_stake_distribution("stock_exchanges", &STOCK_EXCHANGES_VALIDATOR_DATA);

    Ok(())
}

fn run_tests_for_stake_distribution(
    distribution_name: &str,
    validator_data: &[ValidatorData],
) -> Result<()> {
    // load validator and ping data
    let (validators, mut validators_and_ping_servers) =
        validators_from_validator_data(validator_data);

    // sort by stake (from highest to lowest)
    validators_and_ping_servers.sort_by_key(|(v, _)| Reverse(v.stake));
    for (i, (v, _)) in validators_and_ping_servers.iter_mut().enumerate() {
        v.id = i as ValidatorId;
    }

    // extract the validators only
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
            )?;
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
            )?;
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
            )?;
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
            )?;
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
            )?;
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
            )?;
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
            )?;
        }
    }

    Ok(())
}

fn run_tests<
    L: SamplingStrategy + Send + Sync + Clone,
    R: SamplingStrategy + Send + Sync + Clone,
>(
    test_name: &str,
    validators: &[ValidatorInfo],
    validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
    leader_sampler: &L,
    rotor_sampler: &R,
    ping_leader_sampler: &L,
    ping_rotor_sampler: &R,
) -> Result<()> {
    if RUN_BANDWIDTH_TESTS {
        // TODO: clean up code
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth")
            .join("bandwidth_supported")
            .with_extension("csv");
        let file = File::options().append(true).open(filename)?;
        let writer = csv::Writer::from_writer(file);
        let writer = Arc::new(Mutex::new(writer));
        let supported_writer_ref = &writer;
        let filename = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth")
            .join("bandwidth_usage")
            .with_extension("csv");
        let file = File::options().append(true).open(filename)?;
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
                tester.evaluate_supported(test_name, supported_writer_ref);
                tester.evaluate_usage(test_name, usage_writer_ref.clone());
            }
        });
    }

    if RUN_LATENCY_TESTS {
        let validators_with_pings = validators_with_ping_data
            .iter()
            .map(|(v, _)| v.clone())
            .collect::<Vec<_>>();
        let total_stake: Stake = validators_with_pings.iter().map(|v| v.stake).sum();
        let leader_bandwidth = 10_000_000_000; // 10 Gbps
        let min_bandwidth = 1_000_000_000; // 1 Gbps
        let bandwidths = validators_with_pings
            .iter()
            .map(|v| {
                ((v.stake as f64 / total_stake as f64
                    * (validators_with_pings.len() as u64 * leader_bandwidth) as f64)
                    .round() as u64)
                    .max(min_bandwidth)
            })
            .collect();
        let environment =
            SimulationEnvironment::from_validators_with_ping_data(validators_with_ping_data)
                .with_bandwidths(leader_bandwidth, bandwidths);

        // Rotor
        let params = RotorParams::new(32, 64, 40);
        let builder = RotorInstanceBuilder::new(
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            params,
        );
        let engine =
            SimulationEngine::<RotorLatencySimulation<_, _>>::new(builder, environment.clone());
        info!("rotor latency sim (sequential)");
        engine.run_many_sequential(10);
        engine
            .stats()
            .write_to_csv("data/output/rotor_10.csv", &params)?;
        info!("rotor latency sim (parallel)");
        engine.run_many_parallel(1000);
        engine
            .stats()
            .write_to_csv("data/output/rotor_1000.csv", &params)?;

        // Ryse
        let ryse_params = RyseParameters::new(8, 320);
        let ryse_builder = RyseInstanceBuilder::new(
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            ryse_params,
        );
        let params = ryse::LatencySimParams::new(ryse_params, 4, 1);
        let builder = ryse::LatencySimInstanceBuilder::new(ryse_builder, params.clone());
        let engine =
            SimulationEngine::<RyseLatencySimulation<_, _>>::new(builder, environment.clone());
        info!("ryse latency sim (parallel)");
        engine.run_many_parallel(1000);
        engine
            .stats()
            .write_to_csv("data/output/ryse_1000.csv", &params)?;

        // Pyjama
        let params = PyjamaParams::new(8, 640);
        let builder = PyjamaInstanceBuilder::new(
            ping_leader_sampler.clone(),
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            params,
        );
        let engine =
            SimulationEngine::<PyjamaLatencySimulation<_, _, _>>::new(builder, environment.clone());
        info!("pyjama latency sim (parallel)");
        engine.run_many_parallel(1000);
        engine
            .stats()
            .write_to_csv("data/output/pyjama_1000.csv", &params)?;

        // Alpenglow
        // latency experiments with random leaders
        for (n, k) in SHRED_COMBINATIONS {
            info!("{test_name} latency tests (random leaders, n={n}, k={k})");
            let rotor_params = RotorParams::new(n, k, 40);
            let rotor_builder = RotorInstanceBuilder::new(
                ping_leader_sampler.clone(),
                ping_rotor_sampler.clone(),
                rotor_params,
            );
            let params = LatencySimParams::new(rotor_params, 4, 1);
            let builder = LatencySimInstanceBuilder::new(rotor_builder, params.clone());
            let engine = SimulationEngine::<AlpenglowLatencySimulation<_, _>>::new(
                builder,
                environment.clone(),
            );
            engine.run_many_parallel(1000);
            engine
                .stats()
                .write_to_csv("data/output/alpenglow_1000.csv", &params)?;
        }

        // latency experiments with fixed leaders
        let cities = if test_name.starts_with("solana") {
            vec![
                "Westpoort", // Amsterdam
                "Frankfurt",
                "London",
                "Basel",
                "Secaucus", // NYC/NJ
                "Los Angeles",
                "Tokyo",
                "Singapore",
                "Cape Town",
                "Buenos Aires",
            ]
        } else if test_name.starts_with("sui") {
            vec![
                "Los Angeles",
                "Secaucus", // NYC/NJ
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
                "Secaucus", // NYC/NJ
                "London",
                "Shanghai",
                "Tokyo",
            ]
        } else if test_name.starts_with("stock_exchanges") {
            vec![
                "Toronto",
                "Secaucus", // NYC/NJ
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

        for (n, k) in SHRED_COMBINATIONS {
            cities.par_iter().try_for_each(|city| {
                info!("{test_name} latency tests (fixed leader in {city}, n={n}, k={k})");
                let leader = find_leader_in_city(validators_with_ping_data, city);
                let rotor_params = RotorParams::new(n, k, 40);
                let rotor_builder = RotorInstanceBuilder::new(
                    AllSameSampler(leader),
                    ping_rotor_sampler.clone(),
                    rotor_params,
                );
                let params = LatencySimParams::new(rotor_params, 4, 1);
                let builder = LatencySimInstanceBuilder::new(rotor_builder, params.clone());
                let engine = SimulationEngine::<AlpenglowLatencySimulation<_, _>>::new(
                    builder,
                    environment.clone(),
                );
                engine.run_many_sequential(1000);
                let filename = format!("data/output/alpenglow_{city}_1000.csv");
                engine.stats().write_to_csv(filename, &params)
            })?;
        }
    }

    if RUN_ROTOR_ROBUSTNESS_TESTS {
        for &(n, k) in &SHRED_COMBINATIONS {
            run_rotor_robustness_test(n, k)?;
        }
    }

    Ok(())
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
