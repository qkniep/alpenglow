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
//! All simulations are evaluated on different stake distributions (uncomment in [`main`]) and for
//! different sampling strategies (toggle via the `RUN_*` constants in the configuration section).

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
use ::alpenglow::disseminator::rotor::{
    QuorumSamplingStrategy, SamplingStrategy, StakeWeightedSampler,
};
use ::alpenglow::network::simulated::ping_data::PingServer;
use ::alpenglow::network::simulated::stake_distribution::{
    VALIDATOR_DATA, ValidatorData, validators_from_validator_data,
};
use ::alpenglow::{Stake, ValidatorId, ValidatorInfo, logging};
use clap::Parser;
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

// ─── Simulation parameters ────────────────────────────────────────────────────

/// Number of leaders sampled per slot.
const NUM_LEADERS: usize = 8;

/// Number of slices per block in the Rotor dissemination protocol.
const NUM_SLICES: usize = 40;

/// Shred counts to sweep (total relays per slice in Rotor).
const SHRED_COUNTS: &[usize] = &[64, 128, 256, 512];

/// Uplink bandwidth caps to evaluate in the bandwidth simulation (bits per second).
const MAX_BANDWIDTHS: &[u64] = &[
    100_000_000,     // 100 Mbps
    1_000_000_000,   // 1 Gbps
    10_000_000_000,  // 10 Gbps
    100_000_000_000, // 100 Gbps
];

/// (data_shreds, total_shreds) pairs for Rotor robustness tests.
const ROBUSTNESS_CONFIGS: &[(usize, usize)] = &[(32, 64)];

// ─── Test suite toggles ───────────────────────────────────────────────────────

const RUN_BANDWIDTH_TESTS: bool = true;
const RUN_LATENCY_TESTS: bool = true;
const RUN_ROTOR_ROBUSTNESS_TESTS: bool = true;

// ─── Sampling strategy toggles ───────────────────────────────────────────────

const RUN_STAKE_WEIGHTED: bool = true;
const RUN_UNIFORM: bool = false;
const RUN_FA1_IID: bool = false;
const RUN_FA2: bool = false;
const RUN_FA1_PARTITION: bool = false;
const RUN_DECAYING_ACCEPTANCE: bool = false;
const RUN_TURBINE: bool = false;

// ─────────────────────────────────────────────────────────────────────────────

/// Runs the full test suite for one sampling strategy across all shred counts.
///
/// For each shred count in [`SHRED_COUNTS`], the macro creates appropriately-sized
/// leader and rotor samplers via the provided closures, then calls
/// [`run_bandwidth_tests`] and [`run_latency_tests`].
///
/// # Arguments
/// - `$dist`: distribution name label (e.g. `"solana"`)
/// - `$validators`: validator list without ping data, for bandwidth tests
/// - `$ping_vals`: validator list extracted from ping data, for latency tests
/// - `$ping_data`: full `(ValidatorInfo, PingServer)` slice, for environment + city lookup
/// - `$env`: pre-built [`SimulationEnvironment`]
/// - `$bw_writers`: `Option<BandwidthWriters>` — `Some` iff bandwidth tests are enabled
/// - `name`: short label used in output file names
/// - `leader`: closure `|vals: &[ValidatorInfo], quorum_size: usize| -> L`
/// - `rotor`: closure `|vals: &[ValidatorInfo], quorum_size: usize| -> R`
macro_rules! run_strategy {
    (
        $dist:expr,
        $validators:expr, $ping_vals:expr, $ping_data:expr,
        $env:expr, $bw_writers:expr,
        name: $name:literal,
        leader: $leader_fn:expr,
        rotor: $rotor_fn:expr $(,)?
    ) => {{
        let leader_sampler = $leader_fn(&$validators, NUM_LEADERS);
        let ping_leader_sampler = $leader_fn(&$ping_vals, NUM_LEADERS);
        for &shreds in SHRED_COUNTS {
            let test_name = format!("{}-{}-{}", $dist, $name, shreds);
            let rotor_sampler = $rotor_fn(&$validators, shreds);
            let ping_rotor_sampler = $rotor_fn(&$ping_vals, shreds);
            if let Some(ref writers) = $bw_writers {
                run_bandwidth_tests(
                    &test_name, &$validators,
                    &leader_sampler, &rotor_sampler,
                    writers,
                );
            }
            if RUN_LATENCY_TESTS {
                run_latency_tests(
                    &test_name, $dist,
                    &$ping_data, &$env,
                    &ping_leader_sampler, &ping_rotor_sampler,
                )?;
            }
        }
    }};
}

/// Alpenglow protocol simulations.
#[derive(Debug, Parser)]
#[command(version, about)]
struct Args {}

fn main() -> Result<()> {
    color_eyre::install()?;
    Args::parse();
    logging::enable_logforth();

    crate::ryse::run_robustness_tests();
    crate::pyjama::run_robustness_tests();

    for &shreds in SHRED_COUNTS {
        run_ryse_robustness_test(shreds as u64)?;
        run_pyjama_robustness_test(shreds as u64)?;
    }

    run_tests_for_distribution("solana", &VALIDATOR_DATA)?;
    // run_tests_for_distribution("sui", &SUI_VALIDATOR_DATA)?;
    // run_tests_for_distribution("5hubs", &FIVE_HUBS_VALIDATOR_DATA)?;
    // run_tests_for_distribution("stock_exchanges", &STOCK_EXCHANGES_VALIDATOR_DATA)?;

    Ok(())
}

fn run_tests_for_distribution(
    distribution_name: &str,
    validator_data: &[ValidatorData],
) -> Result<()> {
    let (validators, mut validators_and_ping_servers) =
        validators_from_validator_data(validator_data);

    validators_and_ping_servers.sort_by_key(|(v, _)| Reverse(v.stake));
    for (i, (v, _)) in validators_and_ping_servers.iter_mut().enumerate() {
        v.id = ValidatorId::new(i as u64);
    }

    let validators_with_pings: Vec<ValidatorInfo> = validators_and_ping_servers
        .iter()
        .map(|(v, _)| v.clone())
        .collect();

    let environment = build_latency_environment(&validators_with_pings, &validators_and_ping_servers);
    if RUN_LATENCY_TESTS {
        std::fs::create_dir_all("data/output")?;
    }
    let bw_writers = if RUN_BANDWIDTH_TESTS {
        Some(BandwidthWriters::create()?)
    } else {
        None
    };

    // ─── Sampling strategies ─────────────────────────────────────────────────
    // Toggle strategies via the RUN_* constants in the configuration section above.

    if RUN_STAKE_WEIGHTED {
        run_strategy!(
            distribution_name,
            validators, validators_with_pings, validators_and_ping_servers,
            environment, bw_writers,
            name: "stake_weighted",
            leader: |vals: &[ValidatorInfo], n| {
                StakeWeightedSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
            rotor: |vals: &[ValidatorInfo], n| {
                StakeWeightedSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
        );
    }
    if RUN_UNIFORM {
        run_strategy!(
            distribution_name,
            validators, validators_with_pings, validators_and_ping_servers,
            environment, bw_writers,
            name: "uniform",
            leader: |vals: &[ValidatorInfo], n| {
                UniformSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
            rotor: |vals: &[ValidatorInfo], n| {
                UniformSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
        );
    }
    if RUN_FA1_IID {
        run_strategy!(
            distribution_name,
            validators, validators_with_pings, validators_and_ping_servers,
            environment, bw_writers,
            name: "fa1_iid",
            leader: |vals: &[ValidatorInfo], n| {
                StakeWeightedSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
            rotor: |vals: &[ValidatorInfo], n| {
                FaitAccompli1Sampler::new_with_stake_weighted_fallback(vals.to_vec(), n as u64)
            },
        );
    }
    if RUN_FA2 {
        run_strategy!(
            distribution_name,
            validators, validators_with_pings, validators_and_ping_servers,
            environment, bw_writers,
            name: "fa2",
            leader: |vals: &[ValidatorInfo], n| {
                StakeWeightedSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
            rotor: |vals: &[ValidatorInfo], n| {
                FaitAccompli2Sampler::new(vals.to_vec(), n as u64)
            },
        );
    }
    if RUN_FA1_PARTITION {
        run_strategy!(
            distribution_name,
            validators, validators_with_pings, validators_and_ping_servers,
            environment, bw_writers,
            name: "fa1_partition",
            leader: |vals: &[ValidatorInfo], n| {
                StakeWeightedSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
            rotor: |vals: &[ValidatorInfo], n| {
                FaitAccompli1Sampler::new_with_partition_fallback(vals.to_vec(), n as u64)
            },
        );
    }
    if RUN_DECAYING_ACCEPTANCE {
        run_strategy!(
            distribution_name,
            validators, validators_with_pings, validators_and_ping_servers,
            environment, bw_writers,
            name: "decaying_acceptance",
            leader: |vals: &[ValidatorInfo], n| {
                StakeWeightedSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
            rotor: |vals: &[ValidatorInfo], n| {
                DecayingAcceptanceSampler::new(vals.to_vec(), 3.0, n)
            },
        );
    }
    if RUN_TURBINE {
        run_strategy!(
            distribution_name,
            validators, validators_with_pings, validators_and_ping_servers,
            environment, bw_writers,
            name: "turbine",
            leader: |vals: &[ValidatorInfo], n| {
                TurbineSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
            rotor: |vals: &[ValidatorInfo], n| {
                TurbineSampler::new(vals.to_vec()).into_quorum_strategy(n)
            },
        );
    }

    // ─────────────────────────────────────────────────────────────────────────

    if RUN_ROTOR_ROBUSTNESS_TESTS {
        for &(data_shreds, total_shreds) in ROBUSTNESS_CONFIGS {
            run_rotor_robustness_test(data_shreds, total_shreds)?;
        }
    }

    Ok(())
}

/// Shared CSV writers for bandwidth test output.
struct BandwidthWriters {
    supported: Arc<Mutex<csv::Writer<File>>>,
    usage: Arc<Mutex<csv::Writer<File>>>,
}

impl BandwidthWriters {
    /// Creates the output directory and opens fresh CSV files for writing.
    fn create() -> Result<Self> {
        let dir = PathBuf::from("data")
            .join("output")
            .join("simulations")
            .join("bandwidth");
        std::fs::create_dir_all(&dir)?;

        let supported = Arc::new(Mutex::new(csv::Writer::from_writer(File::create(
            dir.join("bandwidth_supported.csv"),
        )?)));
        let usage = Arc::new(Mutex::new(csv::Writer::from_writer(File::create(
            dir.join("bandwidth_usage.csv"),
        )?)));

        Ok(Self { supported, usage })
    }
}

/// Runs the bandwidth test for a single strategy at a single shred count.
///
/// Evaluates every bandwidth cap in [`MAX_BANDWIDTHS`] in parallel.
fn run_bandwidth_tests<
    L: SamplingStrategy + Clone + Send + Sync,
    R: QuorumSamplingStrategy + Clone + Send + Sync,
>(
    test_name: &str,
    validators: &[ValidatorInfo],
    leader_sampler: &L,
    rotor_sampler: &R,
    writers: &BandwidthWriters,
) {
    info!(
        "{test_name} bandwidth test ({} shreds)",
        rotor_sampler.quorum_size()
    );
    MAX_BANDWIDTHS.into_par_iter().for_each(|&max_bandwidth| {
        let bandwidths = vec![max_bandwidth; validators.len()];
        let mut tester = BandwidthTest::new(
            validators,
            max_bandwidth,
            bandwidths,
            leader_sampler.clone(),
            rotor_sampler.clone(),
        );
        tester.run_multiple(1_000_000);
        tester.evaluate_supported(test_name, &writers.supported);
        tester.evaluate_usage(test_name, writers.usage.clone());
    });
}

/// Runs all latency simulations for a single strategy at a single shred count.
///
/// Simulates Rotor, Ryse, Pyjama, and Alpenglow (random and fixed leaders).
/// Output files are named `<protocol>_<test_name>.csv`.
fn run_latency_tests<
    L: SamplingStrategy + QuorumSamplingStrategy + Clone + Send + Sync,
    R: QuorumSamplingStrategy + Clone + Send + Sync,
>(
    test_name: &str,
    distribution_name: &str,
    validators_and_ping_servers: &[(ValidatorInfo, &'static PingServer)],
    environment: &SimulationEnvironment,
    ping_leader_sampler: &L,
    ping_rotor_sampler: &R,
) -> Result<()> {
    let q = ping_rotor_sampler.quorum_size();
    let leader_q = ping_leader_sampler.quorum_size();
    let rotor_params = RotorParams::new(q / 2, q, NUM_SLICES);

    // Rotor standalone latency
    {
        let builder = RotorInstanceBuilder::new(
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            rotor_params,
        );
        let engine = SimulationEngine::<RotorLatencySimulation<_, _>>::new(
            builder,
            environment.clone(),
        );
        info!("{test_name} rotor latency sim");
        engine.run_many_parallel(1000);
        engine
            .stats()
            .write_to_csv(format!("data/output/rotor_{test_name}.csv"), &rotor_params)?;
    }

    // Ryse latency
    {
        let ryse_params = RyseParameters::new(leader_q as u64, q as u64);
        let ryse_builder = RyseInstanceBuilder::new(
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            ryse_params,
        );
        let params = ryse::LatencySimParams::new(ryse_params, 4, 1);
        let builder = ryse::LatencySimInstanceBuilder::new(ryse_builder, params.clone());
        let engine =
            SimulationEngine::<RyseLatencySimulation<_, _>>::new(builder, environment.clone());
        info!("{test_name} ryse latency sim");
        engine.run_many_parallel(1000);
        engine
            .stats()
            .write_to_csv(format!("data/output/ryse_{test_name}.csv"), &params)?;
    }

    // Pyjama latency
    {
        let pyjama_params = PyjamaParams::new(leader_q as u64, q as u64);
        let builder = PyjamaInstanceBuilder::new(
            ping_leader_sampler.clone(),
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            pyjama_params,
        );
        let engine = SimulationEngine::<PyjamaLatencySimulation<_, _, _>>::new(
            builder,
            environment.clone(),
        );
        info!("{test_name} pyjama latency sim");
        engine.run_many_parallel(1000);
        engine
            .stats()
            .write_to_csv(format!("data/output/pyjama_{test_name}.csv"), &pyjama_params)?;
    }

    // Alpenglow latency — random leaders
    let alpenglow_params = LatencySimParams::new(rotor_params, 4, 1);
    {
        let rotor_builder = RotorInstanceBuilder::new(
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            rotor_params,
        );
        let builder = LatencySimInstanceBuilder::new(rotor_builder, alpenglow_params.clone());
        let engine = SimulationEngine::<AlpenglowLatencySimulation<_, _>>::new(
            builder,
            environment.clone(),
        );
        info!("{test_name} alpenglow latency sim (random leaders)");
        engine.run_many_parallel(1000);
        engine.stats().write_to_csv(
            format!("data/output/alpenglow_{test_name}.csv"),
            &alpenglow_params,
        )?;
    }

    // Alpenglow latency — fixed leaders per city
    {
        let cities = cities_for_distribution(distribution_name);
        cities.par_iter().try_for_each(|city| {
            let leader = find_leader_in_city(validators_and_ping_servers, city);
            let rotor_builder = RotorInstanceBuilder::new(
                AllSameSampler(leader),
                ping_rotor_sampler.clone(),
                rotor_params,
            );
            let builder =
                LatencySimInstanceBuilder::new(rotor_builder, alpenglow_params.clone());
            let engine = SimulationEngine::<AlpenglowLatencySimulation<_, _>>::new(
                builder,
                environment.clone(),
            );
            info!("{test_name} alpenglow latency sim (fixed leader in {city})");
            engine.run_many_sequential(1000);
            engine.stats().write_to_csv(
                format!("data/output/alpenglow_{city}_{test_name}.csv"),
                &alpenglow_params,
            )
        })?;
    }

    Ok(())
}

/// Builds a [`SimulationEnvironment`] with stake-proportional bandwidth caps for latency tests.
fn build_latency_environment(
    validators_with_pings: &[ValidatorInfo],
    validators_and_ping_servers: &[(ValidatorInfo, &'static PingServer)],
) -> SimulationEnvironment {
    let total_stake: Stake = validators_with_pings.iter().map(|v| v.stake).sum();

    let leader_bandwidth: u64 = 10_000_000_000; // 10 Gbps
    let min_bandwidth: u64 = 1_000_000_000; // 1 Gbps
    let bandwidths = validators_with_pings
        .iter()
        .map(|v| {
            let stake_fraction = v.stake.inner() as f64 / total_stake.inner() as f64;
            let proportional =
                (stake_fraction * validators_with_pings.len() as f64 * leader_bandwidth as f64)
                    .round() as u64;
            proportional.max(min_bandwidth)
        })
        .collect();

    SimulationEnvironment::from_validators_with_ping_data(validators_and_ping_servers)
        .with_bandwidths(leader_bandwidth, bandwidths)
}

/// Returns the list of cities used for fixed-leader Alpenglow latency tests.
fn cities_for_distribution(distribution_name: &str) -> Vec<&'static str> {
    if distribution_name.starts_with("solana") {
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
    } else if distribution_name.starts_with("sui") {
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
    } else if distribution_name.starts_with("5hubs") {
        vec![
            "San Francisco",
            "Secaucus", // NYC/NJ
            "London",
            "Shanghai",
            "Tokyo",
        ]
    } else if distribution_name.starts_with("stock_exchanges") {
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
        unimplemented!("no city list defined for distribution: {distribution_name}")
    }
}

/// Finds the first validator located in the given city.
///
/// # Panics
///
/// Panics if no validator is found in `city`.
fn find_leader_in_city(
    validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
    city: &str,
) -> ValidatorInfo {
    validators_with_ping_data
        .iter()
        .find(|(_, p)| p.location == city)
        .map(|(v, _)| v.clone())
        .unwrap_or_else(|| panic!("no validator found in {city}"))
}
