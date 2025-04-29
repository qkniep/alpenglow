// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//!
//!
//!

mod bandwidth;
mod latency;
mod rotor_safety;

use std::collections::HashSet;

use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::rotor::sampling_strategy::{
    DecayingAcceptanceSampler, FaitAccompli1Sampler, TurbineSampler, UniformSampler,
};
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::network::simulated::ping_data::{PingServer, find_closest_ping_server, get_ping};
use alpenglow::network::simulated::stake_distribution::VALIDATOR_DATA;
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use color_eyre::Result;
use log::{info, warn};
use logforth::append;
use logforth::filter::EnvFilter;
use rayon::prelude::*;

use bandwidth::BandwidthTest;
use latency::{LatencyTest, LatencyTestStage};
use rotor_safety::RotorSafetyTest;

fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    // enable `logforth` logging
    logforth::builder()
        .dispatch(|d| {
            d.filter(EnvFilter::from_default_env())
                .append(append::Stderr::default())
        })
        .apply();

    // load validator and ping data
    let (validators, validators_and_ping_servers) = load_validators();
    let validators_with_pings: Vec<ValidatorInfo> = validators_and_ping_servers
        .iter()
        .map(|(v, _)| v.clone())
        .collect();

    // TODO: indicatif progress bar

    // run all tests for the different sampling strategies
    for sampling_strat in [
        "uniform",
        "stake_weighted",
        "fa1",
        "decaying_acceptance",
        "turbine",
    ] {
        if sampling_strat == "uniform" {
            let leader_sampler = UniformSampler::new(validators.clone());
            let ping_leader_sampler = UniformSampler::new(validators_with_pings.clone());
            let rotor_sampler = UniformSampler::new(validators.clone());
            let ping_rotor_sampler = UniformSampler::new(validators_with_pings.clone());
            run_tests(
                sampling_strat,
                &validators,
                &validators_and_ping_servers,
                leader_sampler,
                rotor_sampler,
                ping_leader_sampler,
                ping_rotor_sampler,
            );
        } else if sampling_strat == "stake_weighted" {
            let leader_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            let rotor_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_rotor_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            run_tests(
                sampling_strat,
                &validators,
                &validators_and_ping_servers,
                leader_sampler,
                rotor_sampler,
                ping_leader_sampler,
                ping_rotor_sampler,
            )
        } else if sampling_strat == "fa1" {
            let leader_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            let rotor_sampler =
                FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators.clone(), 64);
            let ping_rotor_sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(
                validators_with_pings.clone(),
                64,
            );
            run_tests(
                sampling_strat,
                &validators,
                &validators_and_ping_servers,
                leader_sampler,
                rotor_sampler,
                ping_leader_sampler,
                ping_rotor_sampler,
            )
        } else if sampling_strat == "decaying_acceptance" {
            let leader_sampler = StakeWeightedSampler::new(validators.clone());
            let ping_leader_sampler = StakeWeightedSampler::new(validators_with_pings.clone());
            let rotor_sampler = DecayingAcceptanceSampler::new(validators.clone(), 3.0);
            let ping_rotor_sampler =
                DecayingAcceptanceSampler::new(validators_with_pings.clone(), 3.0);
            run_tests(
                sampling_strat,
                &validators,
                &validators_and_ping_servers,
                leader_sampler,
                rotor_sampler,
                ping_leader_sampler,
                ping_rotor_sampler,
            )
        } else if sampling_strat == "turbine" {
            let leader_sampler = TurbineSampler::new(validators.clone());
            let ping_leader_sampler = TurbineSampler::new(validators_with_pings.clone());
            let rotor_sampler = TurbineSampler::new(validators.clone());
            let ping_rotor_sampler = TurbineSampler::new(validators_with_pings.clone());
            run_tests(
                sampling_strat,
                &validators,
                &validators_and_ping_servers,
                leader_sampler,
                rotor_sampler,
                ping_leader_sampler,
                ping_rotor_sampler,
            )
        }
    }

    Ok(())
}

fn load_validators() -> (
    Vec<ValidatorInfo>,
    Vec<(ValidatorInfo, &'static PingServer)>,
) {
    // turn ValidatorData into ValidatorInfo
    let mut validators = Vec::new();
    for v in VALIDATOR_DATA.iter() {
        if !(v.is_active && v.delinquent == Some(false)) {
            continue;
        }
        let stake = v.active_stake.unwrap_or(0);
        if stake > 0 {
            let id = validators.len() as ValidatorId;
            let sk = SecretKey::new(&mut rand::rng());
            let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
            validators.push(ValidatorInfo {
                id,
                stake,
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: String::new(),
                disseminator_address: String::new(),
                repair_address: String::new(),
            });
        }
    }

    // assign closest ping servers to validators
    let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
    let mut validators_with_ping_data = Vec::new();
    let mut stake_with_ping_server = 0;
    for v in VALIDATOR_DATA.iter() {
        let stake = v.active_stake.unwrap_or(0);
        if !(v.is_active && v.delinquent == Some(false)) || stake == 0 {
            continue;
        }
        let (Some(lat), Some(lon)) = (&v.latitude, &v.longitude) else {
            continue;
        };
        let ping_server = find_closest_ping_server(lat.parse().unwrap(), lon.parse().unwrap());
        stake_with_ping_server += stake;
        let sk = SecretKey::new(&mut rand::rng());
        let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
        validators_with_ping_data.push((
            ValidatorInfo {
                id: validators_with_ping_data.len() as ValidatorId,
                stake,
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: String::new(),
                disseminator_address: String::new(),
                repair_address: String::new(),
            },
            ping_server,
        ));
    }
    warn!(
        "discarding {:.2}% of validators w/o ping server",
        100.0 - stake_with_ping_server as f64 * 100.0 / total_stake as f64
    );

    // determine pings of validator pairs
    let mut nodes_without_ping = HashSet::new();
    for (v1, p1) in &validators_with_ping_data {
        for (v2, p2) in &validators_with_ping_data {
            if get_ping(p1.id, p2.id).is_none()
                || (get_ping(p2.id, p1.id) == Some(0.0) && p2.id != p1.id)
            {
                nodes_without_ping.insert(v1.id);
                nodes_without_ping.insert(v2.id);
            }
        }
    }
    warn!(
        "discarding {:.2}% of nodes w/o ping",
        nodes_without_ping.len() as f64 * 100.0 / validators_with_ping_data.len() as f64
    );
    warn!("{} validators without ping data", nodes_without_ping.len());
    validators_with_ping_data.retain(|(v, _)| !nodes_without_ping.contains(&v.id));
    info!(
        "{} validators with ping data",
        validators_with_ping_data.len()
    );

    // give validators with ping data consecutive IDs
    validators_with_ping_data
        .iter_mut()
        .enumerate()
        .for_each(|(i, v)| {
            v.0.id = i as ValidatorId;
        });

    (validators, validators_with_ping_data)
}

fn run_tests<
    L: SamplingStrategy + Sync + Send + Clone,
    R: SamplingStrategy + Sync + Send + Clone,
>(
    test_name: &str,
    validators: &[ValidatorInfo],
    validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
    leader_sampler: L,
    rotor_sampler: R,
    ping_leader_sampler: L,
    ping_rotor_sampler: R,
) {
    const MAX_BANDWIDTHS: [u64; 3] = [
        1_000_000_000,   // 1 Gbps
        10_000_000_000,  // 10 Gbps
        100_000_000_000, // 100 Gbps
    ];

    // bandwidth experiment
    MAX_BANDWIDTHS.into_par_iter().for_each(|max_bandwidth| {
        for num_shreds in [64, 128, 256] {
            info!(
                "{test_name} bandwidth test ({:.1} Gbps, {} shreds)",
                max_bandwidth as f64 / 1e9,
                num_shreds
            );
            let bandwidths = vec![max_bandwidth; validators.len()];
            let mut tester = BandwidthTest::new(
                validators,
                max_bandwidth,
                bandwidths,
                leader_sampler.clone(),
                rotor_sampler.clone(),
                num_shreds,
            );
            tester.run(1_000_000);
        }
    });

    const SHRED_COMBINATIONS: [(usize, usize); 5] =
        [(32, 64), (32, 80), (32, 96), (64, 128), (128, 256)];

    // latency experiments with random leaders
    SHRED_COMBINATIONS.into_par_iter().for_each(|(n, k)| {
        info!("{test_name} latency tests (random leaders, n={n}, k={k})");
        let mut tester = LatencyTest::new(
            validators_with_ping_data,
            ping_leader_sampler.clone(),
            ping_rotor_sampler.clone(),
            n,
            k,
        );
        let test_name = format!("{}-{}-{}", test_name, n, k);
        tester.run_many(&test_name, 1000, LatencyTestStage::Final);
    });

    // latency experiments with fixed leaders
    const CITIES: [&str; 10] = [
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
    ];
    for (n, k) in &SHRED_COMBINATIONS {
        CITIES.into_par_iter().for_each(|city| {
            info!("{test_name} latency tests (fixed leader in {city}, n={n}, k={k})");
            let leader = find_leader_in_city(validators_with_ping_data, city);
            let mut tester = LatencyTest::new(
                validators_with_ping_data,
                ping_leader_sampler.clone(),
                ping_rotor_sampler.clone(),
                *n,
                *k,
            );
            let test_name = format!("{}-{}-{}", test_name, n, k);
            tester.run_many_with_leader(&test_name, 1000, LatencyTestStage::Final, leader.clone());
        });
    }

    // safety experiments (Byzantine only, 20%)
    for (n, k) in &SHRED_COMBINATIONS {
        info!("{test_name} safety test (n={n}, k={k})");
        let tester = RotorSafetyTest::new(validators.to_vec(), rotor_sampler.clone(), *n, *k);
        tester.run(0.2);
    }

    // safety experiments (Crash + Byz., 40%)
    for (n, k) in &SHRED_COMBINATIONS {
        info!("{test_name} safety test (n={n}, k={k})");
        let tester = RotorSafetyTest::new(validators.to_vec(), rotor_sampler.clone(), *n, *k);
        tester.run(0.4);
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
    panic!("leader not found in {}", city);
}
