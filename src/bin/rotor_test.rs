// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet};

use alpenglow::crypto::aggsig::SecretKey;
use alpenglow::disseminator::rotor::sampling_strategy::FaitAccompli1Sampler;
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::network::simulated::ping_data::{PingServer, find_closest_ping_server, get_ping};
use alpenglow::network::simulated::stake_distribution::VALIDATOR_DATA;
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use color_eyre::Result;
use rand::SeedableRng;
use rand::seq::SliceRandom;
use tracing::level_filters::LevelFilter;
use tracing::{info, warn};
use tracing_subscriber::{EnvFilter, prelude::*};

fn main() -> Result<()> {
    color_eyre::install()?;

    // enable `tracing` and `tokio-console`
    let console_layer = console_subscriber::spawn();
    let filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::DEBUG.into())
        .from_env_lossy();
    tracing_subscriber::registry()
        .with(console_layer)
        .with(filter)
        .with(tracing_subscriber::fmt::layer())
        .init();

    // turn ValidatorData into ValidatorInfo
    let mut validators = Vec::new();
    for v in VALIDATOR_DATA.iter() {
        if !(v.is_active && v.delinquent == Some(false)) {
            continue;
        }
        let stake = v.active_stake.unwrap_or(0);
        if stake > 0 {
            let sk = SecretKey::new(&mut rand::rng());
            validators.push(ValidatorInfo {
                id: validators.len() as ValidatorId,
                stake,
                pubkey: sk.to_pk(),
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
        validators_with_ping_data.push((
            ValidatorInfo {
                id: validators_with_ping_data.len() as ValidatorId,
                stake,
                pubkey: sk.to_pk(),
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
            if get_ping(p1.id, p2.id).is_none() {
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

    validators_with_ping_data
        .iter_mut()
        .enumerate()
        .for_each(|(i, v)| {
            v.0.id = i as ValidatorId;
        });
    let mut validator_to_ping_server = HashMap::new();
    for (v, p) in &validators_with_ping_data {
        validator_to_ping_server.insert(v.id, *p);
    }

    let validators_with_ping_data: Vec<_> =
        validators_with_ping_data.into_iter().map(|v| v.0).collect();
    let leader_sampler = StakeWeightedSampler::new(validators_with_ping_data.clone());
    let fallback = StakeWeightedSampler::new(validators_with_ping_data.clone());
    let rotor_sampler = FaitAccompli1Sampler::new(validators_with_ping_data.clone(), fallback);
    latency_test(
        validators_with_ping_data,
        validator_to_ping_server,
        leader_sampler,
        rotor_sampler,
    );

    let sampler = StakeWeightedSampler::new(validators.clone());
    rotor_sampling_test(validators.clone(), sampler, 64);

    let fallback = StakeWeightedSampler::new(validators.clone());
    let sampler = FaitAccompli1Sampler::new(validators.clone(), fallback);
    rotor_sampling_test(validators.clone(), sampler, 64);

    Ok(())
}

#[derive(Default)]
struct LatencyStats {
    max_latency: f64,
    p60_latency: f64,
    p80_latency: f64,
    count: u64,
}

impl LatencyStats {
    fn new() -> Self {
        Self::default()
    }

    fn record_latencies(
        &mut self,
        mut latencies: Vec<(f64, ValidatorId)>,
        validators: &[ValidatorInfo],
    ) {
        latencies.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let max_rotor_latency = latencies.last().unwrap().0;
        let mut p60_rotor_latency = 0.0;
        let mut stake_so_far = 0;
        for (latency, v) in &latencies {
            stake_so_far += validators[*v as usize].stake;
            if stake_so_far as f64 > total_stake as f64 * 0.6 {
                p60_rotor_latency = *latency;
                break;
            }
        }
        let mut p80_rotor_latency = 0.0;
        let mut stake_so_far = 0;
        for (latency, v) in &latencies {
            stake_so_far += validators[*v as usize].stake;
            if stake_so_far as f64 > total_stake as f64 * 0.8 {
                p80_rotor_latency = *latency;
                break;
            }
        }
        self.max_latency += max_rotor_latency;
        self.p60_latency += p60_rotor_latency;
        self.p80_latency += p80_rotor_latency;
        self.count += 1;
    }

    fn print(&self) {
        let avg_max_latency = self.max_latency / self.count as f64;
        let avg_p60_latency = self.p60_latency / self.count as f64;
        let avg_p80_latency = self.p80_latency / self.count as f64;
        info!("avg max latency: {:.2}", avg_max_latency);
        info!("avg p60 latency: {:.2}", avg_p60_latency);
        info!("avg p80 latency: {:.2}", avg_p80_latency);
    }
}

fn latency_test(
    validators: Vec<ValidatorInfo>,
    validator_to_ping_server: HashMap<ValidatorId, &PingServer>,
    leader_sampler: impl SamplingStrategy,
    rotor_sampler: impl SamplingStrategy,
) {
    let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
    let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
    let mut direct_stats = LatencyStats::new();
    let mut rotor_stats = LatencyStats::new();
    let mut notar_stats = LatencyStats::new();
    let mut fast_final_stats = LatencyStats::new();
    let mut slow_final_stats = LatencyStats::new();
    let leader = leader_sampler.sample(&mut rng);
    let leader_location = &validator_to_ping_server[&leader.id].location;
    info!("leader location: {}", leader_location);
    for _ in 0..100 {
        let relays = rotor_sampler.sample_multiple(96, &mut rng);
        let mut relay_latencies = Vec::new();
        for relay in &relays {
            let leader_ping_server = validator_to_ping_server[&leader.id].id;
            let relay_ping_server = validator_to_ping_server[&relay.id].id;
            let latency = get_ping(leader_ping_server, relay_ping_server).unwrap();
            relay_latencies.push(latency);
        }

        let mut direct_latencies = Vec::new();
        for v in &validators {
            let leader_ping_server = validator_to_ping_server[&leader.id].id;
            let v_ping_server = validator_to_ping_server[&v.id].id;
            let latency = get_ping(leader_ping_server, v_ping_server).unwrap();
            direct_latencies.push((latency, v.id));
        }

        let mut rotor_latencies = Vec::new();
        for v in &validators {
            let mut latencies = Vec::new();
            for (relay, latency) in relays.iter().zip(relay_latencies.iter()) {
                let relay_ping_server = validator_to_ping_server[&relay.id].id;
                let v_ping_server = validator_to_ping_server[&v.id].id;
                let latency = latency + get_ping(relay_ping_server, v_ping_server).unwrap();
                latencies.push(latency);
            }
            latencies.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let threshold_latency = latencies[31];
            rotor_latencies.push((threshold_latency, v.id));
        }

        let mut notar_latencies = Vec::new();
        for (v1_rotor_latency, v1) in &rotor_latencies {
            let mut latencies = Vec::new();
            for (v2_rotor_latency, v2) in &rotor_latencies {
                let v1_ping_server = validator_to_ping_server[v1].id;
                let v2_ping_server = validator_to_ping_server[v2].id;
                let latency = v2_rotor_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                latencies.push((latency, *v2));
            }
            latencies.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let mut notar_latency = 0.0;
            let mut stake_so_far = 0;
            for (latency, v) in &latencies {
                stake_so_far += validators[*v as usize].stake;
                if stake_so_far as f64 > total_stake as f64 * 0.6 {
                    notar_latency = *latency;
                    break;
                }
            }
            notar_latency = notar_latency.max(*v1_rotor_latency);
            notar_latencies.push((notar_latency, *v1));
        }

        let mut fast_final_latencies = Vec::new();
        for (v1_rotor_latency, v1) in &rotor_latencies {
            let mut latencies = Vec::new();
            for (v2_rotor_latency, v2) in &rotor_latencies {
                let v1_ping_server = validator_to_ping_server[v1].id;
                let v2_ping_server = validator_to_ping_server[v2].id;
                let latency = v2_rotor_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                latencies.push((latency, *v2));
            }
            latencies.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let mut fast_final_latency = 0.0;
            let mut stake_so_far = 0;
            for (latency, v) in &latencies {
                stake_so_far += validators[*v as usize].stake;
                if stake_so_far as f64 > total_stake as f64 * 0.8 {
                    fast_final_latency = *latency;
                    break;
                }
            }
            fast_final_latency = fast_final_latency.max(*v1_rotor_latency);
            fast_final_latencies.push((fast_final_latency, *v1));
        }

        let mut slow_final_latencies = Vec::new();
        for (v1_notar_latency, v1) in &notar_latencies {
            let mut latencies = Vec::new();
            for (v2_notar_latency, v2) in &notar_latencies {
                let v1_ping_server = validator_to_ping_server[v1].id;
                let v2_ping_server = validator_to_ping_server[v2].id;
                let latency = v2_notar_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                latencies.push((latency, *v2));
            }
            latencies.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let mut slow_final_latency = 0.0;
            let mut stake_so_far = 0;
            for (latency, v) in &latencies {
                stake_so_far += validators[*v as usize].stake;
                if stake_so_far as f64 > total_stake as f64 * 0.6 {
                    slow_final_latency = *latency;
                    break;
                }
            }
            slow_final_latency = slow_final_latency.max(*v1_notar_latency);
            slow_final_latencies.push((slow_final_latency, *v1));
        }

        direct_stats.record_latencies(direct_latencies, &validators);
        rotor_stats.record_latencies(rotor_latencies, &validators);
        notar_stats.record_latencies(notar_latencies, &validators);
        fast_final_stats.record_latencies(fast_final_latencies, &validators);
        slow_final_stats.record_latencies(slow_final_latencies, &validators);
    }
    info!("Direct:");
    direct_stats.print();
    info!("Rotor:");
    rotor_stats.print();
    info!("Notarization:");
    notar_stats.print();
    info!("Fast-Finalization:");
    fast_final_stats.print();
    info!("Slow-Finalization:");
    slow_final_stats.print();
}

fn rotor_sampling_test(
    validators: Vec<ValidatorInfo>,
    sampler: impl SamplingStrategy,
    num_shreds: usize,
) {
    let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
    let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
    let mut validators_to_corrupt = validators.clone();
    let mut failures = 0;
    for _ in 0..1_000_000 {
        // greedily corrupt up to 40% of validators
        let mut corrupted = HashSet::new();
        let mut corrupted_stake = 0.0;
        validators_to_corrupt.shuffle(&mut rng);

        for v in &validators_to_corrupt {
            let rel_stake = v.stake as f64 / total_stake as f64;
            if corrupted_stake + rel_stake <= 0.4 {
                corrupted.insert(v.id);
                corrupted_stake += rel_stake;
            }
        }

        let sampled = sampler.sample_multiple(num_shreds, &mut rng);
        let mut corrupted_samples = 0;
        for v in sampled {
            if corrupted.contains(&v.id) {
                corrupted_samples += 1;
            }
        }
        if corrupted_samples > num_shreds - 32 {
            failures += 1;
        }
    }
    info!(
        "failures: {} ({}%)",
        failures,
        failures as f64 / 1e6 * 100.0
    );
}
