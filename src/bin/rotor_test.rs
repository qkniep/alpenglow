// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;

use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::rotor::sampling_strategy::FaitAccompli1Sampler;
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::network::simulated::ping_data::{PingServer, find_closest_ping_server, get_ping};
use alpenglow::network::simulated::stake_distribution::VALIDATOR_DATA;
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use color_eyre::Result;
use rand::SeedableRng;
use rand::seq::SliceRandom;
use rayon::prelude::*;
use tracing::level_filters::LevelFilter;
use tracing::{info, warn};
use tracing_subscriber::{EnvFilter, prelude::*};

fn main() -> Result<()> {
    color_eyre::install()?;

    // enable `tracing`
    let filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::DEBUG.into())
        .from_env_lossy();
    tracing_subscriber::registry()
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
            let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
            validators.push(ValidatorInfo {
                id: validators.len() as ValidatorId,
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
    let mut ping_servers = Vec::with_capacity(validators_with_ping_data.len());
    for (_, p) in &validators_with_ping_data {
        ping_servers.push(*p);
    }

    let validators_with_ping_data: Vec<_> =
        validators_with_ping_data.into_iter().map(|v| v.0).collect();
    (64..=128).into_par_iter().for_each(|k| {
        let leader_sampler = StakeWeightedSampler::new(validators_with_ping_data.clone());
        let rotor_sampler = FaitAccompli1Sampler::new_with_stake_weighted_fallback(
            validators_with_ping_data.clone(),
            k,
        );
        let mut tester = LatencyTest::new(
            validators_with_ping_data.clone(),
            ping_servers.clone(),
            leader_sampler,
            rotor_sampler,
            k as usize,
        );
        tester.run_many(100_000, LatencyTestStage::Rotor);
    });

    info!("StakeWeightedSampler:");
    (64..=128).into_par_iter().for_each(|k| {
        let sampler = StakeWeightedSampler::new(validators.clone());
        rotor_sampling_test(validators.clone(), sampler, k);
    });

    info!("FaitAccompli1Sampler:");
    (64..=128).into_par_iter().for_each(|k| {
        let sampler =
            FaitAccompli1Sampler::new_with_stake_weighted_fallback(validators.clone(), k as u64);
        rotor_sampling_test(validators.clone(), sampler, k);
    });

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
        latencies: &mut Vec<(f64, ValidatorId)>,
        validators: &[ValidatorInfo],
    ) {
        latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let max_rotor_latency = latencies.last().unwrap().0;
        let mut p60_rotor_latency = 0.0;
        let mut stake_so_far = 0;
        for (latency, v) in &*latencies {
            stake_so_far += validators[*v as usize].stake;
            if stake_so_far as f64 > total_stake as f64 * 0.6 {
                p60_rotor_latency = *latency;
                break;
            }
        }
        let mut p80_rotor_latency = 0.0;
        let mut stake_so_far = 0;
        for (latency, v) in &*latencies {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum LatencyTestStage {
    Direct,
    Rotor,
    Notar,
    Final,
}

struct LatencyTest<L: SamplingStrategy, R: SamplingStrategy> {
    validators: Vec<ValidatorInfo>,
    ping_servers: Vec<&'static PingServer>,
    leader_sampler: L,
    rotor_sampler: R,
    num_shreds: usize,

    direct_stats: LatencyStats,
    rotor_stats: LatencyStats,
    notar_stats: LatencyStats,
    fast_final_stats: LatencyStats,
    slow_final_stats: LatencyStats,

    relay_latencies: Vec<f64>,
    direct_latencies: Vec<(f64, ValidatorId)>,
    rotor_latencies: Vec<(f64, ValidatorId)>,
    notar_latencies: Vec<(f64, ValidatorId)>,
    fast_final_latencies: Vec<(f64, ValidatorId)>,
    slow_final_latencies: Vec<(f64, ValidatorId)>,
    tmp_latencies: Vec<f64>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencyTest<L, R> {
    fn new(
        validators: Vec<ValidatorInfo>,
        ping_servers: Vec<&'static PingServer>,
        leader_sampler: L,
        rotor_sampler: R,
        k: usize,
    ) -> Self {
        let num_val = validators.len();
        Self {
            validators,
            ping_servers,
            leader_sampler,
            rotor_sampler,
            num_shreds: k,

            direct_stats: LatencyStats::new(),
            rotor_stats: LatencyStats::new(),
            notar_stats: LatencyStats::new(),
            fast_final_stats: LatencyStats::new(),
            slow_final_stats: LatencyStats::new(),

            relay_latencies: vec![0.0; k],
            direct_latencies: vec![(0.0, 0); num_val],
            rotor_latencies: vec![(0.0, 0); num_val],
            notar_latencies: vec![(0.0, 0); num_val],
            fast_final_latencies: vec![(0.0, 0); num_val],
            slow_final_latencies: vec![(0.0, 0); num_val],
            tmp_latencies: vec![0.0; k],
        }
    }

    fn run_many(&mut self, iterations: usize, up_to_stage: LatencyTestStage) {
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
        let total_stake: Stake = self.validators.iter().map(|v| v.stake).sum();
        for _ in 0..iterations {
            let leader = self.leader_sampler.sample(&mut rng);
            let leader_location = &self.ping_servers[leader.id as usize].location;
            let relays = self
                .rotor_sampler
                .sample_multiple(self.num_shreds, &mut rng);
            for (i, relay) in relays.iter().enumerate() {
                let leader_ping_server = self.ping_servers[leader.id as usize].id;
                let relay_ping_server = self.ping_servers[relay.id as usize].id;
                let latency = get_ping(leader_ping_server, relay_ping_server).unwrap();
                self.relay_latencies[i] = latency;
            }

            for (i, v) in self.validators.iter().enumerate() {
                let leader_ping_server = self.ping_servers[leader.id as usize].id;
                let v_ping_server = self.ping_servers[v.id as usize].id;
                let latency = get_ping(leader_ping_server, v_ping_server).unwrap();
                self.direct_latencies[i] = (latency, v.id);
            }

            if up_to_stage == LatencyTestStage::Direct {
                continue;
            }

            for (i, v) in self.validators.iter().enumerate() {
                for (j, (relay, latency)) in
                    relays.iter().zip(self.relay_latencies.iter()).enumerate()
                {
                    let relay_ping_server = self.ping_servers[relay.id as usize].id;
                    let v_ping_server = self.ping_servers[v.id as usize].id;
                    let latency = latency + get_ping(relay_ping_server, v_ping_server).unwrap();
                    self.tmp_latencies[j] = latency;
                }
                self.tmp_latencies
                    .sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let threshold_latency = self.tmp_latencies[31];
                self.rotor_latencies[i] = (threshold_latency, v.id);
            }

            if up_to_stage == LatencyTestStage::Rotor {
                continue;
            }

            for (v1_rotor_latency, v1) in &self.rotor_latencies {
                let mut latencies = Vec::new();
                for (v2_rotor_latency, v2) in &self.rotor_latencies {
                    let v1_ping_server = self.ping_servers[*v1 as usize].id;
                    let v2_ping_server = self.ping_servers[*v2 as usize].id;
                    let latency =
                        v2_rotor_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                    latencies.push((latency, *v2));
                }
                latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let mut notar_latency = 0.0;
                let mut stake_so_far = 0;
                for (latency, v) in &latencies {
                    stake_so_far += self.validators[*v as usize].stake;
                    if stake_so_far as f64 > total_stake as f64 * 0.6 {
                        notar_latency = *latency;
                        break;
                    }
                }
                notar_latency = notar_latency.max(*v1_rotor_latency);
                self.notar_latencies[*v1 as usize] = (notar_latency, *v1);
            }

            if up_to_stage == LatencyTestStage::Notar {
                continue;
            }

            for (v1_rotor_latency, v1) in &self.rotor_latencies {
                let mut latencies = Vec::new();
                for (v2_rotor_latency, v2) in &self.rotor_latencies {
                    let v1_ping_server = self.ping_servers[*v1 as usize].id;
                    let v2_ping_server = self.ping_servers[*v2 as usize].id;
                    let latency =
                        v2_rotor_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                    latencies.push((latency, *v2));
                }
                latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let mut fast_final_latency: f64 = 0.0;
                let mut stake_so_far = 0;
                for (latency, v) in &latencies {
                    stake_so_far += self.validators[*v as usize].stake;
                    if stake_so_far as f64 > total_stake as f64 * 0.8 {
                        fast_final_latency = *latency;
                        break;
                    }
                }
                fast_final_latency = fast_final_latency.max(*v1_rotor_latency);
                self.fast_final_latencies[*v1 as usize] = (fast_final_latency, *v1);
            }

            for (v1_notar_latency, v1) in &self.notar_latencies {
                let mut latencies = Vec::new();
                for (v2_notar_latency, v2) in &self.notar_latencies {
                    let v1_ping_server = self.ping_servers[*v1 as usize].id;
                    let v2_ping_server = self.ping_servers[*v2 as usize].id;
                    let latency =
                        v2_notar_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                    latencies.push((latency, *v2));
                }
                latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let mut slow_final_latency: f64 = 0.0;
                let mut stake_so_far = 0;
                for (latency, v) in &latencies {
                    stake_so_far += self.validators[*v as usize].stake;
                    if stake_so_far as f64 > total_stake as f64 * 0.6 {
                        slow_final_latency = *latency;
                        break;
                    }
                }
                slow_final_latency = slow_final_latency.max(*v1_notar_latency);
                self.slow_final_latencies[*v1 as usize] = (slow_final_latency, *v1);
            }

            self.direct_stats
                .record_latencies(&mut self.direct_latencies, &self.validators);
            self.rotor_stats
                .record_latencies(&mut self.rotor_latencies, &self.validators);
            self.notar_stats
                .record_latencies(&mut self.notar_latencies, &self.validators);
            self.fast_final_stats
                .record_latencies(&mut self.fast_final_latencies, &self.validators);
            self.slow_final_stats
                .record_latencies(&mut self.slow_final_latencies, &self.validators);
        }
        println!(
            "{},{},{},{},{},{},{}",
            self.num_shreds,
            self.direct_stats.max_latency,
            self.direct_stats.p60_latency,
            self.direct_stats.p80_latency,
            self.rotor_stats.max_latency,
            self.rotor_stats.p60_latency,
            self.rotor_stats.p80_latency
        );
        // info!("[{k} Shreds] Direct:");
        // direct_stats.print();
        // info!("[{k} Shreds] Rotor:");
        // rotor_stats.print();
        // info!("[{k} Shreds] Notarization:");
        // notar_stats.print();
        // info!("[{k} Shreds] Fast-Finalization:");
        // fast_final_stats.print();
        // info!("[{k} Shreds] Slow-Finalization:");
        // slow_final_stats.print();
    }
}

fn rotor_sampling_test(
    validators: Vec<ValidatorInfo>,
    sampler: impl SamplingStrategy,
    num_shreds: usize,
) {
    let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
    let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
    let mut validators_to_corrupt = validators.clone();
    let mut tests = 0;
    let mut failures = 0;
    'outer: for _ in 0..10_000 {
        // greedily corrupt less than 40% of validators
        let mut corrupted = HashSet::new();
        let mut corrupted_stake = 0.0;
        validators_to_corrupt.shuffle(&mut rng);

        for v in &validators_to_corrupt {
            let rel_stake = v.stake as f64 / total_stake as f64;
            if corrupted_stake + rel_stake < 0.4 {
                corrupted.insert(v.id);
                corrupted_stake += rel_stake;
            }
        }

        for _ in 0..10_000 {
            let sampled = sampler.sample_multiple(num_shreds, &mut rng);
            let mut corrupted_samples = 0;
            for v in sampled {
                if corrupted.contains(&v.id) {
                    corrupted_samples += 1;
                }
            }
            tests += 1;
            if corrupted_samples > num_shreds - 32 {
                failures += 1;
                if failures >= 3 {
                    break 'outer;
                }
            }
        }
    }
    info!(
        "{:<3} shreds, failures [log2]: {:.3}",
        num_shreds,
        (failures as f64 / tests as f64).log2()
    );
}
