// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for Rotor and Alpenglow.
//!
//!

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::RwLock;

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use log::info;
use rand::prelude::*;
use rayon::prelude::*;

/// The sequential stages of the latency test.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LatencyTestStage {
    Direct,
    Rotor,
    Notar,
    Final,
}

/// Simulated latency test.
pub struct LatencyTest<L: SamplingStrategy, R: SamplingStrategy> {
    // core setup of the latency test
    validators: Vec<ValidatorInfo>,
    ping_servers: Vec<&'static PingServer>,
    leader_sampler: L,
    rotor_sampler: R,
    num_data_shreds: usize,
    num_shreds: usize,
    total_stake: Stake,

    // running aggregates (averages)
    direct_stats: RwLock<LatencyStats>,
    rotor_stats: RwLock<LatencyStats>,
    shreds95_stats: RwLock<LatencyStats>,
    notar_stats: RwLock<LatencyStats>,
    notar65_stats: RwLock<LatencyStats>,
    fast_final_stats: RwLock<LatencyStats>,
    slow_final_stats: RwLock<LatencyStats>,
    final_stats: RwLock<LatencyStats>,
}

impl<L: SamplingStrategy + Sync + Send, R: SamplingStrategy + Sync + Send> LatencyTest<L, R> {
    /// Creates a new latency test instance.
    ///
    /// Caller needs to make sure that `leader_sampler` and `rotor_smapler`
    /// operate on the correct set of validators.
    pub fn new(
        validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
        leader_sampler: L,
        rotor_sampler: R,
        num_data_shreds: usize,
        num_shreds: usize,
    ) -> Self {
        let validators: Vec<ValidatorInfo> = validators_with_ping_data
            .iter()
            .map(|(v, _)| v.clone())
            .collect();
        let ping_servers: Vec<&'static PingServer> =
            validators_with_ping_data.iter().map(|(_, p)| *p).collect();
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        Self {
            validators,
            ping_servers,
            leader_sampler,
            rotor_sampler,
            num_data_shreds,
            num_shreds,
            total_stake,

            direct_stats: RwLock::new(LatencyStats::new()),
            rotor_stats: RwLock::new(LatencyStats::new()),
            shreds95_stats: RwLock::new(LatencyStats::new()),
            notar_stats: RwLock::new(LatencyStats::new()),
            notar65_stats: RwLock::new(LatencyStats::new()),
            fast_final_stats: RwLock::new(LatencyStats::new()),
            slow_final_stats: RwLock::new(LatencyStats::new()),
            final_stats: RwLock::new(LatencyStats::new()),
        }
    }

    /// Runs the latency simulation `iterations` times.
    ///
    /// In each iteration, a new leader and new relays are randomly selected.
    /// Each iteration runs only until `up_to_stage`, e.g., if `up_to_stage` is
    /// `LatencyTestStage::Direct`, only the direct latency will be measured.
    pub fn run_many(&self, test_name: &str, iterations: usize, up_to_stage: LatencyTestStage) {
        (0..iterations).into_par_iter().for_each(|_| {
            let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
            self.run_one(up_to_stage, &mut rng);
        });
        let path = Path::new("data")
            .join("output")
            .join("simulations")
            .join("latency")
            .join(test_name)
            .with_extension("csv");
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        self.write_to_csv(path);
    }

    /// Runs the latency simulation `iterations` times.
    ///
    /// In each iteration, a new leader and new relays are randomly selected.
    /// Each iteration runs only until `up_to_stage`, e.g., if `up_to_stage` is
    /// `LatencyTestStage::Direct`, only the direct latency will be measured.
    pub fn run_many_with_leader(
        &self,
        test_name: &str,
        iterations: usize,
        up_to_stage: LatencyTestStage,
        leader: ValidatorInfo,
    ) {
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
        for _ in 0..iterations {
            let relays = self
                .rotor_sampler
                .sample_multiple(self.num_shreds, &mut rng);
            self.run_one_deterministic(up_to_stage, leader.id, relays);
        }

        let leader_ping_server = self.ping_servers[leader.id as usize];
        let path = Path::new("data")
            .join("output")
            .join("simulations")
            .join("latency")
            .join(&leader_ping_server.location)
            .join(test_name)
            .with_extension("csv");
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        self.write_to_csv(path);
    }

    /// Runs one iteration of the latency simulation with random leader and relays.
    pub fn run_one(&self, up_to_stage: LatencyTestStage, rng: &mut impl Rng) {
        // sample leader and relays
        let leader = self.leader_sampler.sample(rng);
        let relays = self.rotor_sampler.sample_multiple(self.num_shreds, rng);
        self.run_one_deterministic(up_to_stage, leader, relays);
    }

    /// Runs one iteration of the latency simulation with given leader and relays.
    pub fn run_one_deterministic(
        &self,
        up_to_stage: LatencyTestStage,
        leader: ValidatorId,
        relays: Vec<ValidatorId>,
    ) {
        let num_val = self.validators.len();
        let mut relay_latencies = vec![0.0; self.num_shreds];
        let mut direct_latencies = vec![(0.0, 0); num_val];
        let mut rotor_latencies = vec![(0.0, 0); num_val];
        let mut shreds95_latencies = vec![(0.0, 0); num_val];
        let mut notar_latencies = vec![(0.0, 0); num_val];
        let mut notar65_latencies = vec![(0.0, 0); num_val];
        let mut fast_final_latencies = vec![(0.0, 0); num_val];
        let mut slow_final_latencies = vec![(0.0, 0); num_val];
        let mut final_latencies = vec![(0.0, 0); num_val];
        let mut tmp_rotor_latencies = vec![0.0; self.num_shreds];
        let mut tmp_latencies = vec![(0.0, 0); num_val];

        // measure direct latencies
        for v in &self.validators {
            let leader_ping_server = self.ping_servers[leader as usize].id;
            let v_ping_server = self.ping_servers[v.id as usize].id;
            let latency = get_ping(leader_ping_server, v_ping_server).unwrap();
            direct_latencies[v.id as usize] = (latency, v.id);
        }
        for (i, relay) in relays.iter().enumerate() {
            relay_latencies[i] = direct_latencies[*relay as usize].0;
        }

        if up_to_stage == LatencyTestStage::Direct {
            return;
        }

        // measure Rotor block dissemination latencies
        for v in &self.validators {
            for (i, (relay, latency)) in relays.iter().zip(relay_latencies.iter()).enumerate() {
                let relay_ping_server = self.ping_servers[*relay as usize].id;
                let v_ping_server = self.ping_servers[v.id as usize].id;
                let latency = latency + get_ping(relay_ping_server, v_ping_server).unwrap();
                tmp_rotor_latencies[i] = latency;
            }
            tmp_rotor_latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
            let threshold_latency = tmp_rotor_latencies[self.num_data_shreds - 1];
            rotor_latencies[v.id as usize] = (threshold_latency, v.id);
            let threshold_latency = tmp_rotor_latencies[61 - 1];
            shreds95_latencies[v.id as usize] = (threshold_latency, v.id);
        }

        if up_to_stage == LatencyTestStage::Rotor {
            return;
        }

        // simulate notar vote propagation
        for (v1_rotor_latency, v1) in &rotor_latencies {
            for (v2_rotor_latency, v2) in &rotor_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency = v2_rotor_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            tmp_latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());

            // measure latency until notarization and fast-finalization
            let mut notar_latency = None;
            let mut notar65_latency = None;
            let mut fast_final_latency = None;
            let mut stake_so_far = 0;
            for (latency, v) in &tmp_latencies {
                stake_so_far += self.validators[*v as usize].stake;
                if notar_latency.is_none() && stake_so_far as f64 > self.total_stake as f64 * 0.6 {
                    notar_latency = Some(*latency);
                }
                if notar65_latency.is_none() && stake_so_far as f64 > self.total_stake as f64 * 0.65
                {
                    notar65_latency = Some(*latency);
                }
                if stake_so_far as f64 > self.total_stake as f64 * 0.8 {
                    fast_final_latency = Some(*latency);
                    break;
                }
            }
            let mut notar_latency = notar_latency.unwrap();
            let notar65_latency = notar65_latency.unwrap();
            let mut fast_final_latency = fast_final_latency.unwrap();
            notar_latency = notar_latency.max(*v1_rotor_latency);
            notar_latencies[*v1 as usize] = (notar_latency, *v1);
            notar65_latencies[*v1 as usize] = (notar65_latency, *v1);
            fast_final_latency = fast_final_latency.max(*v1_rotor_latency);
            fast_final_latencies[*v1 as usize] = (fast_final_latency, *v1);
            final_latencies[*v1 as usize] = (fast_final_latency, *v1);
        }

        // simulate notar cert propagation
        for (v1_rotor_latency, v1) in &rotor_latencies {
            for (v2_notar_latency, v2) in &notar_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency = v2_notar_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            let mut notar_cert_latency = tmp_latencies
                .iter()
                .map(|(l, _)| *l)
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();
            notar_cert_latency = notar_cert_latency.max(*v1_rotor_latency);
            if notar_cert_latency < notar_latencies[*v1 as usize].0 {
                notar_latencies[*v1 as usize] = (notar_cert_latency, *v1);
            }
        }

        // simulate fast-final cert propagation
        for (v1_rotor_latency, v1) in &rotor_latencies {
            for (v2_fast_final_latency, v2) in &fast_final_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency =
                    v2_fast_final_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            let mut fast_final_cert_latency = tmp_latencies
                .iter()
                .map(|(l, _)| *l)
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();
            fast_final_cert_latency = fast_final_cert_latency.max(*v1_rotor_latency);
            if fast_final_cert_latency < fast_final_latencies[*v1 as usize].0 {
                fast_final_latencies[*v1 as usize] = (fast_final_cert_latency, *v1);
                final_latencies[*v1 as usize] = (fast_final_cert_latency, *v1);
            }
        }

        if up_to_stage == LatencyTestStage::Notar {
            return;
        }

        // measure latency until (slow) finalization
        for (v1_notar_latency, v1) in &notar_latencies {
            for (v2_notar_latency, v2) in &notar_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency = v2_notar_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            tmp_latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
            let mut slow_final_latency: f64 = 0.0;
            let mut stake_so_far = 0;
            for (latency, v) in &tmp_latencies {
                stake_so_far += self.validators[*v as usize].stake;
                if stake_so_far as f64 > self.total_stake as f64 * 0.6 {
                    slow_final_latency = *latency;
                    break;
                }
            }
            slow_final_latency = slow_final_latency.max(*v1_notar_latency);
            slow_final_latencies[*v1 as usize] = (slow_final_latency, *v1);
            if slow_final_latency < final_latencies[*v1 as usize].0 {
                final_latencies[*v1 as usize] = (slow_final_latency, *v1);
            }
        }

        // simulate (slow) final cert propagation
        for (v1_rotor_latency, v1) in &notar_latencies {
            for (v2_slow_final_latency, v2) in &slow_final_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency =
                    v2_slow_final_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            let mut slow_final_cert_latency = tmp_latencies
                .iter()
                .map(|(l, _)| *l)
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();
            slow_final_cert_latency = slow_final_cert_latency.max(*v1_rotor_latency);
            if slow_final_cert_latency < slow_final_latencies[*v1 as usize].0 {
                slow_final_latencies[*v1 as usize] = (slow_final_cert_latency, *v1);
                if slow_final_cert_latency < final_latencies[*v1 as usize].0 {
                    final_latencies[*v1 as usize] = (slow_final_cert_latency, *v1);
                }
            }
        }

        self.direct_stats.write().unwrap().record_latencies(
            &mut direct_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.rotor_stats.write().unwrap().record_latencies(
            &mut rotor_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.shreds95_stats.write().unwrap().record_latencies(
            &mut shreds95_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.notar_stats.write().unwrap().record_latencies(
            &mut notar_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.notar65_stats.write().unwrap().record_latencies(
            &mut notar65_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.fast_final_stats.write().unwrap().record_latencies(
            &mut fast_final_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.slow_final_stats.write().unwrap().record_latencies(
            &mut slow_final_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.final_stats.write().unwrap().record_latencies(
            &mut final_latencies,
            &self.validators,
            &self.ping_servers,
        );
    }

    /// Writes latency test results to a CSV file.
    // TODO: return io::Result
    pub fn write_to_csv(&self, filename: impl AsRef<Path>) {
        let file = File::create(filename).unwrap();
        let mut writer = BufWriter::new(file);

        writeln!(
            writer,
            "percentile,direct,rotor,shreds95,notar,notar65,fast_final,slow_final,final"
        )
        .unwrap();
        for percentile in 1..=100 {
            let direct_stats = self.direct_stats.read().unwrap();
            let direct_latency = direct_stats.get_avg_percentile_latency(percentile);

            let rotor_stats = self.rotor_stats.read().unwrap();
            let rotor_latency = rotor_stats.get_avg_percentile_latency(percentile);

            let shreds95_stats = self.shreds95_stats.read().unwrap();
            let shreds95_latency = shreds95_stats.get_avg_percentile_latency(percentile);

            let notar_stats = self.notar_stats.read().unwrap();
            let notar_latency = notar_stats.get_avg_percentile_latency(percentile);

            let notar65_stats = self.notar65_stats.read().unwrap();
            let notar65_latency = notar65_stats.get_avg_percentile_latency(percentile);

            let fast_final_stats = self.fast_final_stats.read().unwrap();
            let fast_final_latency = fast_final_stats.get_avg_percentile_latency(percentile);

            let slow_final_stats = self.slow_final_stats.read().unwrap();
            let slow_final_latency = slow_final_stats.get_avg_percentile_latency(percentile);

            let final_stats = self.final_stats.read().unwrap();
            let final_latency = final_stats.get_avg_percentile_latency(percentile);

            writeln!(
                writer,
                "{},{},{},{},{},{},{},{},{}",
                percentile,
                direct_latency,
                rotor_latency,
                shreds95_latency,
                notar_latency,
                notar65_latency,
                fast_final_latency,
                slow_final_latency,
                final_latency,
            )
            .unwrap();
        }
    }
}

struct LatencyStats {
    sum_percentile_latencies: [f64; 100],
    percentile_location: Vec<HashMap<String, f64>>,
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
        ping_servers: &[&'static PingServer],
    ) {
        latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let percentile_stake = total_stake as f64 / 100.0;
        let mut percentile = 1;
        let mut stake_so_far = 0.0;
        for (latency, v) in &*latencies {
            let mut validator_stake = validators[*v as usize].stake as f64;
            for _ in 0..100 {
                let percentile_stake_left = percentile as f64 * percentile_stake - stake_so_far;
                let abs_stake_contrib = validator_stake.min(percentile_stake_left);
                let rel_stake_contrib = abs_stake_contrib / percentile_stake;
                let latency_contrib = rel_stake_contrib * *latency;
                self.sum_percentile_latencies[percentile as usize - 1] += latency_contrib;
                let count = self.percentile_location[percentile as usize - 1]
                    .entry(ping_servers[*v as usize].location.clone())
                    .or_default();
                *count += abs_stake_contrib;
                stake_so_far += abs_stake_contrib;
                validator_stake -= abs_stake_contrib;
                if percentile < 100 && stake_so_far >= percentile as f64 * percentile_stake {
                    percentile += 1;
                } else {
                    break;
                }
            }
        }
        assert!((stake_so_far - total_stake as f64).abs() < 5000.0);
        assert!(percentile >= 100);
        self.count += 1;
    }

    fn get_avg_percentile_latency(&self, percentile: u8) -> f64 {
        assert!(percentile > 0 && percentile <= 100);
        let sum = self.sum_percentile_latencies[percentile as usize - 1];
        sum / self.count as f64
    }

    fn _print(&self) {
        let avg_p60_latency = self.get_avg_percentile_latency(60);
        info!("avg p60 latency: {avg_p60_latency:.2}");
        let avg_p80_latency = self.get_avg_percentile_latency(80);
        info!("avg p80 latency: {avg_p80_latency:.2}");
        let avg_max_latency = self.get_avg_percentile_latency(100);
        info!("avg max latency: {avg_max_latency:.2}");

        for percentile in 1..=100 {
            println!("percentile: {percentile}");
            let total_count: f64 = self.percentile_location[percentile - 1].values().sum();
            for (location, count) in &self.percentile_location[percentile - 1] {
                let frac = *count * 100.0 / total_count;
                println!("    location: {location}, frac: {frac:.2}%");
            }
        }
    }
}

impl Default for LatencyStats {
    fn default() -> Self {
        Self {
            sum_percentile_latencies: [0.0; 100],
            percentile_location: vec![HashMap::new(); 100],
            count: 0,
        }
    }
}
