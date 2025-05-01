// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for Rotor and Alpenglow.
//!
//!

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use log::info;
use rand::prelude::*;

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
    direct_stats: LatencyStats,
    rotor_stats: LatencyStats,
    notar_stats: LatencyStats,
    fast_final_stats: LatencyStats,
    slow_final_stats: LatencyStats,
    final_stats: LatencyStats,

    // temporary storage used during one iteration
    relay_latencies: Vec<f64>,
    direct_latencies: Vec<(f64, ValidatorId)>,
    rotor_latencies: Vec<(f64, ValidatorId)>,
    notar_latencies: Vec<(f64, ValidatorId)>,
    fast_final_latencies: Vec<(f64, ValidatorId)>,
    slow_final_latencies: Vec<(f64, ValidatorId)>,
    final_latencies: Vec<(f64, ValidatorId)>,
    tmp_rotor_latencies: Vec<f64>,
    tmp_latencies: Vec<(f64, ValidatorId)>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencyTest<L, R> {
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
        let num_val = validators.len();
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        Self {
            validators,
            ping_servers,
            leader_sampler,
            rotor_sampler,
            num_data_shreds,
            num_shreds,
            total_stake,

            direct_stats: LatencyStats::new(),
            rotor_stats: LatencyStats::new(),
            notar_stats: LatencyStats::new(),
            fast_final_stats: LatencyStats::new(),
            slow_final_stats: LatencyStats::new(),
            final_stats: LatencyStats::new(),

            relay_latencies: vec![0.0; num_shreds],
            direct_latencies: vec![(0.0, 0); num_val],
            rotor_latencies: vec![(0.0, 0); num_val],
            notar_latencies: vec![(0.0, 0); num_val],
            fast_final_latencies: vec![(0.0, 0); num_val],
            slow_final_latencies: vec![(0.0, 0); num_val],
            final_latencies: vec![(0.0, 0); num_val],
            tmp_rotor_latencies: vec![0.0; num_shreds],
            tmp_latencies: vec![(0.0, 0); num_val],
        }
    }

    /// Runs the latency simulation `iterations` times.
    ///
    /// In each iteration, a new leader and new relays are randomly selected.
    /// Each iteration runs only until `up_to_stage`, e.g., if `up_to_stage` is
    /// `LatencyTestStage::Direct`, only the direct latency will be measured.
    pub fn run_many(&mut self, test_name: &str, iterations: usize, up_to_stage: LatencyTestStage) {
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
        for _ in 0..iterations {
            self.run_one(up_to_stage, &mut rng);
        }
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
        &mut self,
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
    pub fn run_one(&mut self, up_to_stage: LatencyTestStage, rng: &mut impl Rng) {
        // sample leader and relays
        let leader = self.leader_sampler.sample(rng);
        let relays = self.rotor_sampler.sample_multiple(self.num_shreds, rng);
        self.run_one_deterministic(up_to_stage, leader.clone(), relays);
    }

    /// Runs one iteration of the latency simulation with given leader and relays.
    pub fn run_one_deterministic(
        &mut self,
        up_to_stage: LatencyTestStage,
        leader: ValidatorId,
        relays: Vec<ValidatorId>,
    ) {
        // measure direct latencies
        for v in &self.validators {
            let leader_ping_server = self.ping_servers[leader as usize].id;
            let v_ping_server = self.ping_servers[v.id as usize].id;
            let latency = get_ping(leader_ping_server, v_ping_server).unwrap();
            self.direct_latencies[v.id as usize] = (latency, v.id);
        }
        for (i, relay) in relays.iter().enumerate() {
            self.relay_latencies[i] = self.direct_latencies[*relay as usize].0;
        }

        if up_to_stage == LatencyTestStage::Direct {
            return;
        }

        // measure Rotor block dissemination latencies
        for v in &self.validators {
            for (i, (relay, latency)) in relays.iter().zip(self.relay_latencies.iter()).enumerate()
            {
                let relay_ping_server = self.ping_servers[*relay as usize].id;
                let v_ping_server = self.ping_servers[v.id as usize].id;
                let latency = latency + get_ping(relay_ping_server, v_ping_server).unwrap();
                self.tmp_rotor_latencies[i] = latency;
            }
            self.tmp_rotor_latencies
                .sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
            let threshold_latency = self.tmp_rotor_latencies[self.num_data_shreds - 1];
            self.rotor_latencies[v.id as usize] = (threshold_latency, v.id);
        }

        if up_to_stage == LatencyTestStage::Rotor {
            return;
        }

        // simulate notar vote propagation
        for (v1_rotor_latency, v1) in &self.rotor_latencies {
            for (v2_rotor_latency, v2) in &self.rotor_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency = v2_rotor_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                self.tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            self.tmp_latencies
                .sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());

            // measure latency until notarization and fast-finalization
            let mut notar_latency = None;
            let mut fast_final_latency = None;
            let mut stake_so_far = 0;
            for (latency, v) in &self.tmp_latencies {
                stake_so_far += self.validators[*v as usize].stake;
                if notar_latency.is_none() && stake_so_far as f64 > self.total_stake as f64 * 0.6 {
                    notar_latency = Some(*latency);
                }
                if stake_so_far as f64 > self.total_stake as f64 * 0.8 {
                    fast_final_latency = Some(*latency);
                    break;
                }
            }
            let mut notar_latency = notar_latency.unwrap();
            let mut fast_final_latency = fast_final_latency.unwrap();
            notar_latency = notar_latency.max(*v1_rotor_latency);
            self.notar_latencies[*v1 as usize] = (notar_latency, *v1);
            fast_final_latency = fast_final_latency.max(*v1_rotor_latency);
            self.fast_final_latencies[*v1 as usize] = (fast_final_latency, *v1);
            self.final_latencies[*v1 as usize] = (fast_final_latency, *v1);
        }

        // simulate notar cert propagation
        for (v1_rotor_latency, v1) in &self.rotor_latencies {
            for (v2_notar_latency, v2) in &self.notar_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency = v2_notar_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                self.tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            let mut notar_cert_latency = self
                .tmp_latencies
                .iter()
                .map(|(l, _)| *l)
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();
            notar_cert_latency = notar_cert_latency.max(*v1_rotor_latency);
            if notar_cert_latency < self.notar_latencies[*v1 as usize].0 {
                self.notar_latencies[*v1 as usize] = (notar_cert_latency, *v1);
            }
        }

        // simulate fast-final cert propagation
        for (v1_rotor_latency, v1) in &self.rotor_latencies {
            for (v2_fast_final_latency, v2) in &self.fast_final_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency =
                    v2_fast_final_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                self.tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            let mut fast_final_cert_latency = self
                .tmp_latencies
                .iter()
                .map(|(l, _)| *l)
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();
            fast_final_cert_latency = fast_final_cert_latency.max(*v1_rotor_latency);
            if fast_final_cert_latency < self.fast_final_latencies[*v1 as usize].0 {
                self.fast_final_latencies[*v1 as usize] = (fast_final_cert_latency, *v1);
                self.final_latencies[*v1 as usize] = (fast_final_cert_latency, *v1);
            }
        }

        if up_to_stage == LatencyTestStage::Notar {
            return;
        }

        // measure latency until (slow) finalization
        for (v1_notar_latency, v1) in &self.notar_latencies {
            for (v2_notar_latency, v2) in &self.notar_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency = v2_notar_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                self.tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            self.tmp_latencies
                .sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
            let mut slow_final_latency: f64 = 0.0;
            let mut stake_so_far = 0;
            for (latency, v) in &self.tmp_latencies {
                stake_so_far += self.validators[*v as usize].stake;
                if stake_so_far as f64 > self.total_stake as f64 * 0.6 {
                    slow_final_latency = *latency;
                    break;
                }
            }
            slow_final_latency = slow_final_latency.max(*v1_notar_latency);
            self.slow_final_latencies[*v1 as usize] = (slow_final_latency, *v1);
            if slow_final_latency < self.final_latencies[*v1 as usize].0 {
                self.final_latencies[*v1 as usize] = (slow_final_latency, *v1);
            }
        }

        // simulate (slow) final cert propagation
        for (v1_rotor_latency, v1) in &self.notar_latencies {
            for (v2_slow_final_latency, v2) in &self.slow_final_latencies {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;
                let latency =
                    v2_slow_final_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                self.tmp_latencies[*v2 as usize] = (latency, *v2);
            }
            let mut slow_final_cert_latency = self
                .tmp_latencies
                .iter()
                .map(|(l, _)| *l)
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();
            slow_final_cert_latency = slow_final_cert_latency.max(*v1_rotor_latency);
            if slow_final_cert_latency < self.slow_final_latencies[*v1 as usize].0 {
                self.slow_final_latencies[*v1 as usize] = (slow_final_cert_latency, *v1);
                if slow_final_cert_latency < self.final_latencies[*v1 as usize].0 {
                    self.final_latencies[*v1 as usize] = (slow_final_cert_latency, *v1);
                }
            }
        }

        self.direct_stats.record_latencies(
            &mut self.direct_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.rotor_stats.record_latencies(
            &mut self.rotor_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.notar_stats.record_latencies(
            &mut self.notar_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.fast_final_stats.record_latencies(
            &mut self.fast_final_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.slow_final_stats.record_latencies(
            &mut self.slow_final_latencies,
            &self.validators,
            &self.ping_servers,
        );
        self.final_stats.record_latencies(
            &mut self.final_latencies,
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
            "percentile,direct,rotor,notar,fast_final,slow_final,final"
        )
        .unwrap();
        for percentile in 1..=100 {
            let direct_latency = self.direct_stats.get_avg_percentile_latency(percentile);
            let rotor_latency = self.rotor_stats.get_avg_percentile_latency(percentile);
            let notar_latency = self.notar_stats.get_avg_percentile_latency(percentile);
            let fast_final_latency = self.fast_final_stats.get_avg_percentile_latency(percentile);
            let slow_final_latency = self.slow_final_stats.get_avg_percentile_latency(percentile);
            let final_latency = self.final_stats.get_avg_percentile_latency(percentile);
            writeln!(
                writer,
                "{},{},{},{},{},{},{}",
                percentile,
                direct_latency,
                rotor_latency,
                notar_latency,
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

    fn print(&self) {
        let avg_p60_latency = self.get_avg_percentile_latency(60);
        info!("avg p60 latency: {:.2}", avg_p60_latency);
        let avg_p80_latency = self.get_avg_percentile_latency(80);
        info!("avg p80 latency: {:.2}", avg_p80_latency);
        let avg_max_latency = self.get_avg_percentile_latency(100);
        info!("avg max latency: {:.2}", avg_max_latency);

        for percentile in 1..=100 {
            println!("percentile: {percentile}");
            let total_count: f64 = self.percentile_location[percentile - 1].values().sum();
            for (location, count) in &self.percentile_location[percentile - 1] {
                let frac = *count * 100.0 / total_count;
                println!("    location: {}, frac: {:.2}%", location, frac);
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
