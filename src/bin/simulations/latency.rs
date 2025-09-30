// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for the Alpenglow protocol.
//!
//! So far, this test can only simulate the good case.

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::RwLock;

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::shredder::MAX_DATA_PER_SHRED;
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use log::info;
use rand::prelude::*;
use rayon::prelude::*;

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;

/// The sequential stages of the latency test.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LatencyTestStage {
    Rotor,
    Notar,
    Final,
}

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Direct(usize),
    Rotor(usize),
    Shreds95,
    Notar,
    Notar65,
    FastFinal,
    SlowFinal,
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
    num_slices: usize,
    total_stake: Stake,

    // optional bandwidth information
    // if provided, these will be used to simulate transmission delays
    // otherwise, transmission delay is ignored
    leader_bandwidth: Option<u64>,
    bandwidths: Option<Vec<u64>>,

    // running aggregates (averages)
    stats: RwLock<LatencyStats>,
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
            num_slices: 1,
            total_stake,

            leader_bandwidth: None,
            bandwidths: None,

            stats: RwLock::new(LatencyStats::default()),
        }
    }

    /// Sets the bandwidths for all validators for simulating transmission delays.
    pub fn with_bandwidths(mut self, leader_bandwidth: u64, bandwidths: Vec<u64>) -> Self {
        self.leader_bandwidth = Some(leader_bandwidth);
        self.bandwidths = Some(bandwidths);
        self
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
        self.stats.read().unwrap().write_to_csv(path).unwrap();
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
            let relays = (0..self.num_slices)
                .map(|_| {
                    self.rotor_sampler
                        .sample_multiple(self.num_shreds, &mut rng)
                })
                .collect::<Vec<_>>();
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
        self.stats.read().unwrap().write_to_csv(path).unwrap();
    }

    /// Runs one iteration of the latency simulation with random leader and relays.
    pub fn run_one(&self, up_to_stage: LatencyTestStage, rng: &mut impl Rng) {
        // sample leader and relays
        let leader = self.leader_sampler.sample(rng);
        let relays = (0..self.num_slices)
            .map(|_| self.rotor_sampler.sample_multiple(self.num_shreds, rng))
            .collect::<Vec<_>>();
        self.run_one_deterministic(up_to_stage, leader, relays);
    }

    /// Runs one iteration of the latency simulation with given leader and relays.
    pub fn run_one_deterministic(
        &self,
        up_to_stage: LatencyTestStage,
        leader: ValidatorId,
        relays: Vec<Vec<ValidatorId>>,
    ) {
        // setup & initialization
        let num_val = self.validators.len();
        let mut relay_latencies = vec![0.0; self.num_shreds];
        let mut latencies = Latencies::default();
        // TODO: automatically initialize
        for slice in 0..self.num_slices {
            let event = LatencyEvent::Direct(slice);
            latencies
                .0
                .insert(event, RwLock::new(vec![(f64::INFINITY, 0); num_val]));
        }
        for slice in 0..self.num_slices {
            let event = LatencyEvent::Rotor(slice);
            latencies
                .0
                .insert(event, RwLock::new(vec![(f64::INFINITY, 0); num_val]));
        }
        for event in [
            LatencyEvent::Shreds95,
            LatencyEvent::Notar,
            LatencyEvent::Notar65,
            LatencyEvent::FastFinal,
            LatencyEvent::SlowFinal,
            LatencyEvent::Final,
        ] {
            latencies
                .0
                .insert(event, RwLock::new(vec![(f64::INFINITY, 0); num_val]));
        }
        let mut tmp_rotor_latencies = vec![0.0; self.num_shreds];
        let mut tmp_latencies = vec![(0.0, 0); num_val];
        let mut tmp_transmission_latencies = vec![0.0; num_val];

        for (slice, relays) in relays.iter().enumerate() {
            // measure direct latencies from leader to everyone
            for v in &self.validators {
                let leader_ping_server = self.ping_servers[leader as usize].id;
                let v_ping_server = self.ping_servers[v.id as usize].id;

                let start_time = tmp_transmission_latencies[leader as usize];
                let propagation_delay = get_ping(leader_ping_server, v_ping_server).unwrap();
                let transmission_delay =
                    self.time_to_send_message(MAX_DATA_PER_SHRED * v.id as usize, v.id);
                let latency = start_time + propagation_delay + transmission_delay;
                latencies.record(LatencyEvent::Direct(slice), latency, v.id);
            }
            let total_transmission_delay =
                self.time_to_send_message(MAX_DATA_PER_SHRED * num_val, leader);
            tmp_transmission_latencies[leader as usize] += total_transmission_delay;
            for (i, relay) in relays.iter().enumerate() {
                relay_latencies[i] = latencies.get_one(LatencyEvent::Direct(slice), *relay);
            }

            // measure Rotor block dissemination latencies
            for v in &self.validators {
                for (i, (relay, latency)) in relays.iter().zip(relay_latencies.iter()).enumerate() {
                    let relay_ping_server = self.ping_servers[*relay as usize].id;
                    let v_ping_server = self.ping_servers[v.id as usize].id;

                    let start_time = tmp_transmission_latencies[*relay as usize].max(*latency);
                    if slice == 0 {
                        tmp_transmission_latencies[*relay as usize] = start_time;
                    }
                    let propagation_delay = get_ping(relay_ping_server, v_ping_server).unwrap();
                    let transmission_delay = self.time_to_send_message(MAX_DATA_PER_SHRED, *relay);
                    tmp_transmission_latencies[*relay as usize] += transmission_delay;
                    let latency = start_time + propagation_delay + transmission_delay;
                    tmp_rotor_latencies[i] = latency;
                }
                tmp_rotor_latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let threshold_latency = tmp_rotor_latencies[self.num_data_shreds - 1];
                latencies.record(LatencyEvent::Rotor(slice), threshold_latency, v.id);
                let threshold_latency = tmp_rotor_latencies[61 - 1];
                latencies.record(LatencyEvent::Shreds95, threshold_latency, v.id);
            }
        }

        if up_to_stage == LatencyTestStage::Rotor {
            return;
        }

        // simulate notar vote propagation
        // FIXME: need to use actual slowest slice (which may not generally be the last one)
        let last_slice_event = LatencyEvent::Rotor(self.num_slices - 1);
        for (v1_rotor_latency, v1) in latencies.get(last_slice_event).unwrap().iter() {
            for (v2_rotor_latency, v2) in latencies.get(last_slice_event).unwrap().iter() {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;

                let start_time = tmp_transmission_latencies[*v2 as usize].max(*v2_rotor_latency);
                if *v1 == 0 {
                    tmp_transmission_latencies[*v2 as usize] = start_time;
                }
                let propagation_delay = get_ping(v2_ping_server, v1_ping_server).unwrap();
                let transmission_delay = self.time_to_send_message(VOTE_SIZE, *v2);
                tmp_transmission_latencies[*v2 as usize] += transmission_delay;
                let latency = start_time + propagation_delay + transmission_delay;
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
            latencies.record(LatencyEvent::Notar, notar_latency, *v1);
            latencies.record(LatencyEvent::Notar65, notar65_latency, *v1);
            fast_final_latency = fast_final_latency.max(*v1_rotor_latency);
            latencies.record(LatencyEvent::FastFinal, fast_final_latency, *v1);
            latencies.record(LatencyEvent::Final, fast_final_latency, *v1);
        }

        if up_to_stage == LatencyTestStage::Notar {
            return;
        }

        // measure latency until (slow) finalization
        for (v1_notar_latency, v1) in latencies.get(LatencyEvent::Notar).unwrap().iter() {
            for (v2_notar_latency, v2) in latencies.get(LatencyEvent::Notar).unwrap().iter() {
                let v1_ping_server = self.ping_servers[*v1 as usize].id;
                let v2_ping_server = self.ping_servers[*v2 as usize].id;

                let start_time = tmp_transmission_latencies[*v2 as usize].max(*v2_notar_latency);
                if *v1 == 0 {
                    tmp_transmission_latencies[*v2 as usize] = start_time;
                }
                let propagation_delay = get_ping(v2_ping_server, v1_ping_server).unwrap();
                let transmission_delay = self.time_to_send_message(VOTE_SIZE, *v2);
                tmp_transmission_latencies[*v2 as usize] += transmission_delay;
                let latency = start_time + propagation_delay + transmission_delay;
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
            latencies.record(LatencyEvent::SlowFinal, slow_final_latency, *v1);
            latencies.record(LatencyEvent::Final, slow_final_latency, *v1);
        }

        // commit latencies to stats (update averages)
        let stats_map = &mut self.stats.write().unwrap();
        stats_map.record_latencies(&mut latencies, &self.validators, &self.ping_servers);
    }

    fn time_to_send_message(&self, bytes: usize, validator: ValidatorId) -> f64 {
        let Some(bandwidths) = &self.bandwidths else {
            return 0.0;
        };
        (bytes * 8) as f64 / bandwidths[validator as usize] as f64
    }
}

type LatencyVec = Vec<(f64, ValidatorId)>;

#[derive(Default)]
struct Latencies(HashMap<LatencyEvent, RwLock<LatencyVec>>);

impl Latencies {
    fn record(&self, event: LatencyEvent, latency: f64, validator: ValidatorId) {
        let mut vec = self.0.get(&event).unwrap().write().unwrap();
        let entry = vec.get_mut(validator as usize).unwrap();
        if latency < entry.0 {
            *entry = (latency, validator);
        }
    }

    fn get(&self, event: LatencyEvent) -> Option<std::sync::RwLockReadGuard<'_, LatencyVec>> {
        self.0.get(&event).map(|v| v.read().unwrap())
    }

    fn get_one(&self, event: LatencyEvent, validator: ValidatorId) -> f64 {
        let (latency, _val) = self.get(event).unwrap()[validator as usize];
        latency
    }
}

#[derive(Default)]
struct LatencyStats(HashMap<LatencyEvent, EventStats>);

impl LatencyStats {
    fn record_latencies(
        &mut self,
        latencies: &mut Latencies,
        validators: &[ValidatorInfo],
        ping_servers: &[&'static PingServer],
    ) {
        for (event, latencies) in latencies.0.iter() {
            self.0
                .entry(*event)
                .or_default()
                .record_latencies(latencies, validators, ping_servers);
        }
    }

    /// Writes percentiles to a CSV file.
    fn write_to_csv(&self, filename: impl AsRef<Path>) -> std::io::Result<()> {
        let file = File::create(filename)?;
        let mut writer = BufWriter::new(file);

        writeln!(
            writer,
            "percentile,direct,rotor,shreds95,notar,notar65,fast_final,slow_final,final"
        )?;
        for percentile in 1..=100 {
            let direct_stats = self.0.get(&LatencyEvent::Direct(0)).unwrap();
            let direct_latency = direct_stats.get_avg_percentile_latency(percentile);

            let rotor_stats = self.0.get(&LatencyEvent::Rotor(0)).unwrap();
            let rotor_latency = rotor_stats.get_avg_percentile_latency(percentile);

            let shreds95_stats = self.0.get(&LatencyEvent::Shreds95).unwrap();
            let shreds95_latency = shreds95_stats.get_avg_percentile_latency(percentile);

            let notar_stats = self.0.get(&LatencyEvent::Notar).unwrap();
            let notar_latency = notar_stats.get_avg_percentile_latency(percentile);

            let notar65_stats = self.0.get(&LatencyEvent::Notar65).unwrap();
            let notar65_latency = notar65_stats.get_avg_percentile_latency(percentile);

            let fast_final_stats = self.0.get(&LatencyEvent::FastFinal).unwrap();
            let fast_final_latency = fast_final_stats.get_avg_percentile_latency(percentile);

            let slow_final_stats = self.0.get(&LatencyEvent::SlowFinal).unwrap();
            let slow_final_latency = slow_final_stats.get_avg_percentile_latency(percentile);

            let final_stats = self.0.get(&LatencyEvent::Final).unwrap();
            let final_latency = final_stats.get_avg_percentile_latency(percentile);

            writeln!(
                writer,
                "{percentile},{direct_latency},{rotor_latency},{shreds95_latency},{notar_latency},{notar65_latency},{fast_final_latency},{slow_final_latency},{final_latency}",
            )?;
        }

        Ok(())
    }
}

struct EventStats {
    sum_percentile_latencies: [f64; 100],
    percentile_location: Vec<HashMap<String, f64>>,
    count: u64,
}

impl EventStats {
    fn record_latencies(
        &mut self,
        latencies: &RwLock<LatencyVec>,
        validators: &[ValidatorInfo],
        ping_servers: &[&'static PingServer],
    ) {
        let mut latencies = latencies.write().unwrap();
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

impl Default for EventStats {
    fn default() -> Self {
        Self {
            sum_percentile_latencies: [0.0; 100],
            percentile_location: vec![HashMap::new(); 100],
            count: 0,
        }
    }
}
