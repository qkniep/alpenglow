// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! General discrete-event simulator.

// mod event;
// mod resources;
// mod simulator;
//
// pub use event::{Event, EventStats};
// pub use resources::Resources;
// pub use simulator::Simulator;

use std::collections::HashMap;
use std::fs::File;
use std::hash::Hash;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::RwLock;

use alpenglow::network::simulated::ping_data::PingServer;
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use log::info;

///
pub enum EventKind {
    Simple,
    Broadcast,
    Compute,
    SubProtocol,
}

///
pub struct SimulationEnvironment {
    // core setup of the latency test
    pub validators: Vec<ValidatorInfo>,
    pub ping_servers: Vec<&'static PingServer>,
    pub total_stake: Stake,

    // optional bandwidth information
    // if provided, these will be used to simulate transmission delays
    // otherwise, transmission delay is ignored
    leader_bandwidth: Option<u64>,
    bandwidths: Option<Vec<u64>>,
}

impl SimulationEnvironment {
    pub fn new(
        validators: Vec<ValidatorInfo>,
        ping_servers: Vec<&'static PingServer>,
        total_stake: Stake,
    ) -> Self {
        Self {
            validators,
            ping_servers,
            total_stake,
            leader_bandwidth: None,
            bandwidths: None,
        }
    }

    /// Sets the bandwidths for all validators for simulating transmission delays.
    pub fn with_bandwidths(mut self, leader_bandwidth: u64, bandwidths: Vec<u64>) -> Self {
        self.leader_bandwidth = Some(leader_bandwidth);
        self.bandwidths = Some(bandwidths);
        self
    }

    ///
    pub fn num_validators(&self) -> usize {
        self.validators.len()
    }

    ///
    pub fn time_to_send_message(&self, bytes: usize, validator: ValidatorId) -> f64 {
        let Some(bandwidths) = &self.bandwidths else {
            return 0.0;
        };
        (bytes * 8) as f64 / bandwidths[validator as usize] as f64
    }
}

pub type TimingVec = Vec<(f64, ValidatorId)>;

pub struct Timings<E: PartialEq + Eq + Hash>(HashMap<E, RwLock<TimingVec>>);

impl<E: PartialEq + Eq + Hash> Timings<E> {
    // fn initialize(&mut self, stage: LatencyTestStage, num_val: usize) {
    //     for event in stage.events() {
    //         self.0
    //             .insert(event, RwLock::new(vec![(f64::INFINITY, 0); num_val]));
    //     }
    // }
    pub fn initialize(&mut self, event: E, num_val: usize) {
        self.0
            .insert(event, RwLock::new(vec![(f64::INFINITY, 0); num_val]));
    }

    pub fn record(&self, event: E, latency: f64, validator: ValidatorId) {
        let mut vec = self.0.get(&event).unwrap().write().unwrap();
        let entry = vec.get_mut(validator as usize).unwrap();
        if latency < entry.0 {
            *entry = (latency, validator);
        }
    }

    pub fn get(&self, event: E) -> Option<std::sync::RwLockReadGuard<'_, TimingVec>> {
        self.0.get(&event).map(|v| v.read().unwrap())
    }

    pub fn get_one(&self, event: E, validator: ValidatorId) -> f64 {
        let (latency, _val) = self.get(event).unwrap()[validator as usize];
        latency
    }

    pub fn iter(&self) -> impl Iterator<Item = (&E, &RwLock<TimingVec>)> {
        self.0.iter()
    }
}

impl<E: PartialEq + Eq + Hash> Default for Timings<E> {
    fn default() -> Self {
        Self(HashMap::new())
    }
}

pub struct TimingStats<E: Clone + Copy + Eq + Hash>(HashMap<E, EventTimingStats>);

impl<E: Clone + Copy + Eq + Hash> TimingStats<E> {
    pub fn record_latencies(
        &mut self,
        timings: &mut Timings<E>,
        environment: &SimulationEnvironment,
    ) {
        for (event, timing_vec) in timings.iter() {
            self.0.entry(*event).or_default().record_latencies(
                timing_vec,
                &environment.validators,
                &environment.ping_servers,
            );
        }
    }

    /// Writes percentiles to a CSV file.
    pub fn write_to_csv(
        &self,
        filename: impl AsRef<Path>,
        events: &[(&str, E)],
    ) -> std::io::Result<()> {
        let file = File::create(filename)?;
        let mut writer = BufWriter::new(file);

        let columns = events
            .iter()
            .map(|(name, _event)| name.to_string())
            .collect::<Vec<_>>();
        let column_str = columns.join(",");
        writeln!(writer, "percentile,{}", column_str)?;
        for percentile in 1..=100 {
            let event_timings = events
                .iter()
                .map(|(_name, event)| {
                    let event_stats = self.0.get(event).unwrap();
                    event_stats
                        .get_avg_percentile_latency(percentile)
                        .to_string()
                })
                .collect::<Vec<_>>();
            let event_timings_str = event_timings.join(",");
            writeln!(writer, "{percentile},{event_timings_str}")?;
        }

        Ok(())
    }
}

impl<E: Clone + Copy + Eq + Hash> Default for TimingStats<E> {
    fn default() -> Self {
        Self(HashMap::new())
    }
}

pub struct EventTimingStats {
    sum_percentile_latencies: [f64; 100],
    percentile_location: Vec<HashMap<String, f64>>,
    count: u64,
}

impl EventTimingStats {
    pub fn record_latencies(
        &mut self,
        latencies: &RwLock<TimingVec>,
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
        // assert!((stake_so_far - total_stake as f64).abs() < 5000.0);
        // assert!(percentile >= 100);
        self.count += 1;
    }

    pub fn get_avg_percentile_latency(&self, percentile: u8) -> f64 {
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

impl Default for EventTimingStats {
    fn default() -> Self {
        Self {
            sum_percentile_latencies: [0.0; 100],
            percentile_location: vec![HashMap::new(); 100],
            count: 0,
        }
    }
}
