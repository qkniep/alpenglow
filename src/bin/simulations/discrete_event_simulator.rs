// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! General discrete-event simulator.
//!
//!

mod timings;

use std::sync::RwLock;

use alpenglow::network::simulated::ping_data::PingServer;
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use rayon::prelude::*;

pub use self::timings::{EventTimingStats, TimingStats, Timings};

///
pub trait Event: Sized + Clone + Copy + Eq + std::hash::Hash + Send + Sync {
    /// Return the name of the event.
    fn name(&self) -> &str;

    /// Return a list of dependency event IDs.
    fn dependencies(&self) -> Vec<Self>;

    /// Calculate timing vector given dependencies.
    fn calculate_timing(&self, dep_timings: &[&[f64]]) -> Vec<f64>;
}

///
pub trait Stage: Sized + Clone + Copy + Eq + std::hash::Hash + Send + Sync {
    type Event: Event;

    ///
    fn all() -> Vec<Self> {
        let mut stages = Vec::new();
        let mut stage = Self::first();
        while let Some(s) = stage.next() {
            stages.push(s);
            stage = s;
        }
        stages
    }

    ///
    fn first() -> Self;

    ///
    fn next(&self) -> Option<Self>;

    ///
    fn events(&self) -> Vec<Self::Event>;
}

///
pub enum EventKind {
    Simple,
    Broadcast,
    Compute,
    SubProtocol,
}

/// Matrix-based discrete event simulation engine.
// TODO: maybe generalize into a trait and then implement event queue-based engine as well
pub struct SimulationEngine<S: Stage> {
    environment: SimulationEnvironment,
    stats: RwLock<TimingStats<S::Event>>,
}

impl<S: Stage> SimulationEngine<S> {
    ///
    pub fn new(environment: SimulationEnvironment) -> Self {
        Self {
            environment,
            stats: RwLock::new(TimingStats::default()),
        }
    }

    ///
    pub fn run_many_parallel(&self, iterations: u64) {
        (0..iterations).into_par_iter().for_each(|_| {
            let mut timings = Timings::default();
            self.run(&mut timings);
        });
    }

    ///
    pub fn run_many_sequential(&self, iterations: u64) {
        let mut timings = Timings::default();
        for _ in 0..iterations {
            self.run(&mut timings);
        }
    }

    ///
    pub fn run(&self, timings: &mut Timings<S::Event>) {
        // setup & initialization
        let num_val = self.environment.num_validators();
        timings.clear();

        // simulation loop
        for stage in S::all() {
            for event in stage.events() {
                timings.initialize(event, num_val);
            }

            for event in stage.events() {
                //
            }
        }

        // commit latencies to stats (update averages)
        let mut stats_map = self.stats.write().unwrap();
        stats_map.record_latencies(timings, &self.environment);
    }
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
