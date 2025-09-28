// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! General discrete-event simulator.
//!
//!

mod timings;

use std::hash::Hash;
use std::sync::RwLock;

use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use rayon::prelude::*;

pub use self::timings::{SimTime, TimingStats, Timings};

///
pub trait Protocol {
    type Event: Event;
    type Stage: Stage<Event = Self::Event>;
    type Params: Clone + Send + Sync;
    type Instance: Clone + Send + Sync;
    type Builder: Builder<Params = Self::Params, Instance = Self::Instance>;
}

///
pub trait Builder {
    type Params: Clone + Send + Sync;
    type Instance: Clone + Send + Sync;
}

///
pub trait Event: Sized + Clone + Copy + Eq + Hash + Send + Sync {
    /// Return the name of the event.
    fn name(&self) -> String;

    /// Return `true` iff the event should be tracked for timing stats.
    fn should_track_stats(&self) -> bool;

    /// Return a list of dependency event IDs.
    fn dependencies(&self) -> Vec<Self>;

    /// Calculate timing vector given dependencies.
    fn calculate_timing(
        &self,
        dep_timings: &[&[SimTime]],
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime>;
}

///
pub trait Stage: Sized + Clone + Copy + Eq + Hash + Send + Sync {
    type Event: Event;
    type Params: Clone + Send + Sync;

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
    fn events(&self, params: &Self::Params) -> Vec<Self::Event>;
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
    params: S::Params,
    environment: SimulationEnvironment,
    stats: RwLock<TimingStats<S>>,
}

impl<S: Stage> SimulationEngine<S> {
    ///
    pub fn new(params: S::Params, environment: SimulationEnvironment) -> Self {
        Self {
            params,
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
        let stats_map = self.stats.read().unwrap();
        // TODO: determine correct filename
        stats_map.write_to_csv("test.csv", &self.params);
    }

    ///
    pub fn run_many_sequential(&self, iterations: u64) {
        let mut timings = Timings::default();
        for _ in 0..iterations {
            self.run(&mut timings);
        }
        let stats_map = self.stats.read().unwrap();
        // TODO: determine correct filename
        stats_map.write_to_csv("test.csv", &self.params);
    }

    ///
    pub fn run(&self, timings: &mut Timings<S::Event>) {
        // setup & initialization
        let num_val = self.environment.num_validators();
        timings.clear();

        // simulation loop
        for stage in S::all() {
            for event in stage.events(&self.params) {
                timings.initialize(event, num_val);
            }

            for event in stage.events(&self.params) {
                let dep_timings = event
                    .dependencies()
                    .into_iter()
                    .map(|dep| timings.get(dep).unwrap())
                    .collect::<Vec<_>>();
                let latencies = event.calculate_timing(&dep_timings, &self.environment);
                for (validator, latency) in latencies.iter().enumerate() {
                    timings.record(event, *latency, validator as ValidatorId);
                }
            }
        }

        // commit timings to stats
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
    ///
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
    pub fn transmission_delay(&self, bytes: usize, validator: ValidatorId) -> SimTime {
        let Some(bandwidths) = &self.bandwidths else {
            return SimTime::ZERO;
        };
        let latency = bytes as u64 * 8 / bandwidths[validator as usize];
        SimTime::new(latency)
    }

    ///
    pub fn propagation_delay(&self, sender: ValidatorId, receiver: ValidatorId) -> SimTime {
        let sender_server = self.ping_servers[sender as usize].id;
        let receiver_server = self.ping_servers[receiver as usize].id;
        let ping_ms = get_ping(sender_server, receiver_server).unwrap();
        let latency_ns = (ping_ms * 1e6).round() as u64;
        SimTime::new(latency_ns)
    }
}
