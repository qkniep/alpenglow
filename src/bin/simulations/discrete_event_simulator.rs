// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! General discrete-event simulator.
//!
//!

mod timings;

use std::fmt::Debug;
use std::hash::Hash;
use std::sync::RwLock;

use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use log::debug;
use rand::prelude::*;
use rayon::prelude::*;

pub use self::timings::{SimTime, TimingStats, Timings};

///
pub trait Protocol {
    type Event: Event;
    type Stage: Stage<Event = Self::Event, Params = Self::Params>;
    type Params;
    type Instance;
    type Builder: Builder<Params = Self::Params, Instance = Self::Instance>;
}

///
pub trait Builder {
    type Params;
    type Instance;

    ///
    fn build(&self, rng: &mut impl Rng) -> Self::Instance;

    ///
    fn params(&self) -> &Self::Params;
}

///
pub trait Event: Clone + Copy + Debug + Eq + Hash {
    /// Returns the name of the event.
    fn name(&self) -> String;

    /// Returns `true` iff the event should be tracked for timing stats.
    fn should_track_stats(&self) -> bool;

    /// Returns a list of dependency event IDs.
    fn dependencies(&self) -> Vec<Self>;

    /// Calculates timing vector given dependencies.
    fn calculate_timing(
        &self,
        dep_timings: &[&[SimTime]],
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime>;
}

///
pub trait Stage: Clone + Copy + Debug + Eq + Hash {
    type Event: Event;
    type Params: Clone + Send + Sync;

    /// Returns a list of all stages, in order.
    fn all() -> Vec<Self> {
        let mut stages = Vec::new();
        let mut stage = Self::first();
        loop {
            stages.push(stage);
            match stage.next() {
                Some(s) => stage = s,
                None => break,
            }
        }
        stages
    }

    /// Returns the first stage.
    fn first() -> Self;

    /// Returns the next stage, if any.
    fn next(&self) -> Option<Self>;

    /// Returns a list of all events within the stage.
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
pub struct SimulationEngine<P: Protocol> {
    builder: P::Builder,
    environment: SimulationEnvironment,
    stats: RwLock<TimingStats<P>>,
}

impl<P: Protocol> SimulationEngine<P> {
    /// Creates a new simulation engine.
    ///
    /// The `environment` holds the validators, network parameters, etc.
    pub fn new(builder: P::Builder, environment: SimulationEnvironment) -> Self {
        Self {
            builder,
            environment,
            stats: RwLock::new(TimingStats::default()),
        }
    }

    /// Runs the simulation `iterations` times.
    ///
    /// Samples a new `Instance` from the `Builder` for each iteration.
    pub fn run_many_sequential(&self, iterations: u64) {
        let mut rng = rand::rng();
        let mut timings = Timings::default();
        for _ in 0..iterations {
            let instance = self.builder.build(&mut rng);
            self.run(&instance, &mut timings);
        }
        let stats_map = self.stats.read().unwrap();
        // TODO: determine correct filename
        stats_map.write_to_csv("test.csv", self.builder.params());
    }

    /// Runs one iteration of the simulation.
    pub fn run(&self, instance: &P::Instance, timings: &mut Timings<P::Event>) {
        // setup & initialization
        let num_val = self.environment.num_validators();
        timings.clear();

        // simulation loop
        for stage in P::Stage::all() {
            for event in stage.events(self.builder.params()) {
                debug!("initializing timings for event {:?}", event);
                timings.initialize(event, num_val);
            }

            for event in stage.events(self.builder.params()) {
                let dep_timings = event
                    .dependencies()
                    .into_iter()
                    .map(|dep| {
                        debug!("requesting dep timings for event {:?}", dep);
                        timings.get(dep).unwrap()
                    })
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

impl<P: Protocol> SimulationEngine<P>
where
    P::Builder: Send + Sync,
    P::Event: Send + Sync,
{
    ///
    pub fn run_many_parallel(&self, iterations: u64) {
        (0..iterations).into_par_iter().for_each(|_| {
            let mut rng = rand::rng();
            let mut timings = Timings::default();
            let instance = self.builder.build(&mut rng);
            self.run(&instance, &mut timings);
        });
        let stats_map = self.stats.read().unwrap();
        // TODO: determine correct filename
        stats_map.write_to_csv("test.csv", self.builder.params());
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {}
}
