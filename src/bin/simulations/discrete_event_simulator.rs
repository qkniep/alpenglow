// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! General discrete-event simulator.
//!
//! This module provides a generic discrete-event simulator.
//! It can be used to simulate different protocols and configurations.

mod resources;
mod timings;

use std::cmp::Reverse;
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::RwLock;

use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use log::debug;
use rand::prelude::*;
use rayon::prelude::*;

pub use self::timings::{SimTime, TimingStats, Timings};

/// Wrapper trait for a specific protocol simulation.
pub trait Protocol {
    type Event: Event<Params = Self::Params, Instance = Self::Instance>;
    type Stage: Stage<Event = Self::Event, Params = Self::Params>;
    type Params;
    type Instance;
    type Builder: Builder<Params = Self::Params, Instance = Self::Instance>;
}

/// Builder for instances of a protocol with a specific set of parameters.
pub trait Builder {
    type Params;
    type Instance;

    /// Samples a new instance from the builder.
    fn build(&self, rng: &mut impl Rng) -> Self::Instance;

    /// Returns the parameters used by this builder.
    fn params(&self) -> &Self::Params;
}

/// Events that can occur in a protocol simulation.
///
/// Each event has a name, a list of dependencies, and a calculation function.
/// The simulation engine will pass the timings of its dependencies to the calculation function.
/// The calculation function returns the timings of this event at each validator.
pub trait Event: Clone + Copy + Debug + Eq + Hash {
    type Params;
    type Instance;

    /// Returns a printable name for the event.
    ///
    /// This will be used as a column label in the output CSV file.
    fn name(&self) -> String;

    /// Returns `true` iff the event should be tracked for timing stats.
    fn should_track_stats(&self) -> bool;

    /// Returns a list of dependency event IDs.
    fn dependencies(&self, params: &Self::Params) -> Vec<Self>;

    /// Calculates timing vector given dependencies.
    fn calculate_timing(
        &self,
        dep_timings: &[&[SimTime]],
        instance: &Self::Instance,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime>;
}

/// Sequential stages of a protocol simulation.
///
/// Each stage contains one or more events.
/// Events in later stages can only depend on events from earlier stages.
pub trait Stage: Clone + Copy + Debug + Eq + Hash {
    type Event: Event;
    type Params;

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

/// Kinds of events that are directly supported by the simulation engine.
pub enum EventKind {
    /// This event fires as soon as its dependencies are ready.
    Simple,
    /// This event uses the senders outgoing network bandwidth.
    Broadcast,
    /// This event uses the CPU for a certain amount of time.
    Compute,
    /// To determine when this event fires, the simulation engine runs a sub-protocol.
    SubProtocol,
    /// This event fires based on a user-provided function.
    Custom,
}

/// Matrix-based discrete-event simulation engine.
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
        stats_map
            .write_to_csv("test.csv", self.builder.params())
            .expect("failed to write stats to CSV");
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
                    .dependencies(self.builder.params())
                    .into_iter()
                    .map(|dep| {
                        debug!("requesting dep timings for event {:?}", dep);
                        timings.get(dep).unwrap()
                    })
                    .collect::<Vec<_>>();
                let latencies = event.calculate_timing(&dep_timings, instance, &self.environment);
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
    /// Runs the simulation `iterations` times in parallel.
    ///
    /// Samples a new `Instance` from the `Builder` for each iteration.
    /// Uses the [`rayon`] crate for the thread pool.
    pub fn run_many_parallel(&self, iterations: u64) {
        (0..iterations).into_par_iter().for_each(|_| {
            let mut rng = rand::rng();
            let mut timings = Timings::default();
            let instance = self.builder.build(&mut rng);
            self.run(&instance, &mut timings);
        });
        let stats_map = self.stats.read().unwrap();
        // TODO: determine correct filename
        stats_map
            .write_to_csv("test.csv", self.builder.params())
            .expect("failed to write stats to CSV");
    }
}

/// Information about the environment in which the simulation is running.
///
/// This includes the validators, their stakes, bandwidths, ping data, etc.
#[derive(Clone, Debug)]
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
    /// Creates a new simulation environment.
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

    /// Creates a new simulation environment from a list of validators with ping data.
    pub fn from_validators_with_ping_data(
        validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
    ) -> Self {
        // sort by stake (from highest to lowest)
        let mut vals_with_ping_data = validators_with_ping_data.to_vec();
        vals_with_ping_data.sort_by_key(|(v, _)| Reverse(v.stake));
        for (i, (v, _)) in vals_with_ping_data.iter_mut().enumerate() {
            v.id = i as ValidatorId;
        }

        // split and build environment
        let vals = vals_with_ping_data.iter().map(|(v, _)| v.clone()).collect();
        let ping_servers = vals_with_ping_data.iter().map(|(_, p)| *p).collect();
        let total_stake: Stake = vals_with_ping_data.iter().map(|(v, _)| v.stake).sum();
        Self::new(vals, ping_servers, total_stake)
    }

    /// Sets the bandwidths for all validators for simulating transmission delays.
    pub fn with_bandwidths(mut self, leader_bandwidth: u64, bandwidths: Vec<u64>) -> Self {
        self.leader_bandwidth = Some(leader_bandwidth);
        self.bandwidths = Some(bandwidths);
        self
    }

    /// Returns the number of validators.
    pub fn num_validators(&self) -> usize {
        self.validators.len()
    }

    /// Calculates how long it takes the `validator` to serialize `bytes` onto the wire.
    pub fn transmission_delay(&self, bytes: usize, validator: ValidatorId) -> SimTime {
        let Some(bandwidths) = &self.bandwidths else {
            return SimTime::ZERO;
        };
        let latency_secs = bytes as f64 * 8.0 / bandwidths[validator as usize] as f64;
        let latency_ns = (latency_secs * 1e9).round() as u64;
        SimTime::new(latency_ns)
    }

    /// Finds the latency between the `sender` and `receiver` validators.
    pub fn propagation_delay(&self, sender: ValidatorId, receiver: ValidatorId) -> SimTime {
        let sender_server = self.ping_servers[sender as usize].id;
        let receiver_server = self.ping_servers[receiver as usize].id;
        let rtt_ping_ms = get_ping(sender_server, receiver_server).unwrap();
        let one_way_ping_ms = rtt_ping_ms / 2.0;
        let latency_ns = (one_way_ping_ms * 1e6).round() as u64;
        SimTime::new(latency_ns)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {}
}
