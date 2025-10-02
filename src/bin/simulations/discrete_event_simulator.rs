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
use std::sync::{RwLock, RwLockReadGuard};

use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use log::debug;
use rand::prelude::*;
use rayon::prelude::*;

pub use self::resources::Resources;
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
        resources: &mut Resources,
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
    }

    /// Runs one iteration of the simulation.
    pub fn run(&self, instance: &P::Instance, timings: &mut Timings<P::Event>) {
        // setup & initialization
        let num_val = self.environment.num_validators();
        timings.clear();

        let mut resources = Resources::new(num_val);

        // simulation loop
        for stage in P::Stage::all() {
            for event in stage.events(self.builder.params()) {
                debug!("initializing timings for event {}", event.name());
                timings.initialize(event, num_val);
            }

            for event in stage.events(self.builder.params()) {
                let dep_timings = event
                    .dependencies(self.builder.params())
                    .into_iter()
                    .map(|dep| {
                        debug!("requesting dep timings for event {}", dep.name());
                        timings.get(dep).unwrap()
                    })
                    .collect::<Vec<_>>();
                let latencies = event.calculate_timing(
                    &dep_timings,
                    instance,
                    &mut resources,
                    &self.environment,
                );
                for (validator, latency) in latencies.iter().enumerate() {
                    timings.record(event, *latency, validator as ValidatorId);
                }
            }
        }

        // commit timings to stats
        let mut stats_map = self.stats.write().unwrap();
        stats_map.record_latencies(timings, &self.environment);
    }

    /// References the timing stats.
    pub fn stats<'a>(&'a self) -> RwLockReadGuard<'a, TimingStats<P>> {
        self.stats.read().unwrap()
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
    }
}

/// Information about the environment in which the simulation is running.
///
/// This includes the validators, their stakes, bandwidths, ping data, etc.
#[derive(Clone, Debug)]
pub struct SimulationEnvironment {
    // core setup of the latency test
    pub(crate) validators: Vec<ValidatorInfo>,
    ping_servers: Vec<&'static PingServer>,
    pub(crate) total_stake: Stake,

    // optional bandwidth information
    // if provided, these will be used to simulate transmission delays
    // otherwise, transmission delay is ignored
    leader_bandwidth: Option<u64>,
    bandwidths: Option<Vec<u64>>,
}

impl SimulationEnvironment {
    /// Creates a new simulation environment.
    pub fn new(validators: Vec<ValidatorInfo>, ping_servers: Vec<&'static PingServer>) -> Self {
        let total_stake = validators.iter().map(|v| v.stake).sum();
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
        Self::new(vals, ping_servers)
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
        SimTime::from_secs(latency_secs)
    }

    /// Finds the latency between the `sender` and `receiver` validators.
    pub fn propagation_delay(&self, sender: ValidatorId, receiver: ValidatorId) -> SimTime {
        let sender_server = self.ping_servers[sender as usize].id;
        let receiver_server = self.ping_servers[receiver as usize].id;
        let rtt_ping_ms = get_ping(sender_server, receiver_server).unwrap();
        let one_way_ping_secs = rtt_ping_ms / 2.0 / 1e3;
        SimTime::from_secs(one_way_ping_secs)
    }
}

/// Returns the minimum of each column over the given rows.
///
/// Requires that all rows have the same length.
/// Outputs a vector of the same length, containing the minimum in each column.
///
/// # Panics
///
/// - Panics if `rows` is empty.
/// - Panics if any row does not have the same length as the first row.
pub fn column_min<T: Copy + Ord>(rows: &[&[T]]) -> Vec<T> {
    assert!(!rows.is_empty());
    let mut result = rows[0].to_vec();
    for row in &rows[1..] {
        assert_eq!(row.len(), result.len(), "all rows must have same length");
        for (res, &val) in result.iter_mut().zip(row.iter()) {
            if val < *res {
                *res = val;
            }
        }
    }
    result
}

/// Returns the maximum of each column over the given rows.
///
/// Requires that all rows have the same length.
/// Outputs a vector of the same length, containing the maximum in each column.
///
/// # Panics
///
/// - Panics if `rows` is empty.
/// - Panics if any row does not have the same length as the first row.
pub fn column_max<T: Copy + Ord>(rows: &[&[T]]) -> Vec<T> {
    assert!(!rows.is_empty());
    let mut result = rows[0].to_vec();
    for row in &rows[1..] {
        assert_eq!(row.len(), result.len(), "all rows must have same length");
        for (res, &val) in result.iter_mut().zip(row.iter()) {
            if val > *res {
                *res = val;
            }
        }
    }
    result
}

pub fn broadcast_first_arrival_or_dep(
    start_times: &[SimTime],
    resources: &mut Resources,
    environment: &SimulationEnvironment,
    message_size: usize,
) -> Vec<SimTime> {
    let mut timings = start_times.to_vec();

    let send_time_iter = broadcast(start_times, resources, environment, message_size);
    let start_send_times = send_time_iter.collect::<Vec<_>>();

    for (recipient, recipient_timing) in timings.iter_mut().enumerate() {
        // calculate first message arrival time
        let first_arrival_time = start_send_times
            .iter()
            .enumerate()
            .map(|(sender, start_send)| {
                let sender = sender as ValidatorId;
                let prop_delay = environment.propagation_delay(sender, recipient as ValidatorId);
                let tx_delay =
                    environment.transmission_delay((recipient + 1) * message_size, sender);
                *start_send + prop_delay + tx_delay
            })
            .min()
            .unwrap();

        if first_arrival_time < *recipient_timing {
            *recipient_timing = first_arrival_time;
        }
    }
    timings
}

pub fn broadcast_stake_threshold(
    start_times: &[SimTime],
    resources: &mut Resources,
    environment: &SimulationEnvironment,
    message_size: usize,
    threshold: f64,
) -> Vec<SimTime> {
    let mut timings = start_times.to_vec();

    let send_time_iter = broadcast(start_times, resources, environment, message_size);
    let start_send_times = send_time_iter.collect::<Vec<_>>();

    for (recipient, recipient_timing) in timings.iter_mut().enumerate() {
        // calculate message arrival timings
        let mut arrival_timings = start_send_times
            .iter()
            .enumerate()
            .map(|(sender, start_send)| {
                let prop_delay =
                    environment.propagation_delay(sender as ValidatorId, recipient as ValidatorId);
                let tx_delay = environment
                    .transmission_delay((recipient + 1) * message_size, sender as ValidatorId);
                (*start_send + prop_delay + tx_delay, sender)
            })
            .collect::<Vec<_>>();

        // find time the stake threshold is first reached
        arrival_timings.sort_unstable();
        let mut stake_so_far = 0;
        for (arrival_timing, sender) in arrival_timings.into_iter() {
            *recipient_timing = arrival_timing;
            stake_so_far += environment.validators[sender].stake;
            if stake_so_far as f64 >= threshold * environment.total_stake as f64 {
                break;
            }
        }
    }
    timings
}

pub fn broadcast(
    start_times: &[SimTime],
    resources: &mut Resources,
    environment: &SimulationEnvironment,
    message_size: usize,
) -> impl Iterator<Item = SimTime> {
    // reserve the network resource
    for sender in 0..environment.num_validators() {
        let total_tx_time = environment.transmission_delay(
            environment.num_validators() * message_size,
            sender as ValidatorId,
        );
        resources
            .network
            .schedule(sender as ValidatorId, start_times[sender], total_tx_time);
    }

    // determine the start time for sending messages
    let resources = &*resources;
    start_times
        .iter()
        .enumerate()
        .map(|(sender, sender_timing)| {
            resources
                .network
                .time_next_free_after(sender as ValidatorId, *sender_timing)
        })
}

#[cfg(test)]
mod tests {
    use alpenglow::network::simulated::stake_distribution::{
        VALIDATOR_DATA, validators_from_validator_data,
    };

    use super::*;

    const TIME_PER_EVENT: SimTime = SimTime::from_secs(60.0);
    const NUM_EVENTS: u64 = 20;
    const NUM_SIMULATION_ITERATIONS: u64 = 100;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct TestEvent(u64);
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct TestStage;
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct TestParams(u64);
    #[derive(Clone, Copy, Debug)]
    struct TestInstance;
    #[derive(Clone, Copy, Debug)]
    struct TestBuilder(TestParams);
    #[derive(Clone, Copy, Debug)]
    struct TestProtocol;

    impl Event for TestEvent {
        type Params = TestParams;
        type Instance = TestInstance;

        fn name(&self) -> String {
            format!("test_event_{}", self.0)
        }

        fn should_track_stats(&self) -> bool {
            true
        }

        fn dependencies(&self, _params: &Self::Params) -> Vec<Self> {
            if self.0 > 0 {
                vec![TestEvent(self.0 - 1)]
            } else {
                vec![]
            }
        }

        fn calculate_timing(
            &self,
            dep_timings: &[&[SimTime]],
            _instance: &TestInstance,
            _resources: &mut Resources,
            environment: &SimulationEnvironment,
        ) -> Vec<SimTime> {
            let mut timings = if self.0 == 0 {
                vec![SimTime::ZERO; environment.num_validators()]
            } else {
                dep_timings[0].to_vec()
            };
            for timing in timings.iter_mut() {
                *timing += TIME_PER_EVENT;
            }
            timings
        }
    }

    impl Stage for TestStage {
        type Event = TestEvent;
        type Params = TestParams;

        fn first() -> Self {
            TestStage
        }

        fn next(&self) -> Option<Self> {
            None
        }

        fn events(&self, params: &TestParams) -> Vec<TestEvent> {
            (0..params.0).map(TestEvent).collect()
        }
    }

    impl Builder for TestBuilder {
        type Params = TestParams;
        type Instance = TestInstance;

        fn build(&self, _rng: &mut impl Rng) -> TestInstance {
            TestInstance
        }

        fn params(&self) -> &TestParams {
            &self.0
        }
    }

    impl Protocol for TestProtocol {
        type Event = TestEvent;
        type Stage = TestStage;
        type Params = TestParams;
        type Instance = TestInstance;
        type Builder = TestBuilder;
    }

    fn setup() -> (SimulationEngine<TestProtocol>, TestBuilder) {
        let (_, vals_with_ping) = validators_from_validator_data(&VALIDATOR_DATA);
        let environment = SimulationEnvironment::from_validators_with_ping_data(&vals_with_ping);
        let builder = TestBuilder(TestParams(NUM_EVENTS));
        let engine = SimulationEngine::new(builder, environment);
        (engine, builder)
    }

    #[test]
    fn single() {
        let (engine, builder) = setup();
        let instance = builder.build(&mut rand::rng());
        let mut timings = Timings::default();
        engine.run(&instance, &mut timings);

        // check that the timings are correct
        for event_id in 0..NUM_EVENTS {
            for time in timings.get(TestEvent(event_id)).unwrap() {
                let expected_time_secs = TIME_PER_EVENT.as_secs() * (event_id + 1) as f64;
                let delta = (time.as_secs() - expected_time_secs).abs();
                assert!(delta < f64::EPSILON);
            }
        }
    }

    const CUSTOM_EPSILON: f64 = 1e-6;

    #[test]
    fn many_parallel() {
        let (engine, _builder) = setup();
        engine.run_many_parallel(NUM_SIMULATION_ITERATIONS);

        // check that the timings are correct
        for event_id in 0..NUM_EVENTS {
            let stats = engine.stats();
            let event_stats = stats.get(&TestEvent(event_id)).unwrap();
            // timings should be the same for all validators, thus also for all percentiles
            for percentile in 1..=100 {
                let avg_timing_ms = event_stats.get_avg_percentile_latency(percentile);
                let expected_time_ms = TIME_PER_EVENT.as_millis() * (event_id + 1) as f64;
                let delta = (avg_timing_ms - expected_time_ms).abs();
                assert!(delta < CUSTOM_EPSILON);
            }
        }
    }

    #[test]
    fn many_sequential() {
        let (engine, _builder) = setup();
        engine.run_many_sequential(NUM_SIMULATION_ITERATIONS);

        // check that the timings are correct
        for event_id in 0..NUM_EVENTS {
            let stats = engine.stats();
            let event_stats = stats.get(&TestEvent(event_id)).unwrap();
            // timings should be the same for all validators, thus also for all percentiles
            for percentile in 1..=100 {
                let avg_timing_ms = event_stats.get_avg_percentile_latency(percentile);
                let expected_time_ms = TIME_PER_EVENT.as_millis() * (event_id + 1) as f64;
                let delta = (avg_timing_ms - expected_time_ms).abs();
                assert!(delta < CUSTOM_EPSILON);
            }
        }
    }
}
