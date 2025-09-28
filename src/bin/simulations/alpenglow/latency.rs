// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for the Alpenglow protocol.
//!
//! So far, this test can only simulate the good case.

use std::hash::Hash;
use std::marker::PhantomData;
use std::path::Path;
use std::sync::RwLock;

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::network::simulated::ping_data::PingServer;
use alpenglow::{Stake, ValidatorInfo};
use rand::prelude::*;
use rayon::prelude::*;

use crate::discrete_event_simulator::{
    Builder, Event, Protocol, SimTime, SimulationEnvironment, Stage, TimingStats, Timings,
};
use crate::rotor::{RotorInstance, RotorInstanceBuilder, RotorParams};

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;
/// Size (in bytes) assumed per certificate in the simulation.
const CERT_SIZE: usize = 128 /* sig */ + 256 /* bitmap */ + 64 /* slot, hash, flags */;

pub struct AlpenglowLatencySimulation<L: SamplingStrategy, R: SamplingStrategy> {
    _leader_sampler: PhantomData<L>,
    _rotor_sampler: PhantomData<R>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> Protocol for AlpenglowLatencySimulation<L, R> {
    type Event = LatencyEvent;
    type Stage = LatencyTestStage;
    type Params = LatencySimParams;
    type Instance = LatencySimInstance;
    type Builder = LatencySimInstanceBuilder<L, R>;
}

/// The sequential stages of the latency test.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Rotor,
    Notar,
    Final1,
    Final2,
}

impl Stage for LatencyTestStage {
    type Event = LatencyEvent;
    type Params = LatencySimParams;

    fn first() -> Self {
        Self::Rotor
    }

    fn next(&self) -> Option<Self> {
        match self {
            Self::Rotor => Some(Self::Notar),
            Self::Notar => Some(Self::Final1),
            Self::Final1 => Some(Self::Final2),
            Self::Final2 => None,
        }
    }

    fn events(&self, _params: &Self::Params) -> Vec<LatencyEvent> {
        match self {
            Self::Rotor => vec![LatencyEvent::Direct(0), LatencyEvent::Rotor(0)],
            Self::Notar => vec![LatencyEvent::Notar, LatencyEvent::Shreds95],
            Self::Final1 => vec![
                LatencyEvent::FastFinal,
                LatencyEvent::SlowFinal,
                LatencyEvent::Notar65,
            ],
            Self::Final2 => vec![LatencyEvent::Final],
        }
    }
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

impl Event for LatencyEvent {
    fn name(&self) -> String {
        match self {
            Self::Direct(_) => "direct",
            Self::Rotor(_) => "rotor",
            Self::Shreds95 => "shreds95",
            Self::Notar => "notar",
            Self::Notar65 => "notar65",
            Self::FastFinal => "fast_final",
            Self::SlowFinal => "slow_final",
            Self::Final => "final",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        match self {
            Self::Direct(slice) => *slice == 0,
            Self::Rotor(slice) => *slice == 0,
            _ => true,
        }
    }

    fn dependencies(&self) -> Vec<Self> {
        match self {
            Self::Direct(_) => vec![],
            Self::Rotor(_) => vec![Self::Direct(0)],
            Self::Shreds95 => vec![Self::Rotor(0)],
            Self::Notar => vec![Self::Rotor(0)],
            Self::Notar65 => vec![Self::Notar],
            Self::FastFinal => vec![Self::Notar],
            Self::SlowFinal => vec![Self::Notar],
            Self::Final => vec![Self::SlowFinal, Self::FastFinal],
        }
    }

    fn calculate_timing(
        &self,
        dep_timings: &[&[SimTime]],
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        vec![SimTime::ZERO; environment.num_validators()]
    }
}

///
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LatencySimParams {
    rotor_params: RotorParams,
    num_slots_per_window: usize,
    num_slots: usize,
}

impl LatencySimParams {
    ///
    pub fn new(rotor_params: RotorParams, num_slots_per_window: usize, num_slots: usize) -> Self {
        Self {
            rotor_params,
            num_slots_per_window,
            num_slots,
        }
    }
}

///
pub struct LatencySimInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    rotor_builder: RotorInstanceBuilder<L, R>,
    params: LatencySimParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencySimInstanceBuilder<L, R> {
    ///
    pub fn new(rotor_builder: RotorInstanceBuilder<L, R>, params: LatencySimParams) -> Self {
        Self {
            rotor_builder,
            params,
        }
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> Builder for LatencySimInstanceBuilder<L, R> {
    type Params = LatencySimParams;
    type Instance = LatencySimInstance;

    ///
    fn build(&self, rng: &mut impl Rng) -> LatencySimInstance {
        let rotor_instance = self.rotor_builder.build(rng);
        LatencySimInstance {
            rotor_instance,
            params: self.params.clone(),
        }
    }

    ///
    fn params(&self) -> &Self::Params {
        &self.params
    }
}

///
pub struct LatencySimInstance {
    rotor_instance: RotorInstance,
    params: LatencySimParams,
}

/// Simulated latency test.
pub struct LatencyTest<L: SamplingStrategy, R: SamplingStrategy> {
    builder: LatencySimInstanceBuilder<L, R>,
    environment: SimulationEnvironment,
    /// Running aggregates for percentiles.
    stats: RwLock<TimingStats<AlpenglowLatencySimulation<L, R>>>,
}

impl<L, R> LatencyTest<L, R>
where
    L: SamplingStrategy + Send + Sync,
    R: SamplingStrategy + Send + Sync,
{
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

        let rotor_params = RotorParams {
            num_data_shreds,
            num_shreds,
            num_slices: 1,
        };
        let rotor_builder = RotorInstanceBuilder::new(leader_sampler, rotor_sampler, rotor_params);

        let params = LatencySimParams::new(rotor_params, 4, 1);
        let builder = LatencySimInstanceBuilder::new(rotor_builder, params);

        Self {
            builder,
            environment: SimulationEnvironment::new(validators, ping_servers, total_stake),
            stats: RwLock::new(TimingStats::default()),
        }
    }

    /// Sets the bandwidths for all validators for simulating transmission delays.
    pub fn with_bandwidths(mut self, leader_bandwidth: u64, bandwidths: Vec<u64>) -> Self {
        self.environment = self
            .environment
            .with_bandwidths(leader_bandwidth, bandwidths);
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
        self.stats
            .read()
            .unwrap()
            .write_to_csv(path, &self.builder.params)
            .unwrap();
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
            let mut instance = self.builder.build(&mut rng);
            instance.rotor_instance.leader = leader.id;
            self.run_one_deterministic(up_to_stage, instance);
        }

        let leader_ping_server = self.environment.ping_servers[leader.id as usize];
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
        self.stats
            .read()
            .unwrap()
            .write_to_csv(path, &self.builder.params)
            .unwrap();
    }

    /// Runs one iteration of the latency simulation with random leader and relays.
    pub fn run_one(&self, up_to_stage: LatencyTestStage, rng: &mut impl Rng) {
        let instance = self.builder.build(rng);
        self.run_one_deterministic(up_to_stage, instance);
    }

    /// Runs one iteration of the latency simulation with given leader and relays.
    pub fn run_one_deterministic(
        &self,
        up_to_stage: LatencyTestStage,
        instance: LatencySimInstance,
    ) {
        // setup & initialization
        let num_val = self.environment.num_validators();
        let mut timings = Timings::default();

        // simulation loop
        let mut stage = LatencyTestStage::Rotor;
        while stage <= up_to_stage {
            for event in stage.events(&instance.params) {
                timings.initialize(event, num_val);
            }

            for event in stage.events(&instance.params) {
                //
            }

            match stage.next() {
                Some(s) => stage = s,
                None => break,
            }
        }

        // commit latencies to stats (update averages)
        let stats_map = &mut self.stats.write().unwrap();
        stats_map.record_latencies(&mut timings, &self.environment);
    }
}
