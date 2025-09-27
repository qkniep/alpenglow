// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for the Alpenglow protocol.
//!
//! So far, this test can only simulate the good case.

use std::hash::Hash;
use std::path::Path;
use std::sync::RwLock;

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::network::simulated::ping_data::PingServer;
use alpenglow::{Stake, ValidatorInfo};
use rand::prelude::*;
use rayon::prelude::*;

use crate::discrete_event_simulator::{SimulationEnvironment, TimingStats, Timings};
use crate::rotor::{RotorInstance, RotorInstanceBuilder, RotorParams};

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;
/// Size (in bytes) assumed per certificate in the simulation.
const CERT_SIZE: usize = 128 /* sig */ + 256 /* bitmap */ + 64 /* slot, hash, flags */;

/// The sequential stages of the latency test.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Rotor,
    Notar,
    Final1,
    Final2,
}

impl LatencyTestStage {
    fn next(self) -> Option<Self> {
        match self {
            LatencyTestStage::Rotor => Some(LatencyTestStage::Notar),
            LatencyTestStage::Notar => Some(LatencyTestStage::Final1),
            LatencyTestStage::Final1 => Some(LatencyTestStage::Final2),
            LatencyTestStage::Final2 => None,
        }
    }

    fn events(self) -> Vec<LatencyEvent> {
        match self {
            LatencyTestStage::Rotor => vec![LatencyEvent::Direct(0), LatencyEvent::Rotor(0)],
            LatencyTestStage::Notar => vec![LatencyEvent::Notar, LatencyEvent::Shreds95],
            LatencyTestStage::Final1 => vec![LatencyEvent::FastFinal, LatencyEvent::SlowFinal],
            LatencyTestStage::Final2 => vec![LatencyEvent::Final],
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

    ///
    pub fn sample_instance(&self, rng: &mut impl Rng) -> LatencySimInstance {
        let rotor_instance = self.rotor_builder.build(rng);
        LatencySimInstance {
            rotor_instance,
            params: self.params.clone(),
        }
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
    stats: RwLock<TimingStats<LatencyEvent>>,
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
            stats: RwLock::new(TimingStats::<LatencyEvent>::default()),
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
            .write_to_csv(
                path,
                &[
                    ("direct", LatencyEvent::Direct(0)),
                    ("rotor", LatencyEvent::Rotor(0)),
                    ("shreds95", LatencyEvent::Shreds95),
                    ("notar", LatencyEvent::Notar),
                    ("fast_final", LatencyEvent::FastFinal),
                    ("slow_final", LatencyEvent::SlowFinal),
                    ("final", LatencyEvent::Final),
                ],
            )
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
            let mut instance = self.builder.sample_instance(&mut rng);
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
            .write_to_csv(
                path,
                &[
                    ("direct", LatencyEvent::Direct(0)),
                    ("rotor", LatencyEvent::Rotor(0)),
                    ("shreds95", LatencyEvent::Shreds95),
                    ("notar", LatencyEvent::Notar),
                    ("fast_final", LatencyEvent::FastFinal),
                    ("slow_final", LatencyEvent::SlowFinal),
                    ("final", LatencyEvent::Final),
                ],
            )
            .unwrap();
    }

    /// Runs one iteration of the latency simulation with random leader and relays.
    pub fn run_one(&self, up_to_stage: LatencyTestStage, rng: &mut impl Rng) {
        let instance = self.builder.sample_instance(rng);
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
            for event in stage.events() {
                timings.initialize(event, num_val);
            }

            for event in stage.events() {
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
