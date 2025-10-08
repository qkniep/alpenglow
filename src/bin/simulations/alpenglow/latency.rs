// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for the Alpenglow protocol.
//!
//! So far, this test can only simulate the happy path.

use std::hash::Hash;
use std::marker::PhantomData;

use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use rand::prelude::*;

use crate::discrete_event_simulator::{
    Builder, Event, Protocol, Resources, SimTime, SimulationEngine, SimulationEnvironment, Stage,
    Timings, broadcast_first_arrival_or_dep, broadcast_stake_threshold, column_min,
};
use crate::rotor::{RotorInstance, RotorInstanceBuilder, RotorLatencySimulation, RotorParams};

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;
/// Size (in bytes) assumed per certificate in the simulation.
const CERT_SIZE: usize = 128 /* sig */ + 256 /* bitmap */ + 64 /* slot, hash, flags */;

/// Marker type for the Alpenglow latency simulation.
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
            Self::Rotor => vec![LatencyEvent::Block],
            Self::Notar => vec![LatencyEvent::LocalNotar, LatencyEvent::Notar],
            Self::Final1 => vec![LatencyEvent::LocalFastFinal, LatencyEvent::LocalSlowFinal],
            Self::Final2 => vec![LatencyEvent::LocalFinal, LatencyEvent::Final],
        }
    }
}

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Block,
    LocalNotar,
    Notar,
    LocalFastFinal,
    LocalSlowFinal,
    LocalFinal,
    Final,
}

impl Event for LatencyEvent {
    type Params = LatencySimParams;
    type Instance = LatencySimInstance;

    fn name(&self) -> String {
        match self {
            Self::Block => "block",
            Self::LocalNotar => "local_notar",
            Self::Notar => "notar",
            Self::LocalFastFinal => "local_fast_final",
            Self::LocalSlowFinal => "local_slow_final",
            Self::LocalFinal => "local_final",
            Self::Final => "final",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        true
    }

    // TODO: simulate actual circular dependency (of certs and status)
    fn dependencies(&self, _params: &LatencySimParams) -> Vec<Self> {
        match self {
            Self::Block => vec![],
            Self::LocalNotar => vec![Self::Block],
            Self::Notar => vec![Self::LocalNotar],
            Self::LocalFastFinal => vec![Self::Block],
            Self::LocalSlowFinal => vec![Self::Notar],
            Self::LocalFinal => vec![Self::LocalFastFinal, Self::LocalSlowFinal],
            Self::Final => vec![Self::LocalFinal],
        }
    }

    fn calculate_timing(
        &self,
        start_time: SimTime,
        dependency_timings: &[&[SimTime]],
        instance: &LatencySimInstance,
        resources: &mut Resources,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        let broadcast_vote_threshold =
            |resources: &mut Resources, threshold: f64| -> Vec<SimTime> {
                broadcast_stake_threshold(
                    dependency_timings[0],
                    resources,
                    environment,
                    VOTE_SIZE,
                    threshold,
                )
            };

        let local_or_cert = |resources: &mut Resources| -> Vec<SimTime> {
            broadcast_first_arrival_or_dep(dependency_timings[0], resources, environment, CERT_SIZE)
        };

        match self {
            Self::Block => {
                // TODO: find better way of integrating sub-protocol
                let builder = RotorInstanceBuilder::new(
                    StakeWeightedSampler::new(environment.validators.clone()),
                    StakeWeightedSampler::new(environment.validators.clone()),
                    instance.params.rotor_params,
                );
                let engine = SimulationEngine::<RotorLatencySimulation<_, _>>::new(
                    builder,
                    environment.clone(),
                );
                let mut timings = Timings::new(start_time);
                // TODO: actually simulate more than one slot
                engine.run(&instance.rotor_instances[0], &mut timings);
                timings
                    .get(crate::rotor::LatencyEvent::Block)
                    .unwrap()
                    .to_vec()
            }
            Self::LocalNotar => broadcast_vote_threshold(resources, 0.6),
            Self::Notar => local_or_cert(resources),
            Self::LocalFastFinal => broadcast_vote_threshold(resources, 0.8),
            Self::LocalSlowFinal => broadcast_vote_threshold(resources, 0.6),
            Self::LocalFinal => column_min(dependency_timings),
            // NOTE: when sending final cert, final vote is already scheduled
            // TODO: this is not always optimal, handle this properly
            Self::Final => local_or_cert(resources),
        }
    }
}

/// Parameters for the Alpenglow latency simulation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LatencySimParams {
    rotor_params: RotorParams,
    num_slots_per_window: usize,
    num_slots: usize,
}

impl LatencySimParams {
    /// Creates a parameter set for the Alpenglow latency simulation.
    pub fn new(rotor_params: RotorParams, num_slots_per_window: usize, num_slots: usize) -> Self {
        Self {
            rotor_params,
            num_slots_per_window,
            num_slots,
        }
    }
}

/// A builder for Alpenglow latency simulation instances.
pub struct LatencySimInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    rotor_builder: RotorInstanceBuilder<L, R>,
    params: LatencySimParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencySimInstanceBuilder<L, R> {
    /// Creates a new builder instance from a builder for Rotor instances.
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

    fn build(&self, rng: &mut impl Rng) -> LatencySimInstance {
        let rotor_instances = (0..self.params.num_slots)
            .map(|_| self.rotor_builder.build(rng))
            .collect();
        LatencySimInstance {
            rotor_instances,
            params: self.params.clone(),
        }
    }

    fn params(&self) -> &Self::Params {
        &self.params
    }
}

/// A specific instance of the Alpenglow latency simulation.
///
/// Contains one instance of the Rotor latency simulation, [`RotorInstance`], per slot.
pub struct LatencySimInstance {
    rotor_instances: Vec<RotorInstance>,
    params: LatencySimParams,
}
