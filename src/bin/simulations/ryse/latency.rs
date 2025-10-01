// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for Ryse, the MCP protocol.
//!
//! So far, this test can only simulate the good case.

use std::hash::Hash;
use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use rand::prelude::*;

use crate::discrete_event_simulator::{
    Builder, Event, Protocol, Resources, SimTime, SimulationEngine, SimulationEnvironment, Stage,
    Timings,
};
use crate::rotor::{RotorInstance, RotorInstanceBuilder, RotorLatencySimulation, RotorParams};
use crate::ryse::{RyseInstance, RyseInstanceBuilder, RyseParams};

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;
/// Size (in bytes) assumed per certificate in the simulation.
const CERT_SIZE: usize = 128 /* sig */ + 256 /* bitmap */ + 64 /* slot, hash, flags */;

pub struct RyseLatencySimulation<L: SamplingStrategy, R: SamplingStrategy> {
    _leader_sampler: PhantomData<L>,
    _rotor_sampler: PhantomData<R>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> Protocol for RyseLatencySimulation<L, R> {
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
            Self::Notar => vec![LatencyEvent::Notar],
            Self::Final1 => vec![LatencyEvent::FastFinal, LatencyEvent::SlowFinal],
            Self::Final2 => vec![LatencyEvent::Final],
        }
    }
}

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Block,
    Notar,
    FastFinal,
    SlowFinal,
    Final,
}

impl Event for LatencyEvent {
    type Params = LatencySimParams;
    type Instance = LatencySimInstance;

    fn name(&self) -> String {
        match self {
            Self::Block => "block",
            Self::Notar => "notar",
            Self::FastFinal => "fast_final",
            Self::SlowFinal => "slow_final",
            Self::Final => "final",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        true
    }

    fn dependencies(&self, _params: &LatencySimParams) -> Vec<Self> {
        match self {
            Self::Block => vec![],
            Self::Notar => vec![Self::Block],
            Self::FastFinal => vec![Self::Notar],
            Self::SlowFinal => vec![Self::Notar],
            Self::Final => vec![Self::SlowFinal, Self::FastFinal],
        }
    }

    fn calculate_timing(
        &self,
        dependency_timings: &[&[SimTime]],
        _instance: &LatencySimInstance,
        _resources: &mut Resources,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        let broadcast_vote_threshold = |threshold: f64| -> Vec<SimTime> {
            let mut timings = dependency_timings[0].to_vec();
            for recipient in 0..environment.num_validators() {
                // calculate vote arrival timings
                // TODO: reserve network resource
                let mut vote_timings = (0..environment.num_validators())
                    .map(|sender| (SimTime::NEVER, sender))
                    .collect::<Vec<_>>();
                for sender in 0..environment.num_validators() {
                    vote_timings[sender].0 = timings[sender]
                        + environment
                            .propagation_delay(sender as ValidatorId, recipient as ValidatorId)
                        + environment
                            .transmission_delay((recipient + 1) * VOTE_SIZE, sender as ValidatorId);
                }

                // find time the stake threshold is first reached
                vote_timings.sort_unstable();
                let mut stake_so_far = 0;
                for (vote_timing, sender) in vote_timings.into_iter() {
                    timings[recipient] = vote_timing;
                    stake_so_far += environment.validators[sender].stake;
                    if stake_so_far as f64 >= threshold * environment.total_stake as f64 {
                        break;
                    }
                }
            }
            timings
        };

        match self {
            Self::Block => {
                // TODO: find better way of integrating sub-protocol
                let builder = RotorInstanceBuilder::new(
                    StakeWeightedSampler::new(environment.validators.clone()),
                    StakeWeightedSampler::new(environment.validators.clone()),
                    _instance.params.rotor_params,
                );
                let engine = SimulationEngine::<RotorLatencySimulation<_, _>>::new(
                    builder,
                    environment.clone(),
                );
                let mut timings = Timings::default();
                // TODO: actually simulate more than one slot
                engine.run(&_instance.rotor_instances[0], &mut timings);
                timings
                    .get(crate::rotor::LatencyEvent::Block)
                    .unwrap()
                    .to_vec()
            }
            Self::Notar => broadcast_vote_threshold(0.6),
            Self::FastFinal => broadcast_vote_threshold(0.8),
            Self::SlowFinal => broadcast_vote_threshold(0.6),
            Self::Final => column_min(dependency_timings),
        }
    }
}

/// Parameters for the Ryse latency simulation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LatencySimParams {
    rotor_params: RotorParams,
    num_slots_per_window: usize,
    num_slots: usize,
}

impl LatencySimParams {
    /// Creates a parameter set for the Ryse latency simulation.
    pub fn new(rotor_params: RotorParams, num_slots_per_window: usize, num_slots: usize) -> Self {
        Self {
            rotor_params,
            num_slots_per_window,
            num_slots,
        }
    }
}

/// A builder for Ryse latency simulation instances.
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

/// A specific instance of the Ryse latency simulation.
///
/// Contains one instance of the Rotor latency simulation, [`RotorInstance`], per slot.
pub struct LatencySimInstance {
    rotor_instances: Vec<RotorInstance>,
    params: LatencySimParams,
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
fn column_min<T: Copy + Ord>(rows: &[&[T]]) -> Vec<T> {
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
