// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for the Rotor block dissemination protocol.
//!
//!

use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::shredder::MAX_DATA_PER_SHRED;

use crate::discrete_event_simulator::{Event, Protocol, SimTime, SimulationEnvironment, Stage};
use crate::rotor::{RotorInstance, RotorInstanceBuilder, RotorParams};

///
pub struct RotorLatencySimulation<L: SamplingStrategy, R: SamplingStrategy> {
    _leader_sampler: PhantomData<L>,
    _rotor_sampler: PhantomData<R>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> Protocol for RotorLatencySimulation<L, R> {
    type Event = LatencyEvent;
    type Stage = LatencyTestStage;
    type Params = RotorParams;
    type Instance = RotorInstance;
    type Builder = RotorInstanceBuilder<L, R>;
}

/// Stages of the Rotor latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Direct,
    Rotor,
    Block,
}

impl Stage for LatencyTestStage {
    type Event = LatencyEvent;
    type Params = RotorParams;

    fn first() -> Self {
        LatencyTestStage::Direct
    }

    fn next(&self) -> Option<Self> {
        match self {
            LatencyTestStage::Direct => Some(LatencyTestStage::Rotor),
            LatencyTestStage::Rotor => Some(LatencyTestStage::Block),
            LatencyTestStage::Block => None,
        }
    }

    fn events(&self, params: &Self::Params) -> Vec<LatencyEvent> {
        match self {
            LatencyTestStage::Direct => (0..params.num_slices).map(LatencyEvent::Direct).collect(),
            LatencyTestStage::Rotor => (0..params.num_slices).map(LatencyEvent::Rotor).collect(),
            LatencyTestStage::Block => vec![LatencyEvent::Block],
        }
    }
}

/// Events that can occur at each validator during the Rotor latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Direct(usize),
    Rotor(usize),
    Block,
}

impl Event for LatencyEvent {
    type Params = RotorParams;
    type Instance = RotorInstance;

    fn name(&self) -> String {
        match self {
            LatencyEvent::Direct(_) => "direct",
            LatencyEvent::Rotor(_) => "rotor",
            LatencyEvent::Block => "block",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        match self {
            LatencyEvent::Direct(slice) => *slice == 0,
            LatencyEvent::Rotor(slice) => *slice == 0,
            LatencyEvent::Block => true,
        }
    }

    fn dependencies(&self, params: &RotorParams) -> Vec<LatencyEvent> {
        match self {
            LatencyEvent::Direct(slice) => {
                if *slice == 0 {
                    vec![]
                } else {
                    vec![LatencyEvent::Direct(*slice - 1)]
                }
            }
            LatencyEvent::Rotor(slice) => vec![LatencyEvent::Direct(*slice)],
            LatencyEvent::Block => {
                let mut dependencies = Vec::new();
                for slice in 0..params.num_slices {
                    dependencies.push(LatencyEvent::Rotor(slice));
                }
                dependencies
            }
        }
    }

    fn calculate_timing(
        &self,
        dependency_timings: &[&[SimTime]],
        instance: &RotorInstance,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        match self {
            LatencyEvent::Direct(slice) => {
                let mut timings = match *slice {
                    0 => (0..environment.num_validators())
                        .map(|recipient| environment.propagation_delay(0, recipient as ValidatorId))
                        .collect(),
                    _ => dependency_timings[0].to_vec(),
                };
                // TODO: reserve network resource
                let leader = 0;
                for relay in &instance.relays[*slice] {
                    timings[*relay as usize] +=
                        environment.transmission_delay(MAX_DATA_PER_SHRED, leader);
                }
                timings
            }
            LatencyEvent::Rotor(slice) => {
                let mut timings = dependency_timings[0].to_vec();
                for recipient in 0..environment.num_validators() {
                    // TODO: reserve network resource
                    let mut shred_timings = vec![SimTime::NEVER; instance.params.num_shreds];
                    for (i, relay) in instance.relays[*slice].iter().enumerate() {
                        shred_timings[i] = timings[*relay as usize];
                        shred_timings[i] +=
                            environment.propagation_delay(*relay, recipient as ValidatorId);
                        shred_timings[i] += environment
                            .transmission_delay((recipient + 1) * MAX_DATA_PER_SHRED, *relay);
                    }
                    shred_timings.sort_unstable();
                    timings[recipient] += shred_timings[31];
                }
                timings
            }
            LatencyEvent::Block => column_max(dependency_timings),
        }
    }
}

fn column_max<T: Copy + Ord>(rows: &[&[T]]) -> Vec<T> {
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
