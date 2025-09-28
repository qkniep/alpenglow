// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for the Rotor block dissemination protocol.
//!
//!

use std::marker::PhantomData;

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

///
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

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Direct(usize),
    Rotor(usize),
    Block,
}

impl Event for LatencyEvent {
    ///
    fn name(&self) -> String {
        match self {
            LatencyEvent::Direct(_) => "direct",
            LatencyEvent::Rotor(_) => "rotor",
            LatencyEvent::Block => "block",
        }
        .to_owned()
    }

    ///
    fn should_track_stats(&self) -> bool {
        match self {
            LatencyEvent::Direct(slice) => *slice == 0,
            LatencyEvent::Rotor(slice) => *slice == 0,
            LatencyEvent::Block => true,
        }
    }

    ///
    fn dependencies(&self) -> Vec<LatencyEvent> {
        match self {
            LatencyEvent::Direct(i) => {
                if *i == 0 {
                    vec![]
                } else {
                    vec![LatencyEvent::Direct(*i - 1)]
                }
            }
            LatencyEvent::Rotor(i) => vec![LatencyEvent::Direct(*i)],
            LatencyEvent::Block => vec![LatencyEvent::Rotor(0)],
        }
    }

    ///
    fn calculate_timing(
        &self,
        dep_timings: &[&[SimTime]],
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        match self {
            LatencyEvent::Direct(i) => {
                let mut timings = match *i {
                    0 => vec![SimTime::ZERO; environment.num_validators()],
                    _ => dep_timings[0].to_vec(),
                };
                // TODO: use actual relays
                // TODO: reserve network resource
                let leader = 0;
                for relay in 1..=64 {
                    timings[relay as usize] += environment.propagation_delay(leader, relay);
                    timings[relay as usize] +=
                        environment.transmission_delay(MAX_DATA_PER_SHRED, leader);
                }
                timings
            }
            LatencyEvent::Rotor(_) => dep_timings[0].to_vec(),
            LatencyEvent::Block => dep_timings[0].to_vec(),
        }
    }
}

///
pub struct LatencyTest<L: SamplingStrategy, R: SamplingStrategy> {
    builder: RotorInstanceBuilder<L, R>,
    environment: SimulationEnvironment,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencyTest<L, R> {
    ///
    pub fn new(builder: RotorInstanceBuilder<L, R>, environment: SimulationEnvironment) -> Self {
        Self {
            builder,
            environment,
        }
    }
}
