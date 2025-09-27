// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for the Rotor block dissemination protocol.
//!
//!

use alpenglow::disseminator::rotor::SamplingStrategy;

use crate::discrete_event_simulator::{Event, SimTime, SimulationEnvironment, Stage};
use crate::rotor::{RotorInstanceBuilder, RotorParams};

///
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Direct,
    Rotor,
    Block,
}

impl Stage for LatencyTestStage {
    type Event = LatencyEvent;

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

    fn events(&self) -> Vec<LatencyEvent> {
        match self {
            LatencyTestStage::Direct => vec![LatencyEvent::Direct(0)],
            LatencyTestStage::Rotor => vec![LatencyEvent::Rotor(0)],
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
    fn name(&self) -> &str {
        match self {
            LatencyEvent::Direct(_) => "direct",
            LatencyEvent::Rotor(_) => "rotor",
            LatencyEvent::Block => "block",
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
            LatencyEvent::Block => vec![],
        }
    }

    ///
    fn calculate_timing(&self, dep_timings: &[&[SimTime]]) -> Vec<SimTime> {
        todo!()
    }
}

fn events_for_params(params: RotorParams) -> Vec<LatencyEvent> {
    let mut events = Vec::with_capacity(2 * params.num_slices + 1);
    for i in 0..params.num_slices {
        events.push(LatencyEvent::Direct(i));
        events.push(LatencyEvent::Rotor(i));
    }
    events.push(LatencyEvent::Block);
    events
}

///
pub struct LatencyTest<L: SamplingStrategy, R: SamplingStrategy> {
    builder: RotorInstanceBuilder<L, R>,
    environment: SimulationEnvironment,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencyTest<L, R> {
    pub fn new(builder: RotorInstanceBuilder<L, R>, environment: SimulationEnvironment) -> Self {
        Self {
            builder,
            environment,
        }
    }
}
