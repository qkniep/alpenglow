// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for the Rotor block dissemination protocol.
//!
//!

use alpenglow::disseminator::rotor::SamplingStrategy;

use crate::discrete_event_simulator::SimulationEnvironment;
use crate::rotor::{RotorInstanceBuilder, RotorParams};

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Direct(usize),
    Rotor(usize),
    Block,
}

impl LatencyEvent {
    ///
    pub fn dependencies(&self) -> Vec<LatencyEvent> {
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
