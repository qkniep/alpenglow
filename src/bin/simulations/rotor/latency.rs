// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for the Rotor block dissemination protocol.
//!
//!

use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::shredder::MAX_DATA_PER_SHRED;

use super::{RotorInstance, RotorInstanceBuilder, RotorParams};
use crate::discrete_event_simulator::{Event, Protocol, SimTime, SimulationEnvironment, Stage};

/// Wrapper type for the Rotor latency simulation.
///
/// This type implements the `Protocol` trait and can be passed to the simulation engine.
/// There is probably never a need to construct this type directly.
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
            LatencyTestStage::Rotor => {
                let mut events = Vec::with_capacity(2 * params.num_slices + 1);
                events.push(LatencyEvent::BlockSent);
                for slice in 0..params.num_slices {
                    events.push(LatencyEvent::FirstShredInSlice(slice));
                    events.push(LatencyEvent::Rotor(slice));
                }
                events
            }
            LatencyTestStage::Block => vec![LatencyEvent::FirstShred, LatencyEvent::Block],
        }
    }
}

/// Events that can occur at each validator during the Rotor latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Direct(usize),
    BlockSent,
    FirstShredInSlice(usize),
    Rotor(usize),
    FirstShred,
    Block,
}

impl Event for LatencyEvent {
    type Params = RotorParams;
    type Instance = RotorInstance;

    fn name(&self) -> String {
        match self {
            LatencyEvent::Direct(_) => "direct",
            LatencyEvent::BlockSent => "block_sent",
            LatencyEvent::FirstShredInSlice(_) => "first_shred_in_slice",
            LatencyEvent::Rotor(_) => "rotor",
            LatencyEvent::FirstShred => "first_shred",
            LatencyEvent::Block => "block",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        match self {
            LatencyEvent::Direct(slice) => *slice == 0,
            LatencyEvent::BlockSent => true,
            LatencyEvent::FirstShredInSlice(_) => false,
            LatencyEvent::Rotor(slice) => *slice == 0,
            LatencyEvent::FirstShred => true,
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
            LatencyEvent::BlockSent => (0..params.num_slices).map(LatencyEvent::Direct).collect(),
            LatencyEvent::FirstShredInSlice(slice) => vec![LatencyEvent::Direct(*slice)],
            LatencyEvent::Rotor(slice) => vec![LatencyEvent::Direct(*slice)],
            LatencyEvent::FirstShred => (0..params.num_slices)
                .map(LatencyEvent::FirstShredInSlice)
                .collect(),
            LatencyEvent::Block => (0..params.num_slices).map(LatencyEvent::Rotor).collect(),
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
                    0 => (0..environment.num_validators() as ValidatorId)
                        .map(|recipient| environment.propagation_delay(instance.leader, recipient))
                        .collect(),
                    _ => dependency_timings[0].to_vec(),
                };
                // TODO: reserve network resource
                for relay in &instance.relays[*slice] {
                    timings[*relay as usize] +=
                        environment.transmission_delay(MAX_DATA_PER_SHRED, instance.leader);
                }
                timings
            }
            LatencyEvent::BlockSent => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                timings[instance.leader as usize] = SimTime::ZERO;
                let block_bytes =
                    instance.params.num_slices * instance.params.num_shreds * MAX_DATA_PER_SHRED;
                timings[instance.leader as usize] +=
                    environment.transmission_delay(block_bytes, instance.leader);
                timings
            }
            LatencyEvent::FirstShredInSlice(slice) => {
                let mut timings = dependency_timings[0].to_vec();
                for recipient in 0..environment.num_validators() {
                    // TODO: reserve network resource
                    let first_shred_time = instance.relays[*slice]
                        .iter()
                        .map(|relay| {
                            let prop_delay =
                                environment.propagation_delay(*relay, recipient as ValidatorId);
                            let tx_delay = environment
                                .transmission_delay((recipient + 1) * MAX_DATA_PER_SHRED, *relay);
                            timings[*relay as usize] + prop_delay + tx_delay
                        })
                        .min()
                        .unwrap();
                    timings[recipient] = first_shred_time;
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
            LatencyEvent::FirstShred => column_min(dependency_timings),
            LatencyEvent::Block => column_max(dependency_timings),
        }
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

/// Returns the maximum of each column over the given rows.
///
/// Requires that all rows have the same length.
/// Outputs a vector of the same length, containing the maximum in each column.
///
/// # Panics
///
/// - Panics if `rows` is empty.
/// - Panics if any row does not have the same length as the first row.
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
