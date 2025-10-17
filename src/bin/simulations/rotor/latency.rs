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
use crate::discrete_event_simulator::{
    Event, Protocol, Resources, SimTime, SimulationEnvironment, Stage, column_max, column_min,
};

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
        Self::Direct
    }

    fn next(&self) -> Option<Self> {
        match self {
            Self::Direct => Some(Self::Rotor),
            Self::Rotor => Some(Self::Block),
            Self::Block => None,
        }
    }

    fn events(&self, params: &RotorParams) -> Vec<LatencyEvent> {
        match self {
            Self::Direct => {
                let mut events = Vec::with_capacity(params.slices + 1);
                events.push(LatencyEvent::BlockSent);
                for slice in 0..params.slices {
                    events.push(LatencyEvent::Direct(slice));
                }
                events
            }
            Self::Rotor => {
                let mut events = Vec::with_capacity(3 * params.slices);
                for slice in 0..params.slices {
                    events.push(LatencyEvent::StartForwarding(slice));
                    events.push(LatencyEvent::FirstShredInSlice(slice));
                    events.push(LatencyEvent::Rotor(slice));
                }
                events
            }
            Self::Block => vec![LatencyEvent::FirstShred, LatencyEvent::Block],
        }
    }
}

/// Events that can occur at each validator during the Rotor latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    BlockSent,
    Direct(usize),
    StartForwarding(usize),
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
            Self::BlockSent => "block_sent".to_owned(),
            Self::Direct(slice) => format!("direct_{slice}"),
            Self::StartForwarding(_) => "start_forwarding".to_owned(),
            Self::FirstShredInSlice(_) => "first_shred_in_slice".to_owned(),
            Self::Rotor(slice) => format!("rotor_{slice}"),
            Self::FirstShred => "first_shred".to_owned(),
            Self::Block => "block".to_owned(),
        }
    }

    fn should_track_stats(&self) -> bool {
        match self {
            Self::BlockSent => true,
            Self::Direct(slice) => *slice == 0,
            Self::StartForwarding(_) => false,
            Self::FirstShredInSlice(_) => false,
            Self::Rotor(slice) => *slice == 0,
            Self::FirstShred => true,
            Self::Block => true,
        }
    }

    fn dependencies(&self, params: &RotorParams) -> Vec<Self> {
        match self {
            Self::BlockSent => vec![],
            Self::Direct(slice) => {
                if *slice == 0 {
                    vec![]
                } else {
                    vec![Self::Direct(*slice - 1)]
                }
            }
            Self::StartForwarding(slice) => vec![Self::Direct(*slice)],
            Self::FirstShredInSlice(slice) => {
                vec![Self::StartForwarding(*slice)]
            }
            Self::Rotor(slice) => vec![Self::StartForwarding(*slice)],
            Self::FirstShred => (0..params.slices).map(Self::FirstShredInSlice).collect(),
            Self::Block => (0..params.slices).map(Self::Rotor).collect(),
        }
    }

    fn calculate_timing(
        &self,
        start_time: SimTime,
        dependency_timings: &[&[SimTime]],
        instance: &RotorInstance,
        resources: &mut Resources,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        match self {
            Self::BlockSent => {
                let mut timings = vec![start_time; environment.num_validators()];
                let block_bytes =
                    instance.params.slices * instance.params.shreds * MAX_DATA_PER_SHRED;
                let tx_time = environment.transmission_delay(block_bytes, instance.leader);
                let finished_sending_time =
                    resources
                        .network
                        .schedule(instance.leader, SimTime::ZERO, tx_time);
                timings[instance.leader as usize] += finished_sending_time;
                timings
            }
            Self::Direct(slice) => {
                let mut timings = vec![start_time; environment.num_validators()];
                for (recipient, timing) in timings.iter_mut().enumerate() {
                    *timing +=
                        environment.propagation_delay(instance.leader, recipient as ValidatorId);
                }
                for (relay_offset, &relay) in instance.relays[*slice].iter().enumerate() {
                    let shred_send_index = slice * instance.params.shreds + relay_offset + 1;
                    let tx_delay = environment
                        .transmission_delay(shred_send_index * MAX_DATA_PER_SHRED, instance.leader);
                    timings[relay as usize] += tx_delay;
                }
                timings
            }
            Self::StartForwarding(slice) => {
                let mut timings = dependency_timings[0].to_vec();
                for &relay in &instance.relays[*slice] {
                    let timing = &mut timings[relay as usize];
                    let total_bytes = environment.num_validators() * MAX_DATA_PER_SHRED;
                    let total_tx_delay = environment.transmission_delay(total_bytes, relay);
                    let start_time = resources.network.time_next_free_after(relay, *timing);
                    resources.network.schedule(relay, *timing, total_tx_delay);
                    *timing = start_time;
                }
                timings
            }
            Self::FirstShredInSlice(slice) => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                for (recipient, timing) in timings.iter_mut().enumerate() {
                    let first_shred_time = instance.relays[*slice]
                        .iter()
                        .map(|relay| {
                            let prop_delay =
                                environment.propagation_delay(*relay, recipient as ValidatorId);
                            let tx_delay = environment
                                .transmission_delay((recipient + 1) * MAX_DATA_PER_SHRED, *relay);
                            dependency_timings[0][*relay as usize] + prop_delay + tx_delay
                        })
                        .min()
                        .unwrap();
                    *timing = first_shred_time;
                }
                timings
            }
            Self::Rotor(slice) => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                let mut shred_timings = vec![SimTime::NEVER; instance.params.shreds];
                for (recipient, timing) in timings.iter_mut().enumerate() {
                    for (i, relay) in instance.relays[*slice].iter().enumerate() {
                        shred_timings[i] = dependency_timings[0][*relay as usize]
                            + environment.propagation_delay(*relay, recipient as ValidatorId)
                            + environment
                                .transmission_delay((recipient + 1) * MAX_DATA_PER_SHRED, *relay);
                    }
                    shred_timings.sort_unstable();
                    *timing = shred_timings[instance.params.data_shreds - 1];
                }
                timings
            }
            Self::FirstShred => column_min(dependency_timings),
            Self::Block => column_max(dependency_timings),
        }
    }
}
