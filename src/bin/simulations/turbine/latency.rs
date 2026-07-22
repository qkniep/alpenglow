// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for the Turbine block dissemination protocol.
//!
//!

use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::shredder::MAX_DATA_PER_SHRED;

use super::{TurbineInstance, TurbineInstanceBuilder, TurbineParams};
use crate::discrete_event_simulator::{
    Event, Protocol, Resources, SimTime, SimulationEnvironment, Stage, column_max, column_min,
};

/// Wrapper type for the Turbine latency simulation.
///
/// This type implements the `Protocol` trait and can be passed to the simulation engine.
/// There is probably never a need to construct this type directly.
pub struct TurbineLatencySimulation<L: SamplingStrategy> {
    _leader_sampler: PhantomData<L>,
}

impl<L: SamplingStrategy> Protocol for TurbineLatencySimulation<L> {
    type Event = LatencyEvent;
    type Stage = LatencyTestStage;
    type Params = TurbineParams;
    type Instance = TurbineInstance;
    type Builder = TurbineInstanceBuilder<L>;
}

/// Stages of the Turbine latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Direct,
    Turbine,
    Block,
}

impl Stage for LatencyTestStage {
    type Event = LatencyEvent;
    type Params = TurbineParams;

    fn first() -> Self {
        LatencyTestStage::Direct
    }

    fn next(&self) -> Option<Self> {
        match self {
            LatencyTestStage::Direct => Some(LatencyTestStage::Turbine),
            LatencyTestStage::Turbine => Some(LatencyTestStage::Block),
            LatencyTestStage::Block => None,
        }
    }

    fn events(&self, params: &Self::Params) -> Vec<LatencyEvent> {
        match self {
            LatencyTestStage::Direct => {
                let mut events = Vec::with_capacity(params.num_slices + 1);
                events.push(LatencyEvent::BlockSent);
                for slice in 0..params.num_slices {
                    events.push(LatencyEvent::DirectRoot(slice));
                }
                events
            }
            LatencyTestStage::Turbine => {
                let mut events = Vec::with_capacity(5 * params.num_slices);
                for slice in 0..params.num_slices {
                    events.push(LatencyEvent::StartForwardingRoot(slice));
                    events.push(LatencyEvent::DirectL1(slice));
                    events.push(LatencyEvent::StartForwardingL1(slice));
                    events.push(LatencyEvent::FirstShredInSlice(slice));
                    events.push(LatencyEvent::Turbine(slice));
                }
                events
            }
            LatencyTestStage::Block => vec![LatencyEvent::FirstShred, LatencyEvent::Block],
        }
    }
}

/// Events that can occur at each validator during the Turbine latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    BlockSent,
    DirectRoot(usize),
    StartForwardingRoot(usize),
    DirectL1(usize),
    StartForwardingL1(usize),
    FirstShredInSlice(usize),
    Turbine(usize),
    FirstShred,
    Block,
}

impl Event for LatencyEvent {
    type Params = TurbineParams;
    type Instance = TurbineInstance;

    fn name(&self) -> String {
        match self {
            Self::BlockSent => "block_sent".to_owned(),
            Self::DirectRoot(slice) => format!("direct_root_{}", slice),
            Self::StartForwardingRoot(_) => "start_forwarding_root".to_owned(),
            Self::DirectL1(slice) => format!("direct_l1_{}", slice),
            Self::StartForwardingL1(_) => "start_forwarding_l1".to_owned(),
            Self::FirstShredInSlice(_) => "first_shred_in_slice".to_owned(),
            Self::Turbine(slice) => format!("rotor_{}", slice),
            Self::FirstShred => "first_shred".to_owned(),
            Self::Block => "block".to_owned(),
        }
    }

    fn should_track_stats(&self) -> bool {
        match self {
            Self::BlockSent => true,
            Self::DirectRoot(slice) => *slice == 0,
            Self::StartForwardingRoot(_) => false,
            Self::DirectL1(slice) => *slice == 0,
            Self::StartForwardingL1(_) => false,
            Self::FirstShredInSlice(_) => false,
            Self::Turbine(slice) => *slice == 0,
            Self::FirstShred => true,
            Self::Block => true,
        }
    }

    fn dependencies(&self, params: &TurbineParams) -> Vec<Self> {
        match self {
            Self::BlockSent => vec![],
            Self::DirectRoot(slice) => {
                if *slice == 0 {
                    vec![]
                } else {
                    vec![Self::DirectRoot(*slice - 1)]
                }
            }
            Self::StartForwardingRoot(slice) => vec![Self::DirectRoot(*slice)],
            Self::DirectL1(slice) => {
                if *slice == 0 {
                    vec![Self::StartForwardingRoot(*slice)]
                } else {
                    vec![
                        Self::StartForwardingRoot(*slice),
                        Self::DirectL1(*slice - 1),
                    ]
                }
            }
            Self::StartForwardingL1(slice) => vec![Self::DirectL1(*slice)],
            Self::FirstShredInSlice(slice) => {
                vec![
                    Self::StartForwardingRoot(*slice),
                    Self::StartForwardingL1(*slice),
                ]
            }
            Self::Turbine(slice) => vec![
                Self::StartForwardingRoot(*slice),
                Self::StartForwardingL1(*slice),
            ],
            Self::FirstShred => (0..params.num_slices)
                .map(Self::FirstShredInSlice)
                .collect(),
            Self::Block => (0..params.num_slices).map(Self::Turbine).collect(),
        }
    }

    fn calculate_timing(
        &self,
        dependency_timings: &[&[SimTime]],
        instance: &TurbineInstance,
        resources: &mut Resources,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        match self {
            Self::BlockSent => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                let block_bytes =
                    instance.params.num_slices * instance.params.num_shreds * MAX_DATA_PER_SHRED;
                let tx_time = environment.transmission_delay(block_bytes, instance.leader);
                let finished_sending_time =
                    resources
                        .network
                        .schedule(instance.leader, SimTime::ZERO, tx_time);
                timings[instance.leader as usize] = finished_sending_time;
                timings
            }
            Self::DirectRoot(slice) => {
                let mut timings = (0..environment.num_validators() as ValidatorId)
                    .map(|recipient| environment.propagation_delay(instance.leader, recipient))
                    .collect::<Vec<_>>();
                for (shred_index, &root) in instance.roots(*slice).iter().enumerate() {
                    let shred_send_index = slice * instance.params.num_shreds + shred_index + 1;
                    let tx_delay = environment
                        .transmission_delay(shred_send_index * MAX_DATA_PER_SHRED, instance.leader);
                    timings[root as usize] += tx_delay;
                }
                timings
            }
            Self::StartForwardingRoot(slice) => {
                let mut timings = dependency_timings[0].to_vec();
                for (shred_index, &root) in instance.roots(*slice).iter().enumerate() {
                    let timing = &mut timings[root as usize];
                    let total_bytes = environment.num_validators() * MAX_DATA_PER_SHRED;
                    let total_tx_delay = environment.transmission_delay(total_bytes, root);
                    let start_time = resources.network.time_next_free_after(root, *timing);
                    resources.network.schedule(root, *timing, total_tx_delay);
                    *timing = start_time;
                }
                timings
            }
            Self::DirectL1(slice) => {
                // TODO:
                let mut timings = (0..environment.num_validators() as ValidatorId)
                    .map(|recipient| environment.propagation_delay(instance.leader, recipient))
                    .collect::<Vec<_>>();
                for relay in &instance.relays[*slice] {
                    let shred_send_index =
                        slice * instance.params.num_shreds + (*relay as usize) + 1;
                    let tx_delay = environment
                        .transmission_delay(shred_send_index * MAX_DATA_PER_SHRED, instance.leader);
                    timings[*relay as usize] += tx_delay;
                }
                timings
            }
            Self::StartForwardingL1(slice) => {
                // TODO:
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
            Self::Turbine(slice) => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                let mut shred_timings = vec![SimTime::NEVER; instance.params.num_shreds];
                for (recipient, timing) in timings.iter_mut().enumerate() {
                    for (i, relay) in instance.relays[*slice].iter().enumerate() {
                        shred_timings[i] = dependency_timings[0][*relay as usize]
                            + environment.propagation_delay(*relay, recipient as ValidatorId)
                            + environment
                                .transmission_delay((recipient + 1) * MAX_DATA_PER_SHRED, *relay);
                    }
                    shred_timings.sort_unstable();
                    *timing = shred_timings[instance.params.num_data_shreds - 1];
                }
                timings
            }
            Self::FirstShred => column_min(dependency_timings),
            Self::Block => column_max(dependency_timings),
        }
    }
}
