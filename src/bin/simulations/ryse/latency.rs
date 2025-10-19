// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for Ryse, the MCP protocol.
//!
//! So far, this test can only simulate the happy path.

// TODO: lots of shared code with `rotor/latency` and `alpenglow/latency`

use std::hash::Hash;
use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::shredder::MAX_DATA_PER_SHRED;
use log::debug;
use rand::prelude::*;

use crate::discrete_event_simulator::{
    Builder, Event, Protocol, Resources, SimTime, SimulationEnvironment, Stage,
    broadcast_first_arrival_or_dep, broadcast_stake_threshold, column_max, column_min,
};
use crate::ryse::parameters::{RyseInstance, RyseInstanceBuilder, RyseParameters};

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;
/// Size (in bytes) assumed per certificate in the simulation.
const CERT_SIZE: usize = 128 /* sig */ + 256 /* bitmap */ + 64 /* slot, hash, flags */;

/// Marker type for the Ryse latency simulation.
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
    Direct,
    Rotor,
    Block,
    Notar,
    Final1,
    Final2,
}

impl Stage for LatencyTestStage {
    type Event = LatencyEvent;
    type Params = LatencySimParams;

    fn first() -> Self {
        Self::Direct
    }

    fn next(&self) -> Option<Self> {
        match self {
            Self::Direct => Some(Self::Rotor),
            Self::Rotor => Some(Self::Block),
            Self::Block => Some(Self::Notar),
            Self::Notar => Some(Self::Final1),
            Self::Final1 => Some(Self::Final2),
            Self::Final2 => None,
        }
    }

    fn events(&self, params: &LatencySimParams) -> Vec<LatencyEvent> {
        match self {
            Self::Direct => {
                let mut events = Vec::with_capacity(params.ryse_params.num_slices as usize + 1);
                events.push(LatencyEvent::BlockSent);
                for slice in 0..params.ryse_params.num_slices {
                    events.push(LatencyEvent::Direct(slice));
                }
                events
            }
            Self::Rotor => {
                let mut events = Vec::with_capacity(3 * params.ryse_params.num_slices as usize);
                for slice in 0..params.ryse_params.num_slices {
                    events.push(LatencyEvent::StartForwarding(slice));
                    events.push(LatencyEvent::FirstShredInSlice(slice));
                    events.push(LatencyEvent::Rotor(slice));
                }
                events
            }
            Self::Block => vec![LatencyEvent::FirstShred, LatencyEvent::Block],
            Self::Notar => vec![LatencyEvent::LocalNotar, LatencyEvent::Notar],
            Self::Final1 => vec![LatencyEvent::LocalFastFinal, LatencyEvent::LocalSlowFinal],
            Self::Final2 => vec![LatencyEvent::LocalFinal, LatencyEvent::Final],
        }
    }
}

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    // proposal dissemination
    BlockSent,
    Direct(u64),
    StartForwarding(u64),
    FirstShredInSlice(u64),
    Rotor(u64),
    FirstShred,
    Block,
    // consensus
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
            Self::BlockSent => "block_sent".to_owned(),
            Self::Direct(slice) => format!("direct_{slice}"),
            Self::StartForwarding(_) => "start_forwarding".to_owned(),
            Self::FirstShredInSlice(_) => "first_shred_in_slice".to_owned(),
            Self::Rotor(slice) => format!("rotor_{slice}"),
            Self::FirstShred => "first_shred".to_owned(),
            Self::Block => "block".to_owned(),
            Self::LocalNotar => "local_notar".to_owned(),
            Self::Notar => "notar".to_owned(),
            Self::LocalFastFinal => "local_fast_final".to_owned(),
            Self::LocalSlowFinal => "local_slow_final".to_owned(),
            Self::LocalFinal => "local_final".to_owned(),
            Self::Final => "final".to_owned(),
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
            _ => true,
        }
    }

    fn dependencies(&self, params: &LatencySimParams) -> Vec<Self> {
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
            Self::FirstShred => (0..params.ryse_params.num_slices)
                .map(Self::FirstShredInSlice)
                .collect(),
            Self::Block => (0..params.ryse_params.num_slices)
                .map(Self::Rotor)
                .collect(),

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
            Self::BlockSent => {
                let mut timings = vec![start_time; environment.num_validators()];
                // TODO: actually run for more than 1 slot
                for &leader in instance.ryse_instances[0].leaders.iter() {
                    let block_bytes = instance.params.ryse_params.num_slices as usize
                        * instance.params.ryse_params.num_relays as usize
                        * MAX_DATA_PER_SHRED;
                    let tx_time = environment.transmission_delay(block_bytes, leader);
                    let finished_sending_time =
                        resources.network.schedule(leader, start_time, tx_time);
                    timings[leader as usize] += finished_sending_time;
                }
                timings
            }
            Self::Direct(slice) => {
                let mut timings = vec![SimTime::ZERO; environment.num_validators()];
                // TODO: actually run for more than 1 slot
                let slice_relays = &instance.ryse_instances[0].relays[*slice as usize];
                for (relay_offset, &relay) in slice_relays.iter().enumerate() {
                    // TODO: correctly handle validators that are relays more than once
                    let shreds_from_all_leaders = instance.ryse_instances[0]
                        .leaders
                        .iter()
                        .map(|leader| {
                            let prop_delay = environment.propagation_delay(*leader, relay);
                            let shred_send_index = slice * instance.params.ryse_params.num_relays
                                + (relay_offset + 1) as u64;
                            let tx_delay = environment.transmission_delay(
                                shred_send_index as usize * MAX_DATA_PER_SHRED,
                                *leader,
                            );
                            start_time + prop_delay + tx_delay
                        })
                        .max()
                        .unwrap();
                    timings[relay as usize] = timings[relay as usize].max(shreds_from_all_leaders);
                }
                // TODO: remove this again
                let mut relay_timings = slice_relays
                    .iter()
                    .map(|&relay| timings[relay as usize])
                    .collect::<Vec<_>>();
                relay_timings.sort_unstable();
                debug!(
                    "p50 relay received proposals at: {}",
                    relay_timings[relay_timings.len() / 2]
                );
                timings
            }
            Self::StartForwarding(slice) => {
                let mut timings = dependency_timings[0].to_vec();
                // TODO: actually run for more than 1 slot
                for &relay in &instance.ryse_instances[0].relays[*slice as usize] {
                    let timing = &mut timings[relay as usize];
                    let total_bytes = instance.params.ryse_params.num_leaders as usize
                        * environment.num_validators()
                        * MAX_DATA_PER_SHRED;
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
                    // TODO: actually run for more than 1 slot
                    let first_shred_time = instance.ryse_instances[0].relays[*slice as usize]
                        .iter()
                        .map(|relay| {
                            let prop_delay =
                                environment.propagation_delay(*relay, recipient as ValidatorId);
                            let tx_delay = environment.transmission_delay(
                                (recipient + 1)
                                    * instance.params.ryse_params.num_leaders as usize
                                    * MAX_DATA_PER_SHRED,
                                *relay,
                            );
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
                let mut shred_timings =
                    vec![SimTime::NEVER; instance.params.ryse_params.num_relays as usize];
                for (recipient, timing) in timings.iter_mut().enumerate() {
                    // TODO: actually run for more than 1 slot
                    let slice_relays = &instance.ryse_instances[0].relays[*slice as usize];
                    for (i, relay) in slice_relays.iter().enumerate() {
                        shred_timings[i] = dependency_timings[0][*relay as usize]
                            + environment.propagation_delay(*relay, recipient as ValidatorId)
                            + environment.transmission_delay(
                                (recipient + 1)
                                    * instance.params.ryse_params.num_leaders as usize
                                    * MAX_DATA_PER_SHRED,
                                *relay,
                            );
                    }
                    shred_timings.sort_unstable();
                    *timing =
                        shred_timings[instance.params.ryse_params.decode_threshold as usize - 1];
                }
                timings
            }
            Self::FirstShred => column_min(dependency_timings),
            Self::Block => column_max(dependency_timings),

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

/// Parameters for the Ryse latency simulation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LatencySimParams {
    ryse_params: RyseParameters,
    num_slots_per_window: usize,
    num_slots: usize,
}

impl LatencySimParams {
    /// Creates a parameter set for the Ryse latency simulation.
    pub fn new(ryse_params: RyseParameters, num_slots_per_window: usize, num_slots: usize) -> Self {
        Self {
            ryse_params,
            num_slots_per_window,
            num_slots,
        }
    }
}

/// A builder for Ryse latency simulation instances.
pub struct LatencySimInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    ryse_builder: RyseInstanceBuilder<L, R>,
    params: LatencySimParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencySimInstanceBuilder<L, R> {
    /// Creates a new builder instance from a builder for Rotor instances.
    pub fn new(ryse_builder: RyseInstanceBuilder<L, R>, params: LatencySimParams) -> Self {
        Self {
            ryse_builder,
            params,
        }
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> Builder for LatencySimInstanceBuilder<L, R> {
    type Params = LatencySimParams;
    type Instance = LatencySimInstance;

    fn build(&self, rng: &mut impl Rng) -> LatencySimInstance {
        let ryse_instances = (0..self.params.num_slots)
            .map(|_| self.ryse_builder.build(rng))
            .collect();
        LatencySimInstance {
            ryse_instances,
            params: self.params.clone(),
        }
    }

    fn params(&self) -> &Self::Params {
        &self.params
    }
}

/// A specific instance of the Ryse latency simulation.
///
/// Contains one instance of the Ryse protocol, [`RyseInstance`], per slot.
pub struct LatencySimInstance {
    ryse_instances: Vec<RyseInstance>,
    params: LatencySimParams,
}
