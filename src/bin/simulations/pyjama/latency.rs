// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for Pyjama, the MCP protocol.
//!
//! So far, this test can only simulate the happy path.

use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::shredder::{DATA_SHREDS, MAX_DATA_PER_SHRED, TOTAL_SHREDS};

use super::{PyjamaInstance, PyjamaInstanceBuilder, PyjamaParams};
use crate::alpenglow::AlpenglowLatencySimulation;
use crate::discrete_event_simulator::{
    Builder, Event, Protocol, Resources, SimTime, SimulationEngine, SimulationEnvironment, Stage,
    Timings, column_max,
};
use crate::rotor::RotorParams;

/// Wrapper type for the Pyjama latency simulation.
///
/// This type implements the `Protocol` trait and can be passed to the simulation engine.
/// There is probably never a need to construct this type directly.
pub struct PyjamaLatencySimulation<L: SamplingStrategy, P: SamplingStrategy, R: SamplingStrategy> {
    _leader_sampler: PhantomData<L>,
    _proposer_sampler: PhantomData<P>,
    _rotor_sampler: PhantomData<R>,
}

impl<L, P, R> Protocol for PyjamaLatencySimulation<L, P, R>
where
    L: SamplingStrategy,
    P: SamplingStrategy,
    R: SamplingStrategy,
{
    type Event = LatencyEvent;
    type Stage = LatencyTestStage;
    type Params = PyjamaParams;
    type Instance = PyjamaInstance;
    type Builder = PyjamaInstanceBuilder<L, P, R>;
}

/// Stages of the Pyjama latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Propose,
    Relay,
    Attestation,
    Consensus,
    Reconstruct,
}

impl Stage for LatencyTestStage {
    type Event = LatencyEvent;
    type Params = PyjamaParams;

    fn first() -> Self {
        LatencyTestStage::Propose
    }

    fn next(&self) -> Option<Self> {
        match self {
            LatencyTestStage::Propose => Some(LatencyTestStage::Relay),
            LatencyTestStage::Relay => Some(LatencyTestStage::Attestation),
            LatencyTestStage::Attestation => Some(LatencyTestStage::Consensus),
            LatencyTestStage::Consensus => Some(LatencyTestStage::Reconstruct),
            LatencyTestStage::Reconstruct => None,
        }
    }

    fn events(&self, _params: &Self::Params) -> Vec<LatencyEvent> {
        match self {
            LatencyTestStage::Propose => vec![LatencyEvent::Propose],
            LatencyTestStage::Relay => vec![LatencyEvent::Relay],
            LatencyTestStage::Attestation => vec![LatencyEvent::Attestation],
            LatencyTestStage::Consensus => vec![LatencyEvent::Consensus],
            LatencyTestStage::Reconstruct => vec![
                LatencyEvent::Release,
                LatencyEvent::Reconstruct,
                LatencyEvent::Final,
            ],
        }
    }
}

/// Events that can occur at each validator during the Pyjama latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Propose,
    Relay,
    Attestation,
    Consensus,
    Release,
    Reconstruct,
    Final,
}

impl Event for LatencyEvent {
    type Params = PyjamaParams;
    type Instance = PyjamaInstance;

    fn name(&self) -> String {
        match self {
            Self::Propose => "propose",
            Self::Relay => "relay",
            Self::Attestation => "attestation",
            Self::Consensus => "consensus",
            Self::Release => "release",
            Self::Reconstruct => "reconstruct",
            Self::Final => "final",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        true
    }

    fn dependencies(&self, _params: &PyjamaParams) -> Vec<Self> {
        match self {
            Self::Propose => vec![],
            Self::Relay => vec![Self::Propose],
            Self::Attestation => vec![Self::Relay],
            Self::Consensus => vec![Self::Attestation],
            Self::Release => vec![Self::Consensus],
            Self::Reconstruct => vec![Self::Release],
            Self::Final => vec![Self::Consensus, Self::Reconstruct],
        }
    }

    fn calculate_timing(
        &self,
        start_time: SimTime,
        dependency_timings: &[&[SimTime]],
        instance: &PyjamaInstance,
        resources: &mut Resources,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        match self {
            Self::Propose => {
                let mut timings = vec![start_time; environment.num_validators()];
                for &proposer in &instance.proposers {
                    let block_bytes = instance.params.num_slices as usize
                        * instance.params.num_relays as usize
                        * MAX_DATA_PER_SHRED;
                    let tx_time = environment.transmission_delay(block_bytes, proposer);
                    let start_sending_time =
                        resources.network.time_next_free_after(proposer, start_time);
                    resources.network.schedule(proposer, start_time, tx_time);
                    timings[proposer as usize] = start_sending_time;
                }
                timings
            }
            Self::Relay => {
                let mut timings = vec![SimTime::ZERO; environment.num_validators()];
                // TODO: actually run for more than 1 slot
                for (relay_offset, &relay) in instance.relays.iter().enumerate() {
                    let shreds_from_all_proposers = instance
                        .proposers
                        .iter()
                        .map(|proposer| {
                            let start_send_time = dependency_timings[0][*proposer as usize];
                            let prop_delay = environment.propagation_delay(*proposer, relay);
                            let shred_send_index = relay_offset + 1;
                            let tx_delay = environment.transmission_delay(
                                shred_send_index * MAX_DATA_PER_SHRED,
                                *proposer,
                            );
                            start_send_time + prop_delay + tx_delay
                        })
                        .max()
                        .unwrap();
                    timings[relay as usize] =
                        timings[relay as usize].max(shreds_from_all_proposers);
                }
                timings
            }
            Self::Attestation => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                let mut shred_timings = vec![SimTime::NEVER; instance.params.num_relays as usize];
                for (i, relay) in instance.relays.iter().enumerate() {
                    shred_timings[i] = dependency_timings[0][*relay as usize]
                        + environment.propagation_delay(*relay, instance.leader)
                        + environment.transmission_delay(MAX_DATA_PER_SHRED, *relay);
                }
                shred_timings.sort_unstable();
                timings[instance.leader as usize] =
                    shred_timings[instance.params.attestations_threshold as usize - 1];
                timings
            }
            Self::Consensus => {
                let consensus_start_time = dependency_timings[0][instance.leader as usize];
                // TODO: find better way of integrating sub-protocol
                let slices_required = 3;
                let rotor_params = RotorParams {
                    data_shreds: DATA_SHREDS,
                    shreds: TOTAL_SHREDS,
                    slices: slices_required,
                };
                let rotor_builder = crate::rotor::RotorInstanceBuilder::new(
                    StakeWeightedSampler::new(environment.validators.clone()),
                    StakeWeightedSampler::new(environment.validators.clone()),
                    rotor_params,
                );
                let builder = crate::alpenglow::LatencySimInstanceBuilder::new(
                    rotor_builder,
                    crate::alpenglow::LatencySimParams::new(rotor_params, 4, 1),
                );
                let consensus_instance = builder.build(&mut rand::rng());
                let engine = SimulationEngine::<AlpenglowLatencySimulation<_, _>>::new(
                    builder,
                    environment.clone(),
                );
                let mut timings = Timings::new(consensus_start_time);
                engine.run(&consensus_instance, &mut timings);
                timings
                    .get(crate::alpenglow::LatencyEvent::Final)
                    .unwrap()
                    .to_vec()
            }
            Self::Release => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                for relay in &instance.relays {
                    let dep_time = dependency_timings[0][*relay as usize];
                    let block_bytes = environment.num_validators()
                        * instance.params.num_proposers as usize
                        * MAX_DATA_PER_SHRED;
                    let tx_time = environment.transmission_delay(block_bytes, *relay);
                    let start_sending_time =
                        resources.network.time_next_free_after(*relay, dep_time);
                    resources.network.schedule(*relay, dep_time, tx_time);
                    timings[*relay as usize] = start_sending_time;
                }
                timings
            }
            Self::Reconstruct => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                let mut shred_timings = vec![SimTime::NEVER; instance.params.num_relays as usize];
                for (recipient, timing) in timings.iter_mut().enumerate() {
                    for (i, relay) in instance.relays.iter().enumerate() {
                        shred_timings[i] = dependency_timings[0][*relay as usize]
                            + environment.propagation_delay(*relay, recipient as ValidatorId)
                            + environment.transmission_delay(
                                (recipient + 1)
                                    * instance.params.num_proposers as usize
                                    * MAX_DATA_PER_SHRED,
                                *relay,
                            );
                    }
                    shred_timings.sort_unstable();
                    *timing = shred_timings[instance.params.can_decode_threshold as usize - 1];
                }
                timings
            }
            Self::Final => column_max(dependency_timings),
        }
    }
}
