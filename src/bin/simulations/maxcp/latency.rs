// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for MaxCP, the MCP protocol.
//!
//! So far, this test can only simulate the happy path.

use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::shredder::{DATA_SHREDS, MAX_DATA_PER_SHRED, TOTAL_SHREDS};

use super::{MaxcpInstance, MaxcpInstanceBuilder, MaxcpParams};
use crate::alpenglow::AlpenglowLatencySimulation;
use crate::discrete_event_simulator::{
    Builder, Event, Protocol, Resources, SimTime, SimulationEngine, SimulationEnvironment, Stage,
    Timings, column_max,
};
use crate::rotor::RotorParams;

/// Wrapper type for the Maxcp latency simulation.
///
/// This type implements the `Protocol` trait and can be passed to the simulation engine.
/// There is probably never a need to construct this type directly.
pub struct MaxcpLatencySimulation<
    L: SamplingStrategy,
    P: SamplingStrategy,
    A: SamplingStrategy,
    R: SamplingStrategy,
> {
    _leader_sampler: PhantomData<L>,
    _proposer_sampler: PhantomData<P>,
    _attestor_sampler: PhantomData<A>,
    _rotor_sampler: PhantomData<R>,
}

impl<L, P, A, R> Protocol for MaxcpLatencySimulation<L, P, A, R>
where
    L: SamplingStrategy,
    P: SamplingStrategy,
    A: SamplingStrategy,
    R: SamplingStrategy,
{
    type Event = LatencyEvent;
    type Stage = LatencyTestStage;
    type Params = MaxcpParams;
    type Instance = MaxcpInstance;
    type Builder = MaxcpInstanceBuilder<L, P, A, R>;
}

/// Stages of the MaxCP latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Propose,
    Attest,
    BuildBlock,
    Reconstruct,
    Consensus,
}

impl Stage for LatencyTestStage {
    type Event = LatencyEvent;
    type Params = MaxcpParams;

    fn first() -> Self {
        LatencyTestStage::Propose
    }

    fn next(&self) -> Option<Self> {
        match self {
            LatencyTestStage::Propose => Some(LatencyTestStage::Attest),
            LatencyTestStage::Attest => Some(LatencyTestStage::BuildBlock),
            LatencyTestStage::BuildBlock => Some(LatencyTestStage::Consensus),
            LatencyTestStage::Consensus => Some(LatencyTestStage::Reconstruct),
            LatencyTestStage::Reconstruct => None,
        }
    }

    fn events(&self, _params: &Self::Params) -> Vec<LatencyEvent> {
        match self {
            LatencyTestStage::Propose => vec![LatencyEvent::Propose],
            LatencyTestStage::Attest => vec![LatencyEvent::Relay, LatencyEvent::Attest],
            LatencyTestStage::BuildBlock => vec![LatencyEvent::BuildBlock],
            LatencyTestStage::Consensus => vec![LatencyEvent::Consensus],
            LatencyTestStage::Reconstruct => vec![LatencyEvent::Reconstruct, LatencyEvent::Final],
        }
    }
}

/// Events that can occur at each validator during the MaxCP latency simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Propose,
    Relay,
    Attest,
    BuildBlock,
    Consensus,
    Reconstruct,
    Final,
}

impl Event for LatencyEvent {
    type Params = MaxcpParams;
    type Instance = MaxcpInstance;

    fn name(&self) -> String {
        match self {
            Self::Propose => "propose",
            Self::Relay => "relay",
            Self::Attest => "attest",
            Self::BuildBlock => "build_block",
            Self::Consensus => "consensus",
            Self::Reconstruct => "reconstruct",
            Self::Final => "final",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        true
    }

    fn dependencies(&self, _params: &MaxcpParams) -> Vec<Self> {
        match self {
            Self::Propose => vec![],
            Self::Relay => vec![Self::Propose],
            Self::Attest => vec![Self::Propose],
            Self::BuildBlock => vec![Self::Attest],
            Self::Consensus => vec![Self::BuildBlock],
            Self::Reconstruct => vec![Self::Relay],
            Self::Final => vec![Self::Consensus, Self::Reconstruct],
        }
    }

    fn calculate_timing(
        &self,
        start_time: SimTime,
        dependency_timings: &[&[SimTime]],
        instance: &MaxcpInstance,
        resources: &mut Resources,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        match self {
            Self::Propose => {
                let mut timings = vec![start_time; environment.num_validators()];
                for &proposer in &instance.proposers {
                    let block_bytes =
                        (instance.params.num_batches * instance.params.slices_per_batch) as usize
                            * instance.params.num_attestors as usize
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
            Self::Attest => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                timings
            }
            Self::BuildBlock => {
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
                    *timing =
                        shred_timings[instance.params.can_decode_proposal_threshold as usize - 1];
                }
                timings
            }
            Self::Final => column_max(dependency_timings),
        }
    }
}
