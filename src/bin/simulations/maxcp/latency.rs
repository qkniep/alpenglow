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
    Timings,
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
            LatencyTestStage::BuildBlock => Some(LatencyTestStage::Reconstruct),
            LatencyTestStage::Reconstruct => Some(LatencyTestStage::Consensus),
            LatencyTestStage::Consensus => None,
        }
    }

    fn events(&self, _params: &Self::Params) -> Vec<LatencyEvent> {
        match self {
            LatencyTestStage::Propose => vec![LatencyEvent::Propose],
            LatencyTestStage::Attest => vec![LatencyEvent::Relay, LatencyEvent::Attest],
            LatencyTestStage::BuildBlock => vec![LatencyEvent::BuildBlock],
            LatencyTestStage::Reconstruct => vec![LatencyEvent::Reconstruct],
            LatencyTestStage::Consensus => vec![LatencyEvent::Consensus],
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
    Reconstruct,
    Consensus,
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
            Self::Reconstruct => "reconstruct",
            Self::Consensus => "consensus",
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
            Self::Attest => vec![Self::Relay],
            Self::BuildBlock => vec![Self::Attest],
            Self::Reconstruct => vec![Self::Relay],
            Self::Consensus => vec![Self::BuildBlock, Self::Reconstruct],
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
                // TODO: handle more than 1 batch
                for &proposer in &instance.proposers {
                    let batch_bytes = instance.params.slices_per_batch as usize
                        * instance.params.num_attestors as usize
                        * MAX_DATA_PER_SHRED;
                    let tx_time = environment.transmission_delay(batch_bytes, proposer);
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
                for (attestor_offset, &attestor) in instance.attestors.iter().enumerate() {
                    let mut shred_times = instance
                        .proposers
                        .iter()
                        .map(|proposer| {
                            let start_time = dependency_timings[0][*proposer as usize];
                            let shred_send_index = attestor_offset + 1;
                            let tx_time = environment.transmission_delay(
                                shred_send_index * MAX_DATA_PER_SHRED,
                                *proposer,
                            );
                            let prop_time = environment.propagation_delay(*proposer, attestor);
                            start_time + tx_time + prop_time
                        })
                        .collect::<Vec<_>>();
                    shred_times.sort_unstable();
                    let sent_time = shred_times
                        .iter()
                        .map(|recv_time| {
                            if !instance.params.quick_release {
                                let tx_time = environment.transmission_delay(
                                    instance.params.num_proposers as usize * MAX_DATA_PER_SHRED,
                                    attestor,
                                );
                                *recv_time + tx_time
                            } else {
                                // let shred_send_index = attestor_offset + 1;
                                let tx_time = environment.transmission_delay(
                                    instance.params.num_proposers as usize
                                        * environment.num_validators()
                                        * MAX_DATA_PER_SHRED,
                                    attestor,
                                );
                                *recv_time + tx_time
                            }
                        })
                        .max()
                        .unwrap();
                    timings[attestor as usize] = timings[attestor as usize].max(sent_time);
                }
                timings
            }
            Self::Attest => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                for attestor in &instance.attestors {
                    let attestation_bytes = instance.params.num_proposers.div_ceil(11) as usize;
                    let batch_time_secs = instance.params.slot_time.as_secs_f64()
                        / instance.params.num_batches as f64;
                    let send_time = dependency_timings[0][*attestor as usize]
                        .max(SimTime::from_secs(batch_time_secs));
                    timings[*attestor as usize] =
                        send_time + environment.transmission_delay(attestation_bytes, *attestor);
                }
                timings
            }
            Self::BuildBlock => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                let mut shred_timings =
                    vec![SimTime::NEVER; instance.params.num_attestors as usize];
                for (i, attestor) in instance.attestors.iter().enumerate() {
                    shred_timings[i] = dependency_timings[0][*attestor as usize]
                        + environment.propagation_delay(*attestor, instance.leader);
                }
                shred_timings.sort_unstable();
                timings[instance.leader as usize] =
                    shred_timings[instance.params.attestations_threshold as usize - 1];
                timings
            }
            Self::Reconstruct => {
                if !instance.params.quick_release {
                    return vec![SimTime::ZERO; environment.num_validators()];
                }

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
            Self::Consensus => {
                let consensus_start_time = dependency_timings[0][instance.leader as usize];
                // TODO: find better way of integrating sub-protocol
                let slices_required = if instance.params.quick_release {
                    instance.params.num_proposers.div_ceil(11)
                } else {
                    // instance.params.num_proposers.div_ceil(2)
                    instance.params.num_proposers.div_ceil(11)
                } as usize;
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
        }
    }
}
