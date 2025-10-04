// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Latency simulation for Pyjama, the MCP protocol.
//!
//! So far, this test can only simulate the happy path.

use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use alpenglow::shredder::MAX_DATA_PER_SHRED;

use super::{PyjamaInstance, PyjamaInstanceBuilder, PyjamaParams};
use crate::discrete_event_simulator::{Builder, Resources, SimulationEngine, Timings};
use crate::rotor::RotorParams;
use crate::{
    alpenglow::AlpenglowLatencySimulation,
    discrete_event_simulator::{Event, Protocol, SimTime, SimulationEnvironment, Stage},
};

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
            LatencyTestStage::Reconstruct => vec![LatencyEvent::Reconstruct],
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
    Reconstruct,
}

impl Event for LatencyEvent {
    type Params = PyjamaParams;
    type Instance = PyjamaInstance;

    fn name(&self) -> String {
        match self {
            LatencyEvent::Propose => "propose",
            LatencyEvent::Relay => "relay",
            LatencyEvent::Attestation => "attestation",
            LatencyEvent::Consensus => "consensus",
            LatencyEvent::Reconstruct => "reconstruct",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        true
    }

    fn dependencies(&self, _params: &PyjamaParams) -> Vec<LatencyEvent> {
        match self {
            LatencyEvent::Propose => vec![],
            LatencyEvent::Relay => vec![LatencyEvent::Propose],
            LatencyEvent::Attestation => vec![LatencyEvent::Relay],
            LatencyEvent::Consensus => vec![LatencyEvent::Attestation],
            LatencyEvent::Reconstruct => vec![LatencyEvent::Consensus],
        }
    }

    fn calculate_timing(
        &self,
        dependency_timings: &[&[SimTime]],
        instance: &PyjamaInstance,
        _resources: &mut Resources,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        match self {
            LatencyEvent::Propose => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                timings
            }
            LatencyEvent::Relay => {
                let mut timings = vec![SimTime::NEVER; environment.num_validators()];
                timings[instance.leader as usize] = SimTime::ZERO;
                let block_bytes =
                    1 /* num_slices */ * instance.params.num_relays as usize * MAX_DATA_PER_SHRED;
                timings[instance.leader as usize] +=
                    environment.transmission_delay(block_bytes, instance.leader);
                timings
            }
            LatencyEvent::Attestation => vec![SimTime::ZERO; environment.num_validators()],
            // LatencyEvent::Attestation => {
            //     let mut timings = dependency_timings[0].to_vec();
            //     for recipient in 0..environment.num_validators() {
            //         // TODO: reserve network resource
            //         let first_shred_time = instance.relays[*slice]
            //             .iter()
            //             .map(|relay| {
            //                 let prop_delay =
            //                     environment.propagation_delay(*relay, recipient as ValidatorId);
            //                 let tx_delay = environment
            //                     .transmission_delay((recipient + 1) * MAX_DATA_PER_SHRED, *relay);
            //                 timings[*relay as usize] + prop_delay + tx_delay
            //             })
            //             .min()
            //             .unwrap();
            //         timings[recipient] = first_shred_time;
            //     }
            //     timings
            // }
            LatencyEvent::Consensus => {
                // TODO: find better way of integrating sub-protocol
                let rotor_params = RotorParams {
                    num_data_shreds: instance.params.can_decode_threshold as usize,
                    num_shreds: instance.params.num_relays as usize,
                    num_slices: 1,
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
                let mut timings = Timings::default();
                engine.run(&consensus_instance, &mut timings);
                timings
                    .get(crate::alpenglow::LatencyEvent::Final)
                    .unwrap()
                    .to_vec()
            }
            LatencyEvent::Reconstruct => vec![SimTime::ZERO; environment.num_validators()],
        }
    }
}
