// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for the Alpenglow protocol.
//!
//! So far, this test can only simulate the good case.

use std::hash::Hash;
use std::marker::PhantomData;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use rand::prelude::*;

use crate::discrete_event_simulator::{
    Builder, Event, Protocol, Resources, SimTime, SimulationEngine, SimulationEnvironment, Stage,
    Timings, column_min,
};
use crate::rotor::{RotorInstance, RotorInstanceBuilder, RotorLatencySimulation, RotorParams};

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;
/// Size (in bytes) assumed per certificate in the simulation.
const CERT_SIZE: usize = 128 /* sig */ + 256 /* bitmap */ + 64 /* slot, hash, flags */;

/// Marker type for the Alpenglow latency simulation.
pub struct AlpenglowLatencySimulation<L: SamplingStrategy, R: SamplingStrategy> {
    _leader_sampler: PhantomData<L>,
    _rotor_sampler: PhantomData<R>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> Protocol for AlpenglowLatencySimulation<L, R> {
    type Event = LatencyEvent;
    type Stage = LatencyTestStage;
    type Params = LatencySimParams;
    type Instance = LatencySimInstance;
    type Builder = LatencySimInstanceBuilder<L, R>;
}

/// The sequential stages of the latency test.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Rotor,
    Notar,
    Final1,
    Final2,
}

impl Stage for LatencyTestStage {
    type Event = LatencyEvent;
    type Params = LatencySimParams;

    fn first() -> Self {
        Self::Rotor
    }

    fn next(&self) -> Option<Self> {
        match self {
            Self::Rotor => Some(Self::Notar),
            Self::Notar => Some(Self::Final1),
            Self::Final1 => Some(Self::Final2),
            Self::Final2 => None,
        }
    }

    fn events(&self, _params: &Self::Params) -> Vec<LatencyEvent> {
        match self {
            Self::Rotor => vec![LatencyEvent::Block],
            Self::Notar => vec![LatencyEvent::LocalNotar, LatencyEvent::Notar],
            Self::Final1 => vec![LatencyEvent::LocalFastFinal, LatencyEvent::LocalSlowFinal],
            Self::Final2 => vec![LatencyEvent::LocalFinal, LatencyEvent::Final],
        }
    }
}

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Block,
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
            Self::Block => "block",
            Self::LocalNotar => "local_notar",
            Self::Notar => "notar",
            Self::LocalFastFinal => "local_fast_final",
            Self::LocalSlowFinal => "local_slow_final",
            Self::LocalFinal => "local_final",
            Self::Final => "final",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        true
    }

    // TODO: simulate actual circular dependency (of certs and status)
    fn dependencies(&self, _params: &LatencySimParams) -> Vec<Self> {
        match self {
            Self::Block => vec![],
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
        dependency_timings: &[&[SimTime]],
        instance: &LatencySimInstance,
        resources: &mut Resources,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        // reserve the network resource
        // TODO: find a more automated way of doing this
        match self {
            Self::LocalNotar => {
                for sender in 0..environment.num_validators() {
                    let total_tx_time = environment.transmission_delay(
                        environment.num_validators() * VOTE_SIZE,
                        sender as ValidatorId,
                    );
                    resources.network.schedule(
                        sender as ValidatorId,
                        dependency_timings[0][sender],
                        total_tx_time,
                    );
                }
            }
            Self::Notar => {
                for sender in 0..environment.num_validators() {
                    let total_tx_time = environment.transmission_delay(
                        environment.num_validators() * CERT_SIZE,
                        sender as ValidatorId,
                    );
                    resources.network.schedule(
                        sender as ValidatorId,
                        dependency_timings[0][sender],
                        total_tx_time,
                    );
                }
            }
            _ => (),
        }

        let broadcast_vote_threshold = |threshold: f64| -> Vec<SimTime> {
            let mut timings = dependency_timings[0].to_vec();

            // determine the start time for sending votes
            let start_send_vote_timings = dependency_timings[0]
                .iter()
                .enumerate()
                .map(|(sender, sender_timing)| {
                    resources
                        .network
                        .time_next_free_after(sender as ValidatorId, *sender_timing)
                })
                .collect::<Vec<_>>();

            for (recipient, recipient_timing) in timings.iter_mut().enumerate() {
                // calculate vote arrival timings
                let mut vote_timings = start_send_vote_timings
                    .iter()
                    .enumerate()
                    .map(|(sender, start_send)| {
                        let prop_delay = environment
                            .propagation_delay(sender as ValidatorId, recipient as ValidatorId);
                        let tx_delay = environment
                            .transmission_delay((recipient + 1) * VOTE_SIZE, sender as ValidatorId);
                        (*start_send + prop_delay + tx_delay, sender)
                    })
                    .collect::<Vec<_>>();

                // find time the stake threshold is first reached
                vote_timings.sort_unstable();
                let mut stake_so_far = 0;
                for (vote_timing, sender) in vote_timings.into_iter() {
                    *recipient_timing = vote_timing;
                    stake_so_far += environment.validators[sender].stake;
                    if stake_so_far as f64 >= threshold * environment.total_stake as f64 {
                        break;
                    }
                }
            }
            timings
        };

        let local_or_cert = |dependency_timings: &[&[SimTime]]| -> Vec<SimTime> {
            let mut timings = dependency_timings[0].to_vec();

            // reserve network for cert sending
            let start_send_cert_timings = dependency_timings[0]
                .iter()
                .enumerate()
                .map(|(sender, sender_timing)| {
                    resources
                        .network
                        .time_next_free_after(sender as ValidatorId, *sender_timing)
                })
                .collect::<Vec<_>>();

            for (recipient, recipient_timing) in timings.iter_mut().enumerate() {
                // calculate cert arrival timings
                let first_cert_arrival_time = start_send_cert_timings
                    .iter()
                    .enumerate()
                    .map(|(sender, start_send)| {
                        let prop_delay = environment
                            .propagation_delay(sender as ValidatorId, recipient as ValidatorId);
                        let tx_delay = environment
                            .transmission_delay((recipient + 1) * CERT_SIZE, sender as ValidatorId);
                        *start_send + prop_delay + tx_delay
                    })
                    .min()
                    .unwrap();
                if first_cert_arrival_time <= *recipient_timing {
                    *recipient_timing = first_cert_arrival_time;
                }
            }
            timings
        };

        match self {
            Self::Block => {
                // TODO: find better way of integrating sub-protocol
                let builder = RotorInstanceBuilder::new(
                    StakeWeightedSampler::new(environment.validators.clone()),
                    StakeWeightedSampler::new(environment.validators.clone()),
                    instance.params.rotor_params,
                );
                let engine = SimulationEngine::<RotorLatencySimulation<_, _>>::new(
                    builder,
                    environment.clone(),
                );
                let mut timings = Timings::default();
                // TODO: actually simulate more than one slot
                engine.run(&instance.rotor_instances[0], &mut timings);
                timings
                    .get(crate::rotor::LatencyEvent::Block)
                    .unwrap()
                    .to_vec()
            }
            Self::LocalNotar => broadcast_vote_threshold(0.6),
            Self::Notar => local_or_cert(dependency_timings),
            Self::LocalFastFinal => broadcast_vote_threshold(0.8),
            Self::LocalSlowFinal => broadcast_vote_threshold(0.6),
            Self::LocalFinal => column_min(dependency_timings),
            // NOTE: when sending final cert, final vote is already scheduled
            // TODO: this is not always optimal, handle this properly
            Self::Final => local_or_cert(dependency_timings),
        }
    }
}

/// Parameters for the Alpenglow latency simulation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LatencySimParams {
    rotor_params: RotorParams,
    num_slots_per_window: usize,
    num_slots: usize,
}

impl LatencySimParams {
    /// Creates a parameter set for the Alpenglow latency simulation.
    pub fn new(rotor_params: RotorParams, num_slots_per_window: usize, num_slots: usize) -> Self {
        Self {
            rotor_params,
            num_slots_per_window,
            num_slots,
        }
    }
}

/// A builder for Alpenglow latency simulation instances.
pub struct LatencySimInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    rotor_builder: RotorInstanceBuilder<L, R>,
    params: LatencySimParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencySimInstanceBuilder<L, R> {
    /// Creates a new builder instance from a builder for Rotor instances.
    pub fn new(rotor_builder: RotorInstanceBuilder<L, R>, params: LatencySimParams) -> Self {
        Self {
            rotor_builder,
            params,
        }
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> Builder for LatencySimInstanceBuilder<L, R> {
    type Params = LatencySimParams;
    type Instance = LatencySimInstance;

    fn build(&self, rng: &mut impl Rng) -> LatencySimInstance {
        let rotor_instances = (0..self.params.num_slots)
            .map(|_| self.rotor_builder.build(rng))
            .collect();
        LatencySimInstance {
            rotor_instances,
            params: self.params.clone(),
        }
    }

    fn params(&self) -> &Self::Params {
        &self.params
    }
}

/// A specific instance of the Alpenglow latency simulation.
///
/// Contains one instance of the Rotor latency simulation, [`RotorInstance`], per slot.
pub struct LatencySimInstance {
    rotor_instances: Vec<RotorInstance>,
    params: LatencySimParams,
}
