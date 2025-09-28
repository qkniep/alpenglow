// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for the Alpenglow protocol.
//!
//! So far, this test can only simulate the good case.

use std::hash::Hash;
use std::marker::PhantomData;
use std::path::Path;
use std::sync::RwLock;

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::network::simulated::ping_data::PingServer;
use alpenglow::{Stake, ValidatorInfo};
use rand::prelude::*;
use rayon::prelude::*;

use crate::discrete_event_simulator::{
    Builder, Event, Protocol, SimTime, SimulationEnvironment, Stage, TimingStats, Timings,
};
use crate::rotor::{RotorInstance, RotorInstanceBuilder, RotorParams};

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;
/// Size (in bytes) assumed per certificate in the simulation.
const CERT_SIZE: usize = 128 /* sig */ + 256 /* bitmap */ + 64 /* slot, hash, flags */;

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
            Self::Rotor => vec![LatencyEvent::Direct(0), LatencyEvent::Rotor(0)],
            Self::Notar => vec![LatencyEvent::Notar, LatencyEvent::Shreds95],
            Self::Final1 => vec![
                LatencyEvent::FastFinal,
                LatencyEvent::SlowFinal,
                LatencyEvent::Notar65,
            ],
            Self::Final2 => vec![LatencyEvent::Final],
        }
    }
}

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Direct(usize),
    Rotor(usize),
    Shreds95,
    Notar,
    Notar65,
    FastFinal,
    SlowFinal,
    Final,
}

impl Event for LatencyEvent {
    type Params = LatencySimParams;
    type Instance = LatencySimInstance;

    fn name(&self) -> String {
        match self {
            Self::Direct(_) => "direct",
            Self::Rotor(_) => "rotor",
            Self::Shreds95 => "shreds95",
            Self::Notar => "notar",
            Self::Notar65 => "notar65",
            Self::FastFinal => "fast_final",
            Self::SlowFinal => "slow_final",
            Self::Final => "final",
        }
        .to_owned()
    }

    fn should_track_stats(&self) -> bool {
        match self {
            Self::Direct(slice) => *slice == 0,
            Self::Rotor(slice) => *slice == 0,
            _ => true,
        }
    }

    fn dependencies(&self, _params: &LatencySimParams) -> Vec<Self> {
        match self {
            Self::Direct(_) => vec![],
            Self::Rotor(_) => vec![Self::Direct(0)],
            Self::Shreds95 => vec![Self::Rotor(0)],
            Self::Notar => vec![Self::Rotor(0)],
            Self::Notar65 => vec![Self::Notar],
            Self::FastFinal => vec![Self::Notar],
            Self::SlowFinal => vec![Self::Notar],
            Self::Final => vec![Self::SlowFinal, Self::FastFinal],
        }
    }

    fn calculate_timing(
        &self,
        dep_timings: &[&[SimTime]],
        _instance: &LatencySimInstance,
        environment: &SimulationEnvironment,
    ) -> Vec<SimTime> {
        vec![SimTime::ZERO; environment.num_validators()]
    }
}

///
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LatencySimParams {
    rotor_params: RotorParams,
    num_slots_per_window: usize,
    num_slots: usize,
}

impl LatencySimParams {
    ///
    pub fn new(rotor_params: RotorParams, num_slots_per_window: usize, num_slots: usize) -> Self {
        Self {
            rotor_params,
            num_slots_per_window,
            num_slots,
        }
    }
}

///
pub struct LatencySimInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    rotor_builder: RotorInstanceBuilder<L, R>,
    params: LatencySimParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencySimInstanceBuilder<L, R> {
    ///
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
        let rotor_instance = self.rotor_builder.build(rng);
        LatencySimInstance {
            rotor_instance,
            params: self.params.clone(),
        }
    }

    fn params(&self) -> &Self::Params {
        &self.params
    }
}

///
pub struct LatencySimInstance {
    rotor_instance: RotorInstance,
    params: LatencySimParams,
}
