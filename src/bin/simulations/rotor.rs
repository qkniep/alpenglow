// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for the Rotor protocol.
//!
//! This implements the following simulations:
//! - Latency simulation for block dissemination via Rotor.
//! - Robustness simulation against liveness and safety failures.

mod latency;
mod robustness;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use rand::prelude::*;

pub use self::latency::{LatencyEvent, RotorLatencySimulation};
pub use self::robustness::run_rotor_robustness_test;
use crate::discrete_event_simulator::Builder;

/// Parameters for the Rotor protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RotorParams {
    /// Number of shreds needed to recover the data.
    pub num_data_shreds: usize,
    /// NUmber of shreds that make up a slice.
    pub num_shreds: usize,
    /// Number of slices that make up a block.
    pub num_slices: usize,
}

impl RotorParams {
    /// Creates a new set of Rotor parameters.
    pub fn new(num_data_shreds: usize, num_shreds: usize, num_slices: usize) -> Self {
        Self {
            num_data_shreds,
            num_shreds,
            num_slices,
        }
    }
}

/// Builder for Rotor instances with a specific set of parameters.
#[derive(Debug)]
pub struct RotorInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    pub leader_sampler: L,
    pub rotor_sampler: R,
    pub params: RotorParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> RotorInstanceBuilder<L, R> {
    /// Creates a new builder instance, with the provided sampling strategies.
    pub fn new(leader_sampler: L, rotor_sampler: R, params: RotorParams) -> Self {
        Self {
            leader_sampler,
            rotor_sampler,
            params,
        }
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> Builder for RotorInstanceBuilder<L, R> {
    type Params = RotorParams;
    type Instance = RotorInstance;

    fn build(&self, rng: &mut impl Rng) -> RotorInstance {
        RotorInstance {
            leader: self.leader_sampler.sample(rng),
            relays: (0..self.params.num_slices)
                .map(|_| {
                    self.rotor_sampler
                        .sample_multiple(self.params.num_shreds, rng)
                })
                .collect(),
            params: self.params,
        }
    }

    fn params(&self) -> &Self::Params {
        &self.params
    }
}

/// Specific instance of the Rotor protocol.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RotorInstance {
    /// Leader validator.
    pub leader: ValidatorId,
    /// Relays for each slice, and each shred within a slice.
    pub relays: Vec<Vec<ValidatorId>>,
    /// Parameters this instance corresponds to.
    pub params: RotorParams,
}
