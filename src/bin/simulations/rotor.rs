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
use alpenglow::disseminator::rotor::{QuorumSamplingStrategy, SamplingStrategy};
use rand::prelude::*;

pub(crate) use self::latency::{LatencyEvent, RotorLatencySimulation};
pub(crate) use self::robustness::run_rotor_robustness_test;
use crate::discrete_event_simulator::Builder;

/// Parameters for the Rotor protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RotorParams {
    /// Number of shreds needed to recover the data.
    pub(crate) data_shreds: usize,
    /// Number of shreds that make up a slice.
    pub(crate) shreds: usize,
    /// Number of slices that make up a block.
    pub(crate) slices: usize,
}

impl RotorParams {
    /// Creates a new set of Rotor parameters.
    pub(crate) fn new(data_shreds: usize, shreds: usize, slices: usize) -> Self {
        Self {
            data_shreds,
            shreds,
            slices,
        }
    }
}

/// Builder for Rotor instances with a specific set of parameters.
#[derive(Debug)]
pub(crate) struct RotorInstanceBuilder<L: SamplingStrategy, R: QuorumSamplingStrategy> {
    pub(crate) leader_sampler: L,
    pub(crate) rotor_sampler: R,
    pub(crate) params: RotorParams,
}

impl<L: SamplingStrategy, R: QuorumSamplingStrategy> RotorInstanceBuilder<L, R> {
    /// Creates a new builder instance, with the provided sampling strategies.
    pub(crate) fn new(leader_sampler: L, rotor_sampler: R, params: RotorParams) -> Self {
        assert_eq!(rotor_sampler.quorum_size(), params.shreds);
        Self {
            leader_sampler,
            rotor_sampler,
            params,
        }
    }
}

impl<L: SamplingStrategy, R: QuorumSamplingStrategy> Builder for RotorInstanceBuilder<L, R> {
    type Params = RotorParams;
    type Instance = RotorInstance;

    fn build(&self, rng: &mut impl Rng) -> RotorInstance {
        RotorInstance {
            leader: self.leader_sampler.sample(rng),
            relays: (0..self.params.slices)
                .map(|_| self.rotor_sampler.sample_quorum(rng))
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
pub(crate) struct RotorInstance {
    /// Leader validator.
    pub(crate) leader: ValidatorId,
    /// Relays for each slice, and each shred within a slice.
    pub(crate) relays: Vec<Vec<ValidatorId>>,
    /// Parameters this instance corresponds to.
    pub(crate) params: RotorParams,
}
