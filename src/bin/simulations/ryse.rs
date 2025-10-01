// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for Ryse, the MCP proposal.
//!
//! Ryse is one instantiation of a multiple-concurrent proposers (MCP) consensus protocol.
//! As such, it provides the following economic properties:
//! - Selective-censorship resistance:
//! - Hiding:
//!
//! Compared to Pyjama, Ryse aims to be a simple modification of Alpenglow.
//! That is, it is not a general gadget that can be combined with any consensus protocol.
//! Instead, it specifically modifies Alpenglow's Rotor block dissemination protocol.
//! In Ryse, each relay would release shreds from all leaders simultaneously.

mod latency;
mod parameters;
mod robustness;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use rand::prelude::*;

pub use self::latency::{LatencyEvent, RyseLatencySimulation};
pub use self::robustness::run_robustness_tests;
use crate::discrete_event_simulator::Builder;

/// Parameters for the Ryse protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RyseParams {
    /// Number of shreds needed to recover the data.
    pub num_data_shreds: usize,
    /// NUmber of shreds that make up a slice.
    pub num_shreds: usize,
    /// Number of slices that make up a block.
    pub num_slices: usize,
}

impl RyseParams {
    /// Creates a new set of Ryse parameters.
    pub fn new(num_data_shreds: usize, num_shreds: usize, num_slices: usize) -> Self {
        Self {
            num_data_shreds,
            num_shreds,
            num_slices,
        }
    }
}

/// Builder for Ryse instances with a specific set of parameters.
#[derive(Debug)]
pub struct RyseInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    pub leader_sampler: L,
    pub rotor_sampler: R,
    pub params: RyseParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> RyseInstanceBuilder<L, R> {
    /// Creates a new builder instance, with the provided sampling strategies.
    pub fn new(leader_sampler: L, rotor_sampler: R, params: RyseParams) -> Self {
        Self {
            leader_sampler,
            rotor_sampler,
            params,
        }
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> Builder for RyseInstanceBuilder<L, R> {
    type Params = RyseParams;
    type Instance = RyseInstance;

    fn build(&self, rng: &mut impl Rng) -> RyseInstance {
        RyseInstance {
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

/// Specific instance of the Ryse protocol.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RyseInstance {
    /// Leader validator.
    pub leader: ValidatorId,
    /// Relays for each slice, and each shred within a slice.
    pub relays: Vec<Vec<ValidatorId>>,
    /// Parameters this instance corresponds to.
    pub params: RyseParams,
}
