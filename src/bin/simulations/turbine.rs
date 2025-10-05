// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for the Turbine protocol.
//!
//! This implements the following simulations:
//! - Latency simulation for block dissemination via Turbine.
//! - Robustness simulation against liveness and safety failures.

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::disseminator::turbine::{DEFAULT_FANOUT, TurbineTree};
use rand::prelude::*;

use crate::discrete_event_simulator::Builder;

mod latency;
// mod robustness;

/// Parameters for the Turbine protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TurbineParams {
    /// Fanout of the Turbine tree.
    pub fanout: usize,
    /// Number of shreds needed to recover the data.
    pub num_data_shreds: usize,
    /// NUmber of shreds that make up a slice.
    pub num_shreds: usize,
    /// Number of slices that make up a block.
    pub num_slices: usize,
}

impl TurbineParams {
    /// Creates a new set of Turbine parameters.
    pub fn new(num_data_shreds: usize, num_shreds: usize, num_slices: usize) -> Self {
        Self {
            fanout: DEFAULT_FANOUT,
            num_data_shreds,
            num_shreds,
            num_slices,
        }
    }
}

/// Builder for Turbine instances with a specific set of parameters.
#[derive(Debug)]
pub struct TurbineInstanceBuilder<L: SamplingStrategy> {
    pub leader_sampler: L,
    pub params: TurbineParams,
}

impl<L: SamplingStrategy> TurbineInstanceBuilder<L> {
    /// Creates a new builder instance, with the provided sampling strategies.
    pub fn new(leader_sampler: L, params: TurbineParams) -> Self {
        Self {
            leader_sampler,
            params,
        }
    }
}

impl<L: SamplingStrategy> Builder for TurbineInstanceBuilder<L> {
    type Params = TurbineParams;
    type Instance = TurbineInstance;

    fn build(&self, rng: &mut impl Rng) -> TurbineInstance {
        TurbineInstance {
            leader: self.leader_sampler.sample(rng),
            tree: TurbineTree::new(),
            params: self.params,
        }
    }

    fn params(&self) -> &TurbineParams {
        &self.params
    }
}

/// Specific instance of the Turbine protocol.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TurbineInstance {
    /// Leader validator.
    pub leader: ValidatorId,
    /// Relays for each slice, and each shred within a slice.
    pub tree: TurbineTree,
    /// Parameters this instance corresponds to.
    pub params: TurbineParams,
}
