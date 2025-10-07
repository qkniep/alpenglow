// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for the Turbine protocol.
//!
//! This implements the following simulations:
//! - Latency simulation for block dissemination via Turbine.
//! - Robustness simulation against liveness and safety failures.

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::disseminator::turbine::{DEFAULT_FANOUT, WeightedShuffle};
use alpenglow::{ValidatorId, ValidatorInfo};
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
    pub validators: Vec<ValidatorInfo>,
    pub params: TurbineParams,
}

impl<L: SamplingStrategy> TurbineInstanceBuilder<L> {
    /// Creates a new builder instance, with the provided sampling strategies.
    pub fn new(leader_sampler: L, validators: Vec<ValidatorInfo>, params: TurbineParams) -> Self {
        Self {
            leader_sampler,
            validators,
            params,
        }
    }
}

impl<L: SamplingStrategy> Builder for TurbineInstanceBuilder<L> {
    type Params = TurbineParams;
    type Instance = TurbineInstance;

    fn build(&self, rng: &mut impl Rng) -> TurbineInstance {
        let mut build_tree = || {
            let mut weighted_shuffle =
                WeightedShuffle::new(self.validators.iter().map(|v| v.stake));
            weighted_shuffle
                .shuffle(rng)
                .map(|i| i as ValidatorId)
                .collect::<Vec<_>>()
        };
        let trees: Vec<_> = (0..self.params.num_slices)
            .map(|_| {
                (0..self.params.num_shreds)
                    .map(|_| build_tree())
                    .collect::<Vec<_>>()
            })
            .collect();
        TurbineInstance {
            leader: self.leader_sampler.sample(rng),
            trees,
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
    /// Turbine tree for each slice.
    pub trees: Vec<Vec<Vec<ValidatorId>>>,
    /// Parameters this instance corresponds to.
    pub params: TurbineParams,
}

impl TurbineInstance {
    pub fn parent(&self, slice: usize, shred: usize, v: ValidatorId) -> Option<ValidatorId> {
        if v == 0 {
            None
        } else {
            self.trees[slice][shred]
                .get(v as usize / self.params.fanout)
                .copied()
        }
    }

    pub fn layer1_parents(&self, slice: usize, v: ValidatorId) -> Vec<ValidatorId> {
        (0..self.params.num_shreds)
            .filter(|shred| self.layer1(slice, *shred).contains(&v))
            .filter_map(|shred| self.parent(slice, shred, v))
            .collect()
    }

    pub fn layer2_parents(&self, slice: usize, v: ValidatorId) -> Vec<ValidatorId> {
        (0..self.params.num_shreds)
            .filter(|shred| {
                !self.layer1(slice, *shred).contains(&v) && self.root(slice, *shred) != v
            })
            .filter_map(|shred| self.parent(slice, shred, v))
            .collect()
    }

    pub fn root(&self, slice: usize, shred: usize) -> ValidatorId {
        self.trees[slice][shred][0]
    }

    pub fn layer1(&self, slice: usize, shred: usize) -> &[ValidatorId] {
        &self.trees[slice][shred][1..self.params.fanout + 1]
    }

    pub fn layer2(&self, slice: usize, shred: usize) -> &[ValidatorId] {
        &self.trees[slice][shred][self.params.fanout + 1..]
    }
}
