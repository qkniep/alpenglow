// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//!
//!
//!

mod latency;
mod robustness;

use alpenglow::ValidatorId;
use alpenglow::disseminator::rotor::SamplingStrategy;
use rand::prelude::*;

pub use self::robustness::RotorRobustnessTest;

///
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RotorParams {
    pub num_data_shreds: usize,
    pub num_shreds: usize,
    pub num_slices: usize,
}

///
#[derive(Debug)]
pub struct RotorInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    pub leader_sampler: L,
    pub rotor_sampler: R,
    pub params: RotorParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> RotorInstanceBuilder<L, R> {
    ///
    pub fn new(leader_sampler: L, rotor_sampler: R, params: RotorParams) -> Self {
        Self {
            leader_sampler,
            rotor_sampler,
            params,
        }
    }

    ///
    pub fn build(&self, rng: &mut impl Rng) -> RotorInstance {
        RotorInstance {
            leader: self.leader_sampler.sample(rng),
            relays: self
                .rotor_sampler
                .sample_multiple(self.params.num_slices, rng),
            params: self.params,
        }
    }
}

///
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RotorInstance {
    pub leader: ValidatorId,
    pub relays: Vec<ValidatorId>,
    pub params: RotorParams,
}
