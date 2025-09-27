// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//!
//!
//!

mod robustness;

use alpenglow::disseminator::rotor::SamplingStrategy;
pub use robustness::RotorRobustnessTest;

///
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RotorParams<L: SamplingStrategy, R: SamplingStrategy> {
    pub leader_sampler: L,
    pub rotor_sampler: R,
    pub num_data_shreds: usize,
    pub num_shreds: usize,
    pub num_slices: usize,
}
