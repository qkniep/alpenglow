// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Calculations about the robustness of the Ryse MCP protocol.
//!
//! Currently, this just runs some static calculations on the set of parameters.
//!
//! In the future, this would also simulate attack scenarios for a specific stake distribution.
//! This is analogous to what is done for Rotor in [`crate::rotor::RotorRobustnessTest`];

use color_eyre::Result;

use super::parameters::{AdversaryStrength, RyseParameters};

const NUM_PROPOSERS: u64 = 16;
const NUM_RELAYS: u64 = 512;
const ADVERSARY_STRENGTH: AdversaryStrength = AdversaryStrength {
    crashed: 0.2,
    byzantine: 0.2,
};

pub fn run_robustness_tests() -> Result<()> {
    let params = RyseParameters::new(NUM_PROPOSERS, NUM_RELAYS);
    params.print_failure_probabilities(ADVERSARY_STRENGTH);
    let optimal_params = params.optmize(ADVERSARY_STRENGTH);
    optimal_params.print_failure_probabilities(ADVERSARY_STRENGTH);

    // TODO: extend with robustness tests for actual stake distribution
    //       and different sampling strategies (analogous to `rotor/robustness`)

    Ok(())
}
