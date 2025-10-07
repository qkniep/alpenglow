// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Calculations about the robustness of the Pyjama MCP protocol.
//!
//! Currently, this just runs some static calculations on the set of parameters.
//!
//! In the future, this would also simulate attack scenarios for a specific stake distribution.
//! This is analogous to what is done for Rotor in [`crate::rotor::robustness`];

use color_eyre::Result;

use super::parameters::{AdversaryStrength, PyjamaParameters};

const NUM_PROPOSERS: u64 = 16;
const NUM_RELAYS: u64 = 512;
const ADVERSARY_STRENGTH: AdversaryStrength = AdversaryStrength {
    crashed: 0.0,
    byzantine: 0.18,
};

pub fn run_robustness_tests() -> Result<()> {
    PyjamaParameters::new(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_paper1(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_paper2(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_hiding(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_liveness(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);
    PyjamaParameters::new_permanent_liveness(NUM_PROPOSERS, NUM_RELAYS)
        .print_failure_probabilities(ADVERSARY_STRENGTH);

    // TODO: extend with robustness tests for actual stake distribution
    //       and different sampling strategies (analogous to `rotor/robustness`)

    Ok(())
}
