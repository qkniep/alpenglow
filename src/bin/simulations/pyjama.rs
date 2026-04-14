// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for Pyjama, the MCP protocol.
//!
//! Pyjama is one instantiation of a multiple-concurrent proposers (MCP) consensus protocol.
//! As such, it provides the following economic properties:
//! - Selective-censorship resistance:
//!   A malicious consensus leader can not unilaterally exclude an honest proposer's proposal.
//! - Weak hiding:
//!   A malicious proposer cannot condition the contents of their block on the contents of another.
//!
//! Additionally, Pyjama provides the following stronger economic property:
//! - Strong hiding:
//!   A malicious proposer cannot condition inclusion of their block on the contents of another.
//!
//! Compared to Ryse, Pyjama aims to be a general gadget that works with any consensus protocol.
//! It provides a wrapper, where any consensus protocol like Alpenglow can be plugged in.

mod latency;
mod parameters;
mod robustness;

pub use latency::PyjamaLatencySimulation;
pub use parameters::{PyjamaInstance, PyjamaInstanceBuilder, PyjamaParameters as PyjamaParams};
pub use robustness::{run_pyjama_robustness_test, run_robustness_tests};
