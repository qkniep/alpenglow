// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for Ryse, the MCP proposal.
//!
//! Ryse is one instantiation of a multiple-concurrent proposers (MCP) consensus protocol.
//! As such, it provides the following economic properties:
//! - Selective-censorship resistance:
//!   A malicious consensus leader can not unilaterally exclude an honest proposer's proposal.
//! - Weak hiding:
//!   A malicious proposer cannot condition the contents of their block on the contents of another.
//!
//! Compared to Pyjama, Ryse aims to be a simple modification of Alpenglow.
//! That is, it is not a general gadget that can be combined with any consensus protocol.
//! Instead, it specifically modifies Alpenglow's Rotor block dissemination protocol.
//! In Ryse, each relay would release shreds from all leaders simultaneously.

mod latency;
mod parameters;
mod robustness;

pub use self::latency::{LatencySimInstanceBuilder, LatencySimParams, RyseLatencySimulation};
pub use self::parameters::{RyseInstanceBuilder, RyseParameters};
pub use self::robustness::{run_robustness_tests, run_ryse_robustness_test};
