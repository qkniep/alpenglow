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

pub use self::latency::{
    LatencyEvent, LatencySimInstance, LatencySimInstanceBuilder, LatencySimParams,
    RyseLatencySimulation,
};
pub use self::parameters::{RyseInstance, RyseInstanceBuilder, RyseParameters};
pub use self::robustness::run_robustness_tests;
