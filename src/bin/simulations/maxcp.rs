// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for MaxCP, the MCP protocol.
//!
//! MaxCP is one instantiation of a multiple-concurrent proposers (MCP) consensus protocol.
//! As such, it provides the following economic properties:
//! - Selective-censorship resistance:
//!   A malicious consensus leader can not unilaterally exclude an honest proposer's proposal.
//!
//! It does not provide any hiding.

mod latency;
mod parameters;
mod robustness;

pub use latency::MaxcpLatencySimulation;
pub use parameters::{MaxcpInstance, MaxcpInstanceBuilder, MaxcpParameters as MaxcpParams};
pub use robustness::{run_maxcp_robustness_test, run_robustness_tests};
