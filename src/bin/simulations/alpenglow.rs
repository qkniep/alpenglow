// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulations for the Alpenglow protocol.
//!
//! This implements the following simulations:
//! - Latency simulation for the entire good case of the protocol.
//! - Bandwidth simulation calculating required bandwidth for voting and block dissemination.

mod bandwidth;
mod latency;

pub use bandwidth::*;
pub use latency::*;
