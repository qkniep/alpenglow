// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::execution::Execution;
use crate::network::Network;
use crate::{All2All, Alpenglow, Disseminator};

/// Full validator node.
///
/// Consist of a consensus protocol instance and an execution engine.
/// Participates in consensus and executes finaliztransactions.
pub struct Validator<A, D, R, T, E>
where
    A: All2All,
    D: Disseminator,
    R: Network,
    T: Network,
    E: Execution,
{
    /// Consensus protocol instance.
    consensus: Alpenglow<A, D, R, T>,

    /// Execution engine.
    execution: E,
}
