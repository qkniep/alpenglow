// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::execution::Execution;
use crate::network::Network;
use crate::{All2All, Alpenglow, Disseminator, Transaction};

/// Full validator node.
///
/// Consist of a consensus protocol instance and an execution engine.
/// Participates in consensus and executes transactions.
pub struct Validator<A, D, T, E>
where
    A: All2All,
    D: Disseminator,
    T: Network<Recv = Transaction> + 'static,
    E: Execution,
{
    /// Consensus protocol instance.
    consensus: Alpenglow<A, D, T>,

    /// Execution engine.
    execution: E,
}
