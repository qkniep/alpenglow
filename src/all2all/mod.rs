// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

mod robust;
mod trivial;

use crate::network::{NetworkError, NetworkMessage};

pub use robust::RobustAll2All;
pub use trivial::TrivialAll2All;

/// Abstraction for a direct all-to-all network communication protocol.
pub trait All2All {
    /// Broadcasts the given message to all known nodes.
    fn broadcast(
        &self,
        msg: &NetworkMessage,
    ) -> impl Future<Output = Result<(), NetworkError>> + Send;

    /// Receives a message from any of the other nodes.
    fn receive(&self) -> impl Future<Output = Result<NetworkMessage, NetworkError>> + Send;
}
