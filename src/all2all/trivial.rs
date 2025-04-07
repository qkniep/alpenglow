// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::ValidatorInfo;
use crate::network::{Network, NetworkError, NetworkMessage};

use super::All2All;

/// A trivial implementation of an all-to-all broadcast protocol.
/// Broadcasts each message once over the underlying [`Network`].
/// After that the message is ignored.
/// if the underlying [`Network`] is not reliable, the message might be lost.
pub struct TrivialAll2All<N: Network> {
    validators: Vec<ValidatorInfo>,
    network: N,
}

impl<N: Network> TrivialAll2All<N> {
    /// Creates a new `TrivialAll2All` instance.
    /// Messages will be broadcast to all `validators` over the provided `network`.
    pub const fn new(validators: Vec<ValidatorInfo>, network: N) -> Self {
        Self {
            validators,
            network,
        }
    }
}

impl<N: Network> All2All for TrivialAll2All<N> {
    async fn broadcast(&self, msg: &NetworkMessage) -> Result<(), NetworkError> {
        for v in &self.validators {
            self.network.send(msg, &v.all2all_address).await?;
        }
        Ok(())
    }

    async fn receive(&self) -> Result<NetworkMessage, NetworkError> {
        self.network.receive().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_broadcast() {}
}
