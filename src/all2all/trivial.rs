// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! A trivial implementation of an all-to-all broadcast protocol.
//!
//! Broadcasts each message once over the underlying [`Network`].
//! After that, the message is forgotten. The protocol is completely stateless.
//! If the underlying [`Network`] is not reliable, the message might thus be lost.

use crate::ValidatorInfo;
use crate::network::{Network, NetworkError, NetworkMessage};

use super::All2All;

/// Instance of the trivial all-to-all broadcast protocol.
pub struct TrivialAll2All<N: Network> {
    validators: Vec<ValidatorInfo>,
    network: N,
}

impl<N: Network> TrivialAll2All<N> {
    /// Creates a new `TrivialAll2All` instance.
    ///
    /// Messages will be broadcast to all `validators` over the provided `network`.
    /// For each, [`ValidatorInfo::all2all_address`] will serve as recipient.
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

    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::network::simulated::SimulatedNetworkCore;

    use tokio::task::JoinSet;

    use std::{sync::Arc, time::Duration};

    #[tokio::test]
    async fn simple_broadcast() {
        // set up network and nodes
        let core = Arc::new(
            SimulatedNetworkCore::default()
                .with_default_latency(Duration::from_millis(10))
                .with_packet_loss(0.0),
        );
        let net_sender = core.join_unlimited(0).await;
        let mut net_others = Vec::new();
        let mut validators = Vec::new();
        for i in 0..20 {
            if i > 0 {
                net_others.push(core.join_unlimited(i).await);
            }
            let sk = SecretKey::new(&mut rand::rng());
            let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
            validators.push(ValidatorInfo {
                id: i,
                stake: 1,
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: i.to_string(),
                disseminator_address: String::new(),
                repair_address: String::new(),
            });
        }

        // set up all-to-all instances
        let mut all2all_others = Vec::new();
        for net in net_others {
            all2all_others.push(TrivialAll2All::new(validators.clone(), net));
        }
        let all2all_sender = TrivialAll2All::new(validators, net_sender);

        // run sender and receivers
        let mut tasks = JoinSet::new();
        tasks.spawn(async move {
            let msg = NetworkMessage::Ping;
            all2all_sender.broadcast(&msg).await.unwrap();
        });
        for all2all in all2all_others {
            tasks.spawn(async move {
                let received = all2all.receive().await.unwrap();
                assert!(matches!(received, NetworkMessage::Ping));
            });
        }
        tasks.join_all().await;
    }
}
