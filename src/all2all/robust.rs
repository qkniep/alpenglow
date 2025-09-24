// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! A more robust implementation of an all-to-all broadcast protocol.
//!
//! Broadcasts each message over the underlying instance of [`Network`].
//! The message may be retransmitted multiple times.

use std::iter::repeat_n;

use async_trait::async_trait;

use super::All2All;
use crate::ValidatorInfo;
use crate::consensus::ConsensusMessage;
use crate::network::{ConsensusNetwork, Network};

/// Instance of the robust all-to-all broadcast protocol.
// TODO: acutally make more robust (retransmits, ...)
pub struct RobustAll2All<N: Network> {
    validators: Vec<ValidatorInfo>,
    network: N,
}

impl<N: Network> RobustAll2All<N> {
    /// Creates a new `RobustAll2All` instance.
    ///
    /// Messages will be broadcast to all `validators` over the provided `network`.
    /// Potential retransmits will be handled automatically, also over the `network`.
    pub fn new(validators: Vec<ValidatorInfo>, network: N) -> Self {
        Self {
            validators,
            network,
        }
    }

    pub fn handle_retransmits(&self) {}
}

#[async_trait]
impl<N: Network> All2All for RobustAll2All<N>
where
    N: ConsensusNetwork,
{
    async fn broadcast(&self, msg: &ConsensusMessage) -> std::io::Result<()> {
        // HACK: stupidly expensive retransmits
        let addrs = self
            .validators
            .iter()
            .flat_map(|v| repeat_n(v.all2all_address, 1000));
        self.network.send_to_many(msg, addrs).await
    }

    async fn receive(&self) -> std::io::Result<ConsensusMessage> {
        self.network.receive().await
        // loop {
        //     let msg = self.network.receive().await;
        //     match msg {
        //         // TODO: handle ACK
        //         NetworkMessage::Ack(nonce) => {}
        //         // TODO: send ACK
        //         _ => return msg,
        //     }
        // }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::time::Duration;

    use tokio::task::JoinSet;
    use tokio::time::timeout;

    use super::*;
    use crate::consensus::Vote;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::network::simulated::SimulatedNetworkCore;
    use crate::network::{dontcare_sockaddr, localhost_ip_sockaddr};
    use crate::types::Slot;

    async fn broadcast_test(packet_loss: f64) {
        // set up network and nodes
        let core = Arc::new(
            SimulatedNetworkCore::default()
                .with_default_latency(Duration::from_millis(10))
                .with_packet_loss(packet_loss),
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
                all2all_address: localhost_ip_sockaddr(i.try_into().unwrap()),
                disseminator_address: dontcare_sockaddr(),
                repair_request_address: dontcare_sockaddr(),
                repair_response_address: dontcare_sockaddr(),
            });
        }

        // set up all-to-all instances
        let mut all2all_others = Vec::new();
        for net in net_others {
            all2all_others.push(RobustAll2All::new(validators.clone(), net));
        }
        let all2all_sender = RobustAll2All::new(validators, net_sender);

        // run sender and receivers
        let mut tasks = JoinSet::new();
        tasks.spawn(async move {
            let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
            let vote = Vote::new_skip(Slot::genesis(), &voting_sk, 0);
            let msg = ConsensusMessage::Vote(vote);
            all2all_sender.broadcast(&msg).await.unwrap();
            while let Ok(Ok(_)) =
                timeout(Duration::from_millis(1000), all2all_sender.receive()).await
            {
                // do nothing
            }
        });
        for all2all in all2all_others {
            tasks.spawn(async move {
                let received = all2all.receive().await.unwrap();
                assert!(matches!(received, ConsensusMessage::Vote(_)));
                while let Ok(Ok(_)) = timeout(Duration::from_millis(1000), all2all.receive()).await
                {
                    // do nothing
                }
            });
        }
        tasks.join_all().await;
    }

    #[tokio::test]
    async fn simple_broadcast() {
        // run broadcast test with simulated network w/o any packet loss
        broadcast_test(0.0).await;
    }

    #[tokio::test]
    async fn packet_loss() {
        // run broadcast test with simulated network with 20% packet loss
        broadcast_test(0.2).await;
    }

    #[tokio::test]
    async fn extreme_packet_loss() {
        // run broadcast test with simulated network with 90% packet loss
        broadcast_test(0.9).await;
    }
}
