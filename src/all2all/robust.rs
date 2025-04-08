// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;

use crate::ValidatorInfo;
use crate::network::{Network, NetworkError, NetworkMessage};

use super::All2All;

/// A more robust implementation of an all-to-all broadcast protocol.
///
/// Broadcasts each message over the underlying [`Network`].
// TODO: acutally make more robust (retransmits, ...)
pub struct RobustAll2All<N: Network> {
    validators: Vec<ValidatorInfo>,
    queues: Vec<VecDeque<(usize, NetworkMessage, bool)>>,
    network: N,
}

impl<N: Network> RobustAll2All<N> {
    pub fn new(validators: Vec<ValidatorInfo>, network: N) -> Self {
        let queues = vec![VecDeque::new(); validators.len()];
        Self {
            validators,
            queues,
            network,
        }
    }

    pub fn handle_retransmits(&self) {}
}

impl<N: Network> All2All for RobustAll2All<N> {
    async fn broadcast(&self, msg: &NetworkMessage) -> Result<(), NetworkError> {
        for v in &self.validators {
            // HACK: stupidly expensive retransmits
            for _ in 0..1000 {
                self.network.send(msg, &v.all2all_address).await?;
            }
        }
        Ok(())
    }

    async fn receive(&self) -> Result<NetworkMessage, NetworkError> {
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
    use super::*;

    use crate::crypto::aggsig::SecretKey;
    use crate::network::simulated::SimulatedNetworkCore;

    use tokio::task::JoinSet;
    use tokio::time::timeout;

    use std::sync::Arc;
    use std::time::Duration;

    async fn broadcast_test(packet_loss: f64) {
        // set up network and nodes
        let core = Arc::new(
            SimulatedNetworkCore::new()
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
            validators.push(ValidatorInfo {
                id: i,
                stake: 1,
                pubkey: sk.to_pk(),
                all2all_address: format!("{}", i),
                disseminator_address: "".to_owned(),
                repair_address: "".to_owned(),
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
            let msg = NetworkMessage::Ping;
            all2all_sender.broadcast(&msg).await.unwrap();
        });
        for all2all in all2all_others {
            tasks.spawn(async move {
                let received = all2all.receive().await.unwrap();
                assert!(matches!(received, NetworkMessage::Ping));
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
