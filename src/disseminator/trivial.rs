// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use async_trait::async_trait;

use super::Disseminator;
use crate::ValidatorInfo;
use crate::network::{Network, ShredNetwork};
use crate::shredder::Shred;

/// A trivial implementation for a block disseminator.
/// The leader just sends each shred directly to every validator.
pub struct TrivialDisseminator<N: Network> {
    validators: Vec<ValidatorInfo>,
    network: N,
}

impl<N: Network> TrivialDisseminator<N> {
    pub const fn new(validators: Vec<ValidatorInfo>, network: N) -> Self {
        Self {
            validators,
            network,
        }
    }
}

#[async_trait]
impl<N> Disseminator for TrivialDisseminator<N>
where
    N: ShredNetwork,
{
    async fn send(&self, shred: &Shred) -> std::io::Result<()> {
        self.network
            .send_to_many(
                shred,
                self.validators.iter().map(|v| v.disseminator_address),
            )
            .await?;
        Ok(())
    }

    async fn forward(&self, _shred: &Shred) -> std::io::Result<()> {
        // nothing to do
        Ok(())
    }

    async fn receive(&self) -> std::io::Result<Shred> {
        self.network.receive().await
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::time::Duration;

    use tokio::sync::Mutex;
    use tokio::task;

    use super::*;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::network::{UdpNetwork, dontcare_sockaddr, localhost_ip_sockaddr};
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, TOTAL_SHREDS};
    use crate::types::slice::create_slice_with_invalid_txs;

    fn create_disseminator_instances(
        count: u64,
        base_port: u16,
    ) -> (
        Vec<SecretKey>,
        Vec<TrivialDisseminator<UdpNetwork<Shred, Shred>>>,
    ) {
        let mut sks = Vec::new();
        let mut voting_sks = Vec::new();
        let mut validators = Vec::new();
        for i in 0..count {
            sks.push(SecretKey::new(&mut rand::rng()));
            voting_sks.push(aggsig::SecretKey::new(&mut rand::rng()));
            validators.push(ValidatorInfo {
                id: i,
                stake: 1,
                pubkey: sks[i as usize].to_pk(),
                voting_pubkey: voting_sks[i as usize].to_pk(),
                all2all_address: dontcare_sockaddr(),
                disseminator_address: localhost_ip_sockaddr(base_port + i as u16),
                repair_request_address: dontcare_sockaddr(),
                repair_response_address: dontcare_sockaddr(),
            });
        }

        let mut disseminators = Vec::new();
        for i in 0..count {
            let network = UdpNetwork::new(base_port + i as u16);
            disseminators.push(TrivialDisseminator::new(validators.clone(), network));
        }
        (sks, disseminators)
    }

    #[tokio::test]
    async fn dissemination() {
        let (sks, mut disseminators) = create_disseminator_instances(20, 5000);
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let shreds = RegularShredder::default().shred(slice, &sks[0]).unwrap();

        let shreds_received = Arc::new(Mutex::new(0_usize));
        let mut tasks = Vec::new();

        // forward & receive shreds on "non-leader" disseminator instance
        for _ in 0..disseminators.len() - 1 {
            let sr = shreds_received.clone();
            let diss_non_leader = disseminators.pop().unwrap();
            tasks.push(task::spawn(async move {
                loop {
                    match diss_non_leader.receive().await {
                        Ok(shred) => {
                            diss_non_leader.forward(&shred).await.unwrap();
                            *sr.lock().await += 1;
                        }
                        _ => continue,
                    }
                }
            }));
        }

        tokio::time::sleep(Duration::from_millis(10)).await;
        for shred in shreds {
            disseminators[0].send(&shred).await.unwrap();
        }

        // forward shreds on the "leader" disseminator instance
        assert_eq!(disseminators.len(), 1);
        let rotor_leader = disseminators.pop().unwrap();
        let rotor_task_leader = task::spawn(async move {
            loop {
                match rotor_leader.receive().await {
                    Ok(shred) => {
                        rotor_leader.forward(&shred).await.unwrap();
                    }
                    _ => continue,
                }
            }
        });

        tokio::time::sleep(Duration::from_millis(100)).await;

        // non-leaders should have received all shreds via Rotor
        assert_eq!(*shreds_received.lock().await, 19 * TOTAL_SHREDS);
        rotor_task_leader.abort();
        for task in tasks {
            task.abort();
        }
    }
}
