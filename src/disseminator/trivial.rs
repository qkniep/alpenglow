// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use async_trait::async_trait;
use log::warn;

use crate::ValidatorInfo;
use crate::network::{Network, NetworkError, NetworkMessage};
use crate::shredder::Shred;

use super::Disseminator;

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
impl<N: Network> Disseminator for TrivialDisseminator<N> {
    async fn send(&self, shred: &Shred) -> Result<(), NetworkError> {
        let msg = NetworkMessage::Shred(shred.clone());
        for v in &self.validators {
            self.network.send(&msg, &v.disseminator_address).await?;
        }
        Ok(())
    }

    async fn forward(&self, _shred: &Shred) -> Result<(), NetworkError> {
        // nothing to do
        Ok(())
    }

    async fn receive(&self) -> Result<Shred, NetworkError> {
        loop {
            match self.network.receive().await? {
                NetworkMessage::Shred(s) => return Ok(s),
                m => warn!("unexpected message type for disseminator: {m:?}"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::network::UdpNetwork;
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, TOTAL_SHREDS};
    use crate::types::slice::create_slice_with_invalid_txs;

    use tokio::{sync::Mutex, task};

    use std::{sync::Arc, time::Duration};

    fn create_disseminator_instances(
        count: u64,
        base_port: u16,
    ) -> (Vec<SecretKey>, Vec<TrivialDisseminator<UdpNetwork>>) {
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
                all2all_address: String::new(),
                disseminator_address: format!("127.0.0.1:{}", base_port + i as u16),
                repair_address: String::new(),
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
        let shreds = RegularShredder::shred(slice, &sks[0]).unwrap();

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
