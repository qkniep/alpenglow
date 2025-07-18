// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

pub mod sampling_strategy;

use std::sync::Arc;

use log::warn;
use rand::prelude::*;
use sampling_strategy::PartitionSampler;

use crate::consensus::EpochInfo;
use crate::network::{Network, NetworkError, NetworkMessage};
use crate::shredder::Shred;
use crate::{Slot, ValidatorId};

use super::Disseminator;

pub use sampling_strategy::{FaitAccompli1Sampler, SamplingStrategy, StakeWeightedSampler};

/// Rotor is a new block dissemination protocol presented together with Alpenglow.
pub struct Rotor<N: Network, S: SamplingStrategy> {
    network: N,
    sampler: S,
    epoch_info: Arc<EpochInfo>,
}

impl<N: Network> Rotor<N, StakeWeightedSampler> {
    /// Creates a new Rotor instance with the default sampling strategy.
    ///
    /// Contact information for all validators is provided in `validators`.
    /// Provided `network` will be used to send and receive shreds.
    pub fn new(network: N, epoch_info: Arc<EpochInfo>) -> Self {
        let validators = epoch_info.validators.clone();
        let sampler = StakeWeightedSampler::new(validators);
        Self {
            network,
            sampler,
            epoch_info,
        }
    }
}

impl<N: Network> Rotor<N, FaitAccompli1Sampler<PartitionSampler>> {
    /// Creates a new Rotor instance with the FA1 sampling strategy.
    ///
    /// Contact information for all validators is provided in `validators`.
    /// Provided `network` will be used to send and receive shreds.
    pub fn new_fa1(network: N, epoch_info: Arc<EpochInfo>) -> Self {
        let validators = epoch_info.validators.clone();
        let sampler = FaitAccompli1Sampler::new_with_partition_fallback(validators, 64);
        Self {
            network,
            sampler,
            epoch_info,
        }
    }
}

impl<N: Network, S: SamplingStrategy> Rotor<N, S> {
    /// Turns this instance into a new instance with a different sampling strategy.
    #[must_use]
    pub fn with_sampler(self, sampler: S) -> Self {
        Self { sampler, ..self }
    }

    /// Sends the shred to the correct relay.
    async fn send_as_leader(&self, shred: &Shred) -> Result<(), NetworkError> {
        let relay = self.sample_relay(shred.payload().slot, shred.payload().index_in_slot());
        let msg = NetworkMessage::Shred(shred.clone());
        let v = &self.epoch_info.validator(relay);
        self.network.send(&msg, &v.disseminator_address).await
    }

    /// Broadcasts a shred to all validators except for the leader and itself.
    /// Does nothing if we are not the dedicated relay for this shred.
    async fn broadcast_if_relay(&self, shred: &Shred) -> Result<(), NetworkError> {
        let leader = self.epoch_info.leader(shred.payload().slot).id;

        // do nothing if we are not the relay
        let relay = self.sample_relay(shred.payload().slot, shred.payload().index_in_slot());
        if self.epoch_info.own_id != relay {
            return Ok(());
        }

        // otherwise, broadcast
        let msg = NetworkMessage::Shred(shred.clone());
        let bytes = msg.to_bytes();
        for v in &self.epoch_info.validators {
            if v.id == leader || v.id == relay {
                continue;
            }
            self.network
                .send_serialized(&bytes, &v.disseminator_address)
                .await?;
        }
        Ok(())
    }

    fn sample_relay(&self, slot: Slot, shred: usize) -> ValidatorId {
        let seed = [slot.to_be_bytes(), shred.to_be_bytes(), [0; 8], [0; 8]].concat();
        let mut rng = StdRng::from_seed(seed.try_into().unwrap());
        self.sampler.sample(&mut rng)
    }
}

impl<N: Network, S: SamplingStrategy + Sync + Send + 'static> Disseminator for Rotor<N, S> {
    async fn send(&self, shred: &Shred) -> Result<(), NetworkError> {
        Self::send_as_leader(self, shred).await
    }

    async fn forward(&self, shred: &Shred) -> Result<(), NetworkError> {
        Self::broadcast_if_relay(self, shred).await
    }

    async fn receive(&self) -> Result<Shred, NetworkError> {
        loop {
            match self.network.receive().await? {
                NetworkMessage::Shred(s) => return Ok(s),
                m => warn!("unexpected message type for Rotor: {m:?}"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ValidatorInfo;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::network::UdpNetwork;
    use crate::shredder::{
        MAX_DATA_PER_SLICE, RegularShredder, ShredPayloadType, Shredder, Slice, TOTAL_SHREDS,
    };

    use tokio::sync::Mutex;
    use tokio::task;

    use std::collections::HashSet;
    use std::sync::Arc;
    use std::time::Duration;

    fn create_rotor_instances(
        count: u64,
        base_port: u16,
    ) -> (Vec<SecretKey>, Vec<Rotor<UdpNetwork, StakeWeightedSampler>>) {
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

        let mut rotors = Vec::new();
        for i in 0..count {
            let epoch_info = Arc::new(EpochInfo::new(i, validators.clone()));
            let network = UdpNetwork::new(base_port + i as u16);
            rotors.push(Rotor::new(network, epoch_info));
        }
        (sks, rotors)
    }

    #[tokio::test]
    async fn two_instances() {
        let (sks, mut rotors) = create_rotor_instances(2, 3000);
        let slice = Slice {
            slot: 0,
            slice_index: 0,
            is_last: true,
            merkle_root: None,
            data: vec![42; MAX_DATA_PER_SLICE],
        };
        let shreds = RegularShredder::shred(&slice, &sks[0]).unwrap();

        let data_shreds_received = Arc::new(Mutex::new(HashSet::new()));
        let code_shreds_received = Arc::new(Mutex::new(HashSet::new()));
        let mut rotor_tasks = Vec::new();

        // forward & receive shreds on "non-leader" Rotor instance
        for _ in 0..rotors.len() - 1 {
            let dsr = data_shreds_received.clone();
            let csr = code_shreds_received.clone();
            let rotor_non_leader = rotors.pop().unwrap();
            rotor_tasks.push(task::spawn(async move {
                loop {
                    match rotor_non_leader.receive().await {
                        Ok(shred) => {
                            rotor_non_leader.forward(&shred).await.unwrap();
                            let mut guard = match shred.payload_type {
                                ShredPayloadType::Data(_) => dsr.lock().await,
                                ShredPayloadType::Coding(_) => csr.lock().await,
                            };
                            assert!(!guard.contains(&shred.payload().index_in_slice));
                            guard.insert(shred.payload().index_in_slice);
                        }
                        _ => continue,
                    }
                }
            }));
        }

        tokio::time::sleep(Duration::from_millis(10)).await;
        for shred in shreds {
            rotors[0].send(&shred).await.unwrap();
        }

        // forward shreds on the "leader" Rotor instance
        assert_eq!(rotors.len(), 1);
        let rotor_leader = rotors.pop().unwrap();
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

        // non-leader should have received all shreds via Rotor
        assert_eq!(
            data_shreds_received.lock().await.len() + code_shreds_received.lock().await.len(),
            TOTAL_SHREDS
        );
        rotor_task_leader.abort();
        for task in rotor_tasks {
            task.abort();
        }
    }

    #[tokio::test]
    async fn many_instances() {
        let (sks, mut rotors) = create_rotor_instances(10, 3100);
        let slice = Slice {
            slot: 0,
            slice_index: 0,
            is_last: true,
            merkle_root: None,
            data: vec![42; MAX_DATA_PER_SLICE],
        };
        let shreds = RegularShredder::shred(&slice, &sks[0]).unwrap();

        let mut data_shreds_received = Vec::with_capacity(rotors.len());
        (0..rotors.len())
            .for_each(|_| data_shreds_received.push(Arc::new(Mutex::new(HashSet::new()))));
        let mut code_shreds_received = Vec::with_capacity(rotors.len());
        (0..rotors.len())
            .for_each(|_| code_shreds_received.push(Arc::new(Mutex::new(HashSet::new()))));
        let mut rotor_tasks = Vec::new();

        // forward & receive shreds on "non-leader" Rotor instance
        for i in 0..rotors.len() - 1 {
            let dsr = data_shreds_received[i].clone();
            let csr = code_shreds_received[i].clone();
            let rotor_non_leader = rotors.pop().unwrap();
            rotor_tasks.push(task::spawn(async move {
                loop {
                    match rotor_non_leader.receive().await {
                        Ok(shred) => {
                            rotor_non_leader.forward(&shred).await.unwrap();
                            let mut guard = match shred.payload_type {
                                ShredPayloadType::Data(_) => dsr.lock().await,
                                ShredPayloadType::Coding(_) => csr.lock().await,
                            };
                            assert!(!guard.contains(&shred.payload().index_in_slice));
                            guard.insert(shred.payload().index_in_slice);
                        }
                        _ => continue,
                    }
                }
            }));
        }

        tokio::time::sleep(Duration::from_millis(10)).await;
        for shred in shreds {
            rotors[0].send(&shred).await.unwrap();
        }

        // forward shreds on the "leader" Rotor instance
        assert_eq!(rotors.len(), 1);
        let rotor_leader = rotors.pop().unwrap();
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

        // non-leader instances should have received all shreds via Rotor
        for i in 0..9 {
            assert_eq!(
                data_shreds_received[i].lock().await.len()
                    + code_shreds_received[i].lock().await.len(),
                TOTAL_SHREDS
            );
        }
        rotor_task_leader.abort();
        for task in rotor_tasks {
            task.abort();
        }
    }
}
