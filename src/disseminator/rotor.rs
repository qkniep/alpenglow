// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of Alpenglow's new Rotor block dissemination protocol.
//!
//! This is an evolution of Solana's original Turbine block dissemination protocol.
//! Instead of a multi-layered tree, it always uses a single layer of relayers.
//!
//! Rotor can be instantiated with any [`QuorumSamplingStrategy`].
//! Therefore, this module also provides multiple implementations of such.
//! See also, the [`sampling_strategy`] module.
//!
//! For an implementation of Turbine, see [`crate::disseminator::turbine::Turbine`].

pub mod sampling_strategy;

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use rand::prelude::*;

use self::sampling_strategy::PartitionSampler;
pub use self::sampling_strategy::{
    FaitAccompli1Sampler, IidQuorumSampler, QuorumSamplingStrategy, SamplingStrategy,
    StakeWeightedSampler,
};
use super::Disseminator;
use crate::consensus::EpochRegistry;
use crate::network::{Network, ShredNetwork};
use crate::shredder::{Shred, TOTAL_SHREDS};
use crate::{Epoch, Slot, ValidatorIndex, ValidatorInfo};

/// Factory building a sampling strategy from a given epoch's validator set.
type SamplerFactory<S> = Box<dyn Fn(Vec<ValidatorInfo>) -> S + Send + Sync>;

/// Rotor is a new block dissemination protocol presented together with Alpenglow.
///
/// Uses a [`QuorumSamplingStrategy`] to select all relays for a slice at once.
///
/// Relay sampling is *epoch-relative*: the sampling strategy is built per epoch
/// from that epoch's validator set (lazily, then cached), so relays for a shred
/// are always drawn from the set of the shred's epoch — correct even as
/// validators join and leave and the set size changes.
pub struct Rotor<N: Network, S: QuorumSamplingStrategy> {
    network: N,
    /// Builds a sampler for an epoch from its validator set.
    make_sampler: SamplerFactory<S>,
    /// Per-epoch sampler cache, built lazily on the first shred of each epoch.
    samplers: Mutex<BTreeMap<Epoch, S>>,
    epoch_info: Arc<EpochRegistry>,
}

impl<N: Network> Rotor<N, IidQuorumSampler<StakeWeightedSampler>> {
    /// Creates a new Rotor instance with the default sampling strategy.
    ///
    /// Provided `network` will be used to send and receive shreds. Samplers are
    /// built per epoch from `epoch_info`'s validator sets.
    pub fn new(network: N, epoch_info: Arc<EpochRegistry>) -> Self {
        Self {
            network,
            make_sampler: Box::new(|validators| {
                StakeWeightedSampler::new(validators).into_quorum_strategy(TOTAL_SHREDS)
            }),
            samplers: Mutex::new(BTreeMap::new()),
            epoch_info,
        }
    }
}

impl<N: Network> Rotor<N, FaitAccompli1Sampler<PartitionSampler>> {
    /// Creates a new Rotor instance with the FA1 sampling strategy.
    ///
    /// Provided `network` will be used to send and receive shreds. Samplers are
    /// built per epoch from `epoch_info`'s validator sets.
    pub fn new_fa1(network: N, epoch_info: Arc<EpochRegistry>) -> Self {
        Self {
            network,
            make_sampler: Box::new(|validators| {
                FaitAccompli1Sampler::new_with_partition_fallback(validators, TOTAL_SHREDS as u64)
            }),
            samplers: Mutex::new(BTreeMap::new()),
            epoch_info,
        }
    }
}

impl<N, S: QuorumSamplingStrategy + Clone> Rotor<N, S>
where
    N: ShredNetwork,
{
    /// Sends the shred to the correct relay.
    #[hotpath::measure]
    async fn send_as_leader(&self, shred: &Shred) -> std::io::Result<()> {
        let slot = shred.payload().header.slot;
        let Some(epoch_info) = self.epoch_info.for_slot(slot) else {
            return Ok(());
        };
        let Some(relay) = self.sample_relay(shred) else {
            return Ok(());
        };
        let v = epoch_info.validator(relay);
        self.network.send(shred, v.disseminator_address).await
    }

    /// Broadcasts a shred to all validators except for the leader and itself.
    /// Does nothing if we are not the dedicated relay for this shred.
    #[hotpath::measure]
    async fn broadcast_if_relay(&self, shred: &Shred) -> std::io::Result<()> {
        let slot = shred.payload().header.slot;
        let Some(epoch_info) = self.epoch_info.for_slot(slot) else {
            return Ok(());
        };
        let leader = epoch_info.leader(slot).id;

        // do nothing if we are not the relay
        let Some(relay) = self.sample_relay(shred) else {
            return Ok(());
        };
        if self.epoch_info.own_index_for_slot(slot) != Some(relay) {
            return Ok(());
        }

        // otherwise, broadcast
        let to = epoch_info
            .validators()
            .iter()
            .filter(|v| v.id != leader && v.id != relay)
            .map(|v| v.disseminator_address);
        self.network.send_to_many(shred, to).await?;
        Ok(())
    }

    /// Deterministically samples the relay for a given shred.
    ///
    /// Seeds an RNG per slice and calls [`QuorumSamplingStrategy::sample_quorum`]
    /// on the shred's epoch's sampler, then picks the relay at the shred's
    /// position. Returns `None` if the shred's epoch is not installed.
    fn sample_relay(&self, shred: &Shred) -> Option<ValidatorIndex> {
        let slot = shred.payload().header.slot;
        let slice = shred.payload().header.slice_index.inner();
        let shred_index = shred.payload().shred_index.inner();

        let sampler = self.sampler_for(slot)?;
        let seed = [
            slot.inner().to_be_bytes(),
            slice.to_be_bytes(),
            [0; 8],
            [0; 8],
        ]
        .concat();
        let mut rng = StdRng::from_seed(seed.try_into().unwrap());
        let relays = sampler.sample_quorum(&mut rng);
        Some(relays[shred_index])
    }

    /// Returns the sampling strategy for `slot`'s epoch, building and caching it
    /// on first use. Returns `None` if that epoch's set is not installed.
    fn sampler_for(&self, slot: Slot) -> Option<S> {
        let epoch = slot.epoch();
        let mut cache = self.samplers.lock().unwrap();
        if let Some(sampler) = cache.get(&epoch) {
            return Some(sampler.clone());
        }
        let validators = self.epoch_info.for_slot(slot)?.validators().to_vec();
        let sampler = (self.make_sampler)(validators);
        cache.insert(epoch, sampler.clone());
        Some(sampler)
    }
}

#[async_trait]
impl<N, S: QuorumSamplingStrategy + Clone + Send + Sync + 'static> Disseminator for Rotor<N, S>
where
    N: ShredNetwork,
{
    async fn send(&self, shred: &Shred) -> std::io::Result<()> {
        Self::send_as_leader(self, shred).await
    }

    async fn forward(&self, shred: &Shred) -> std::io::Result<()> {
        Self::broadcast_if_relay(self, shred).await
    }

    async fn receive(&self) -> std::io::Result<Shred> {
        self.network.receive().await
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::sync::Arc;
    use std::time::Duration;

    use tokio::sync::Mutex;
    use tokio::task;

    use super::*;
    use crate::consensus::EpochInfo;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::network::{UdpNetwork, dontcare_sockaddr, localhost_ip_sockaddr};
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, TOTAL_SHREDS};
    use crate::types::slice::create_slice_with_invalid_txs;
    use crate::{Stake, ValidatorIndex, ValidatorInfo};

    type MyRotor = Rotor<UdpNetwork<Shred, Shred>, IidQuorumSampler<StakeWeightedSampler>>;

    fn create_rotor_instances(count: u64, base_port: u16) -> (Vec<SecretKey>, Vec<MyRotor>) {
        let mut sks = Vec::new();
        let mut voting_sks = Vec::new();
        let mut validators = Vec::new();
        for i in 0..count {
            sks.push(SecretKey::new(&mut rand::rng()));
            voting_sks.push(aggsig::SecretKey::new(&mut rand::rng()));
            validators.push(ValidatorInfo {
                id: ValidatorIndex::new(i),
                stake: Stake::new(1),
                pubkey: sks[i as usize].to_pk(),
                voting_pubkey: voting_sks[i as usize].to_pk(),
                all2all_address: dontcare_sockaddr(),
                disseminator_address: localhost_ip_sockaddr(base_port + i as u16),
                repair_requester_address: dontcare_sockaddr(),
                repair_responder_address: dontcare_sockaddr(),
            });
        }

        let epoch_info = EpochInfo::new(validators.clone());
        let mut rotors = Vec::new();
        for i in 0..count {
            let v = ValidatorIndex::new(i);
            let registry = Arc::new(EpochRegistry::single(v, epoch_info.clone()));
            let network = UdpNetwork::new(base_port + i as u16);
            rotors.push(Rotor::new(network, registry));
        }
        (sks, rotors)
    }

    async fn test_rotor_dissemination(count: u64, base_port: u16) {
        let (sks, mut rotors) = create_rotor_instances(count, base_port);
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let shreds = RegularShredder::default().shred(slice, &sks[0]).unwrap();

        let mut shreds_received = Vec::with_capacity(rotors.len());
        (0..rotors.len()).for_each(|_| shreds_received.push(Arc::new(Mutex::new(HashSet::new()))));
        let mut rotor_tasks = Vec::with_capacity(rotors.len());

        // forward & receive shreds on "non-leader" Rotor instance
        for i in 0..rotors.len() - 1 {
            let shreds_received = shreds_received[i].clone();
            let rotor_non_leader = rotors.pop().unwrap();
            rotor_tasks.push(task::spawn(async move {
                loop {
                    match rotor_non_leader.receive().await {
                        Ok(shred) => {
                            rotor_non_leader.forward(&shred).await.unwrap();
                            let mut guard = shreds_received.lock().await;
                            assert!(!guard.contains(&*shred.payload().shred_index));
                            guard.insert(*shred.payload().shred_index);
                        }
                        _ => continue,
                    }
                }
            }));
        }

        tokio::time::sleep(Duration::from_millis(10)).await;

        assert_eq!(rotors.len(), 1);
        for shred in shreds {
            rotors[0].send(shred.as_shred()).await.unwrap();
        }

        // forward shreds on the "leader" Rotor instance
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
        for i in 0..(count - 1) {
            assert_eq!(shreds_received[i as usize].lock().await.len(), TOTAL_SHREDS);
        }
        rotor_task_leader.abort();
        for task in rotor_tasks {
            task.abort();
        }
    }

    #[tokio::test]
    async fn two_instances() {
        test_rotor_dissemination(2, 3000).await
    }

    #[tokio::test]
    async fn many_instances() {
        test_rotor_dissemination(10, 3100).await
    }
}
