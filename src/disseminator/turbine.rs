// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of Solana's Turbine block dissemination protocol.
//!
//! For each slot and shred index, a different Turbine tree is built.
//! Each tree corresponds to a stake-weighted shuffling of the validators.
//!
//! See also: <https://docs.anza.xyz/consensus/turbine-block-propagation>

mod weighted_shuffle;

use async_trait::async_trait;
use moka::future::Cache;
use rand::prelude::*;

pub use self::weighted_shuffle::WeightedShuffle;
use super::Disseminator;
use crate::network::{Network, ShredNetwork};
use crate::shredder::Shred;
use crate::{Slot, ValidatorId, ValidatorInfo};

/// Default fanout for the Turbine tree.
pub const DEFAULT_FANOUT: usize = 200;

/// Maximum number of different Turbine trees cached.
///
/// A [`TurbineTree`] takes roughly 1600 bytes of memory to store.
/// So, caching up to 2^16 trees occupies roughly 100 MiB of memory.
const MAX_CACHED_TREES: u64 = 65536;

/// Implementation of Solana's Turbine block dissemination protocol.
pub struct Turbine<N: Network> {
    validator_id: ValidatorId,
    validators: Vec<ValidatorInfo>,
    network: N,
    fanout: usize,
    tree_cache: Cache<(Slot, usize), TurbineTree>,
}

/// View of the Turbine tree from a specific validator's perspective.
///
/// Only contains the information relevant for sending and receiving shreds.
/// The rest of the tree is not stored, especially to make caching more efficient.
#[derive(Clone, Debug)]
pub(crate) struct TurbineTree {
    root: ValidatorId,
    #[allow(dead_code)]
    parent: Option<ValidatorId>,
    children: Vec<ValidatorId>,
}

impl<N> Turbine<N>
where
    N: ShredNetwork,
{
    /// Creates a new Turbine instance, configured with the default fanout.
    pub fn new(validator_id: ValidatorId, validators: Vec<ValidatorInfo>, network: N) -> Self {
        Self {
            validator_id,
            validators,
            network,
            fanout: DEFAULT_FANOUT,
            tree_cache: Cache::new(MAX_CACHED_TREES),
        }
    }

    /// Turns this instance into a new instance with a different fanout value.
    ///
    /// This invalidates all cached trees.
    #[must_use]
    pub fn with_fanout(mut self, fanout: usize) -> Self {
        if fanout == self.fanout {
            return self;
        }
        self.fanout = fanout;
        self.tree_cache = Cache::new(MAX_CACHED_TREES);
        self
    }

    /// Sends the shred to the correct Turbine tree's root validator.
    /// Which Turbine tree to use is determined by the slot and shred index.
    ///
    /// # Errors
    ///
    /// Returns an error if the send operation on the underlying network fails.
    pub async fn send_shred_to_root(&self, shred: &Shred) -> std::io::Result<()> {
        let tree = self
            .get_tree(shred.payload().header.slot, shred.payload().index_in_slot())
            .await;
        let root = tree.get_root();
        let addr = self.validators[root as usize].disseminator_address;
        self.network.send(shred, addr).await
    }

    /// Forwards the shred to all our children in the correct Turbine tree.
    /// Which Turbine tree to use is determined by the slot and shred index.
    ///
    /// # Errors
    ///
    /// Returns an error if the send operation on the underlying network fails.
    pub async fn forward_shred(&self, shred: &Shred) -> std::io::Result<()> {
        let tree = self
            .get_tree(shred.payload().header.slot, shred.payload().index_in_slot())
            .await;
        let addrs = tree
            .get_children()
            .iter()
            .map(|child| self.validators[*child as usize].disseminator_address);
        self.network.send_to_many(shred, addrs).await?;
        Ok(())
    }

    /// Returns the correct Turbine tree for the given slot and shred index.
    /// If the tree is cached, it is returned, otherwise it is built and cached.
    async fn get_tree(&self, slot: Slot, shred: usize) -> TurbineTree {
        if let Some(tree) = self.tree_cache.get(&(slot, shred)).await {
            return tree;
        }
        let tree = TurbineTree::new(
            &self.validators,
            self.fanout,
            self.validator_id,
            slot,
            shred,
        );
        self.tree_cache.insert((slot, shred), tree.clone()).await;
        tree
    }
}

#[async_trait]
impl<N> Disseminator for Turbine<N>
where
    N: ShredNetwork,
{
    async fn send(&self, shred: &Shred) -> std::io::Result<()> {
        self.send_shred_to_root(shred).await
    }

    async fn forward(&self, shred: &Shred) -> std::io::Result<()> {
        self.forward_shred(shred).await
    }

    async fn receive(&self) -> std::io::Result<Shred> {
        self.network.receive().await
    }
}

impl TurbineTree {
    /// Generates a new `TurbineTree` for the given parameters.
    ///
    /// This is deterministic, i.e., same parameters result in the same tree.
    /// Only the neighborhood of the validator given by `own_id` is kept.
    pub fn new(
        validators: &[ValidatorInfo],
        fanout: usize,
        own_id: ValidatorId,
        slot: Slot,
        shred: usize,
    ) -> Self {
        // seed the RNG
        let seed = [
            b"ALPENGLOWTURBINE",
            &slot.inner().to_be_bytes()[..],
            &shred.to_be_bytes()[..],
        ]
        .concat();
        assert_eq!(seed.len(), 32);
        let mut rng = StdRng::from_seed(seed.try_into().unwrap());

        // stake-weighted shuffle
        let mut weighted_shuffle = WeightedShuffle::new(validators.iter().map(|v| v.stake));
        // TODO: remove leader
        let validator_ids: Vec<_> = weighted_shuffle
            .shuffle(&mut rng)
            .map(|i| i as ValidatorId)
            .collect();

        // find root & parent
        let root = validator_ids[0];
        let own_pos = validator_ids.iter().position(|v| *v == own_id).unwrap();
        let parent_pos = match own_pos {
            0 => None,
            _ => Some((own_pos - 1) / fanout),
        };

        // find children
        let offset = own_pos * fanout + 1;
        let children = validator_ids
            .iter()
            .skip(offset)
            .take(fanout)
            .copied()
            .collect();

        Self {
            root,
            parent: parent_pos.map(|p| validator_ids[p]),
            children,
        }
    }

    /// Gives the root validator of this Turbine tree.
    pub const fn get_root(&self) -> ValidatorId {
        self.root
    }

    /// Gives the parent of this validator in the Turbine tree.
    /// Returns `None` iff this validator is the root of the tree.
    #[allow(dead_code)]
    pub const fn get_parent(&self) -> Option<ValidatorId> {
        self.parent
    }

    /// Gives the list of children of this validator in the Turbine tree.
    pub fn get_children(&self) -> &[ValidatorId] {
        &self.children
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
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::network::simulated::SimulatedNetworkCore;
    use crate::network::{SimulatedNetwork, dontcare_sockaddr, localhost_ip_sockaddr};
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, TOTAL_SHREDS};
    use crate::types::slice::create_slice_with_invalid_txs;

    fn create_validator_info(count: u64) -> (Vec<SecretKey>, Vec<ValidatorInfo>) {
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
                disseminator_address: dontcare_sockaddr(),
                repair_request_address: dontcare_sockaddr(),
                repair_response_address: dontcare_sockaddr(),
            });
        }
        (sks, validators)
    }

    async fn create_turbine_instances(
        validators: &mut [ValidatorInfo],
    ) -> Vec<Turbine<SimulatedNetwork<Shred, Shred>>> {
        let core = Arc::new(
            SimulatedNetworkCore::default()
                .with_jitter(0.0)
                .with_packet_loss(0.0),
        );
        for (i, v) in validators.iter_mut().enumerate() {
            v.disseminator_address = localhost_ip_sockaddr(i.try_into().unwrap());
        }
        let mut disseminators = Vec::new();
        for i in 0..validators.len() {
            let network = core.join_unlimited(i as ValidatorId).await;
            let turbine = Turbine::new(i as ValidatorId, validators.to_vec(), network);
            disseminators.push(turbine);
        }
        disseminators
    }

    #[test]
    fn tree() {
        let (_, validators) = create_validator_info(2000);
        let mut trees = Vec::new();
        for v in 0..validators.len() {
            let v = v as ValidatorId;
            let tree = TurbineTree::new(&validators, 200, v, Slot::new(0), 0);
            trees.push((v, tree));
        }

        let root = trees[0].1.get_root();
        for (v, tree) in &trees {
            // all validators know the correct root
            assert_eq!(tree.get_root(), root);
            // validator is never its own parent
            assert!(tree.get_parent().is_none() || tree.get_parent().unwrap() != *v);
            // validator never appears in its own children
            assert!(!tree.get_children().contains(v));
            // no validator appears multiple times in the tree
            let children: HashSet<_> = tree.get_children().iter().collect();
            assert_eq!(children.len(), tree.get_children().len());
            assert!(!tree.get_children().contains(&root));
            if let Some(parent) = tree.get_parent() {
                assert!(!children.contains(&parent));
            }
            // parent-child compatibility
            for child in tree.get_children() {
                let childs_parent = trees[*child as usize].1.get_parent();
                assert_eq!(childs_parent, Some(*v));
            }
            if let Some(parent) = tree.get_parent() {
                let parents_children = trees[parent as usize].1.get_children();
                assert!(parents_children.contains(v));
            }
        }
    }

    #[test]
    fn tree_fanouts() {
        let (_, validators) = create_validator_info(500);
        for v in 0..validators.len() {
            let v = v as ValidatorId;
            let tree = TurbineTree::new(&validators, 200, v, Slot::new(0), 0);
            assert!(tree.get_children().len() <= 200);
            let tree = TurbineTree::new(&validators, 1, v, Slot::new(0), 0);
            assert!(tree.get_children().len() <= 1);
            let tree = TurbineTree::new(&validators, 2, v, Slot::new(0), 0);
            assert!(tree.get_children().len() <= 2);
            let tree = TurbineTree::new(&validators, 400, v, Slot::new(0), 0);
            assert!(tree.get_children().len() <= 400);
            let tree = TurbineTree::new(&validators, 1000, v, Slot::new(0), 0);
            assert!(tree.get_children().len() <= 500);
        }
    }

    #[tokio::test]
    async fn dissemination() {
        let (sks, mut validators) = create_validator_info(10);
        let mut disseminators = create_turbine_instances(&mut validators).await;
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
        let leader = disseminators.pop().unwrap();
        let task_leader = task::spawn(async move {
            loop {
                match leader.receive().await {
                    Ok(shred) => {
                        leader.forward(&shred).await.unwrap();
                    }
                    _ => continue,
                }
            }
        });

        // wait for shreds to arrive
        // needs to be longer than the latency of the simulated network
        tokio::time::sleep(Duration::from_millis(500)).await;

        // non-leaders should have received all shreds via Turbine
        assert_eq!(*shreds_received.lock().await, 9 * TOTAL_SHREDS);
        task_leader.abort();
        for task in tasks {
            task.abort();
        }
    }
}
