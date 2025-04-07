// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use moka::future::Cache;
use rand::prelude::*;
use tracing::warn;

use crate::network::{Network, NetworkError, NetworkMessage};
use crate::shredder::Shred;
use crate::{Slot, ValidatorId, ValidatorInfo};

use super::Disseminator;

const DEFAULT_FANOUT: usize = 200;
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
/// Only contais the information relevant for sending and receiving shreds.
#[derive(Clone, Debug)]
struct TurbineTree {
    root: ValidatorId,
    parent: Option<ValidatorId>,
    children: Vec<ValidatorId>,
}

impl<N: Network> Turbine<N> {
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
    #[must_use]
    pub const fn with_fanout(mut self, fanout: usize) -> Self {
        self.fanout = fanout;
        self
    }

    /// Sends the shred to the correct Turbine tree's root validator.
    /// Which Turbine tree to use is determined by the slot and shred index.
    ///
    /// # Errors
    ///
    /// Returns an error if the send operation on the underlying network fails.
    pub async fn send_shred_to_root(&self, shred: &Shred) -> Result<(), NetworkError> {
        // TODO: fix duplicate use indices between data and coding shreds
        let tree = self.get_tree(shred.slot(), shred.index_in_slot()).await;
        let root = tree.get_root();
        let msg = NetworkMessage::Shred(shred.clone());
        let addr = &self.validators[root as usize].disseminator_address;
        self.network.send(&msg, &addr).await
    }

    /// Forwards the shred to all our children in the correct Turbine tree.
    /// Which Turbine tree to use is determined by the slot and shred index.
    ///
    /// # Errors
    ///
    /// Returns an error if the send operation on the underlying network fails.
    pub async fn forward_shred(&self, shred: &Shred) -> Result<(), NetworkError> {
        let tree = self.get_tree(shred.slot(), shred.index_in_slot()).await;
        let msg = NetworkMessage::Shred(shred.clone());
        for child in tree.get_children() {
            let addr = &self.validators[*child as usize].disseminator_address;
            self.network.send(&msg, &addr).await?;
        }
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

impl<N: Network> Disseminator for Turbine<N> {
    async fn send(&self, shred: &Shred) -> Result<(), NetworkError> {
        self.send_shred_to_root(shred).await
    }

    async fn forward(&self, shred: &Shred) -> Result<(), NetworkError> {
        self.forward_shred(shred).await
    }

    async fn receive(&self) -> Result<Shred, NetworkError> {
        loop {
            match self.network.receive().await? {
                NetworkMessage::Shred(s) => return Ok(s),
                m => warn!("unexpected message type for Turbine: {:?}", m),
            }
        }
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
        let mut validator_ids: Vec<_> = validators.iter().map(|v| v.id).collect();
        let seed = [slot.to_be_bytes(), shred.to_be_bytes(), [0; 8], [0; 8]].concat();
        let mut rng = StdRng::from_seed(seed.try_into().unwrap());
        // TODO: shuffle stake weighted
        validator_ids.shuffle(&mut rng);

        let own_pos = validator_ids.iter().position(|v| *v == own_id).unwrap();
        let root = validator_ids[0];
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
    use super::*;

    use crate::crypto::aggsig::SecretKey;
    use crate::network::UdpNetwork;
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, Slice, TOTAL_SHREDS};

    use tokio::{sync::Mutex, task};

    use std::{collections::HashSet, sync::Arc, time::Duration};

    fn create_validator_info(count: u64) -> (Vec<SecretKey>, Vec<ValidatorInfo>) {
        let mut sks = Vec::new();
        let mut validators = Vec::new();
        for i in 0..count {
            sks.push(SecretKey::new(&mut rand::rng()));
            validators.push(ValidatorInfo {
                id: i,
                stake: 1,
                pubkey: sks[i as usize].to_pk(),
                all2all_address: String::new(),
                disseminator_address: String::new(),
                repair_address: String::new(),
            });
        }
        (sks, validators)
    }

    fn create_turbine_instances(
        validators: &mut [ValidatorInfo],
        base_port: u16,
    ) -> Vec<Turbine<UdpNetwork>> {
        for (i, v) in validators.iter_mut().enumerate() {
            v.disseminator_address = format!("127.0.0.1:{}", base_port + i as u16);
        }
        let mut disseminators = Vec::new();
        for i in 0..validators.len() {
            let network = UdpNetwork::new(base_port + i as u16);
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
            let tree = TurbineTree::new(&validators, 200, v, 0, 0);
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
            let tree = TurbineTree::new(&validators, 200, v, 0, 0);
            assert!(tree.get_children().len() <= 200);
            let tree = TurbineTree::new(&validators, 1, v, 0, 0);
            assert!(tree.get_children().len() <= 1);
            let tree = TurbineTree::new(&validators, 2, v, 0, 0);
            assert!(tree.get_children().len() <= 2);
            let tree = TurbineTree::new(&validators, 400, v, 0, 0);
            assert!(tree.get_children().len() <= 400);
            let tree = TurbineTree::new(&validators, 1000, v, 0, 0);
            assert!(tree.get_children().len() <= 500);
        }
    }

    #[tokio::test]
    async fn dissemination() {
        let (sks, mut validators) = create_validator_info(10);
        let mut disseminators = create_turbine_instances(&mut validators, 4000);
        let slice = Slice {
            slot: 0,
            slice_index: 0,
            is_last: true,
            merkle_root: None,
            data: vec![42; MAX_DATA_PER_SLICE],
        };
        let shreds = RegularShredder::shred(&slice, &sks[0]).unwrap();

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

        tokio::time::sleep(Duration::from_millis(100)).await;

        // non-leaders should have received all shreds via Turbine
        assert_eq!(*shreds_received.lock().await, 9 * TOTAL_SHREDS);
        task_leader.abort();
        for task in tasks {
            task.abort();
        }
    }
}
