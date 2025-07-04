// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding blocks for each slot.
//!
//!

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use log::{debug, trace};
use tokio::sync::mpsc::Sender;

use crate::crypto::{Hash, MerkleTree};
use crate::shredder::{self, RegularShredder, Shred, Shredder, Slice};
use crate::{Block, Slot};

use super::epoch_info::EpochInfo;
use super::votor::VotorEvent;

/// Information about a block within a slot.
#[derive(Clone, Copy, Debug)]
pub struct BlockInfo {
    pub(crate) hash: Hash,
    pub(crate) parent_slot: Slot,
    pub(crate) parent_hash: Hash,
}

impl From<&Block> for BlockInfo {
    fn from(block: &Block) -> Self {
        BlockInfo {
            hash: block.block_hash,
            parent_slot: block.parent,
            parent_hash: block.parent_hash,
        }
    }
}

/// Blockstore is the fundamental data structure holding block data per slot.
// TODO: extract state for each slot into struct?
pub struct Blockstore {
    /// Stores raw shreds per slice, indexed by slot and slice index.
    shreds: BTreeMap<(Slot, usize), Vec<Shred>>,
    /// Stores so far reconstructed slices, indexed by slot and slice index.
    slices: BTreeMap<(Slot, usize), Slice>,
    /// Stores actual fully reconstructed block data for all relevant blocks.
    blocks: BTreeMap<(Slot, Hash), Block>,
    /// Holds currently canonical block hash for a given slot number.
    canonical: BTreeMap<Slot, Hash>,
    /// Holds hashes of alternative blocks for a given slot number.
    alternatives: BTreeMap<Slot, Vec<Hash>>,
    /// Indicates for which slots we already received at least one shred.
    first_shred_seen: BTreeSet<Slot>,
    /// Stores double-Merkle tree for each canonical block.
    double_merkle_trees: BTreeMap<Slot, MerkleTree>,
    /// Stores last slice index for each slot.
    last_slices: BTreeMap<Slot, usize>,

    /// Event channel for sending notifications to Votor.
    votor_channel: Sender<VotorEvent>,
    /// Information about all active validators.
    epoch_info: Arc<EpochInfo>,
    /// Cache of previously verified Merkle roots.
    merkle_root_cache: HashMap<(Slot, usize), Hash>,
}

impl Blockstore {
    /// Initializes a new empty blockstore.
    ///
    /// For each later reconstructed block this blockstore will send a
    /// [`VotorEvent::Block`] to the provided `votor_channel`.
    pub fn new(epoch_info: Arc<EpochInfo>, votor_channel: Sender<VotorEvent>) -> Self {
        Self {
            shreds: BTreeMap::new(),
            slices: BTreeMap::new(),
            blocks: BTreeMap::new(),
            canonical: BTreeMap::new(),
            alternatives: BTreeMap::new(),
            first_shred_seen: BTreeSet::new(),
            double_merkle_trees: BTreeMap::new(),
            last_slices: BTreeMap::new(),
            votor_channel,
            epoch_info,
            merkle_root_cache: HashMap::new(),
        }
    }

    /// Stores a new shred in the blockstore.
    ///
    /// Reconstructs the corresponding slice and block if possible and necessary.
    /// If the added shred belongs to the last slice, all later shreds are deleted.
    ///
    /// Returns `Some(slot, block_info)` if a block was reconstructed, `None` otherwise.
    /// In the `Some`-case, `block_info` is the [`BlockInfo`] of the reconstructed block.
    #[fastrace::trace(short_name = true)]
    pub async fn add_shred(&mut self, shred: Shred) -> Option<(Slot, BlockInfo)> {
        let slot = shred.payload().slot;
        let slice = shred.payload().slice_index;
        let index = shred.payload().index_in_slice;
        let is_last_slice = shred.payload().is_last_slice;
        let slice_shreds = self.shreds.entry((slot, slice)).or_default();

        // check Merkle root and signature
        let leader_pk = &self.epoch_info.leader(slot).pubkey;
        let merkle_root = self.merkle_root_cache.get(&(slot, slice));
        if !shred.verify(leader_pk, merkle_root) {
            debug!("dropping shred with invalid root");
            return None;
        } else if merkle_root.is_none() {
            self.merkle_root_cache
                .insert((slot, slice), shred.merkle_root);
        }

        // store and handle this shred if and only if:
        //   - it is not yet stored in the blockstore
        //   - it is not (known to be) after the last slice
        let exists = slice_shreds.iter().any(|s| {
            s.payload().index_in_slice == index
                && shred.payload_type.is_data() == s.payload_type.is_data()
        });
        let after_last = self
            .last_slices
            .get(&slot)
            .is_some_and(|last_slice| slice > *last_slice);
        if exists || after_last {
            return None;
        }
        slice_shreds.push(shred);

        // store last slice index, delete later shreds
        if is_last_slice && !self.last_slices.contains_key(&slot) {
            self.last_slices.insert(slot, slice);

            // delete shreds after last slice, if there are any
            let keys_to_delete: Vec<_> = self
                .shreds
                .range(&(slot, slice + 1)..&(slot + 1, 0))
                .map(|(k, _)| k)
                .copied()
                .collect();
            for key in keys_to_delete {
                self.shreds.remove(&key);
            }
        }

        // maybe send first shred notification
        if self.first_shred_seen.insert(slot) {
            let event = VotorEvent::FirstShred(slot);
            self.votor_channel.send(event).await.unwrap();
        }

        // maybe reconstruct slice and block
        if self.try_reconstruct_slice(slot, slice) {
            self.try_reconstruct_block(slot).await
        } else {
            None
        }
    }

    /// Reconstructs the slice if the blockstore contains enough shreds.
    ///
    /// Returns `true` if a slice was reconstructed, `false` otherwise.
    fn try_reconstruct_slice(&mut self, slot: Slot, slice: usize) -> bool {
        let slice_shreds = self.shreds.get(&(slot, slice)).unwrap();
        if slice_shreds.len() < shredder::DATA_SHREDS || self.get_slice(slot, slice).is_some() {
            return false;
        }

        let reconstructed_slice = RegularShredder::deshred(slice_shreds).unwrap();
        self.slices.insert((slot, slice), reconstructed_slice);
        trace!("reconstructed slice {slice} in slot {slot}");
        true
    }

    /// Reconstructs the block if the blockstore contains all slices.
    ///
    /// Returns `Some(slot, block_info)` if a block was reconstructed, `None` otherwise.
    /// In the `Some`-case, `block_info` is the [`BlockInfo`] of the reconstructed block.
    async fn try_reconstruct_block(&mut self, slot: Slot) -> Option<(Slot, BlockInfo)> {
        if self.canonical_block_hash(slot).is_some() {
            trace!("already have block for slot {slot}");
            return None;
        }
        let last_slice = self.last_slices.get(&slot)?;
        if self.stored_slices_for_slot(slot) != last_slice + 1 {
            trace!("don't have all slices for slot {slot} yet");
            return None;
        }

        // calculate double-Merkle tree & block hash
        let merkle_roots: Vec<_> = self
            .slices
            .range(&(slot, 0)..)
            .take_while(|(key, _)| key.0 == slot)
            .map(|(_, s)| s.merkle_root.as_ref().unwrap())
            .collect();
        let tree = MerkleTree::new(&merkle_roots);
        let block_hash = tree.get_root();
        self.double_merkle_trees.insert(slot, tree);

        // reconstruct block header
        let first_slice = self.slices.get(&(slot, 0)).unwrap();
        let parent_slot = u64::from_be_bytes(first_slice.data[0..8].try_into().unwrap());
        let parent_hash = first_slice.data[8..40].try_into().unwrap();
        self.canonical.insert(slot, block_hash);
        // TODO: reconstruct actual block content
        let block = Block {
            slot,
            block_hash,
            parent: parent_slot,
            parent_hash,
            transactions: vec![],
        };
        let block_info = BlockInfo::from(&block);
        self.blocks.insert((slot, block_hash), block);

        // clean up raw slices
        for slice_index in 0..=*last_slice {
            self.slices.remove(&(slot, slice_index));
        }

        // notify Votor of block and print block info
        let event = VotorEvent::Block { slot, block_info };
        self.votor_channel.send(event).await.unwrap();
        let h = &hex::encode(block_hash)[..8];
        let ph = &hex::encode(parent_hash)[..8];
        debug!("reconstructed block {h} in slot {slot} with parent {ph} in slot {parent_slot}");
        Some((slot, block_info))
    }

    /// Deletes everything before the given `slot` from the blockstore.
    pub fn prune(&mut self, slot: Slot) {
        self.shreds = self.shreds.split_off(&(slot, 0));
        self.slices = self.slices.split_off(&(slot, 0));
        self.blocks = self.blocks.split_off(&(slot, Hash::default()));
        self.canonical = self.canonical.split_off(&slot);
        self.alternatives = self.alternatives.split_off(&slot);
    }

    /// Gives the canonical block hash for a given `slot`, if any.
    ///
    /// This is usually the first version of the block stored in the blockstore.
    /// Returns `None` if blockstore does not hold any version of the block yet.
    #[must_use]
    pub fn canonical_block_hash(&self, slot: Slot) -> Option<Hash> {
        self.canonical.get(&slot).copied()
    }

    /// Gives any relevant alternative block hashes for a given slot, if any.
    #[must_use]
    pub fn alternative_block_hashes(&self, slot: Slot) -> Option<&[Hash]> {
        self.alternatives.get(&slot).map(|v| v.as_ref())
    }

    /// Gives reference to stored block for the given `slot` and `hash`.
    ///
    /// Returns `None` if blockstore does not hold that block yet.
    pub fn get_block(&self, slot: Slot, hash: Hash) -> Option<&Block> {
        self.blocks.get(&(slot, hash))
    }

    /// Gives reference to stored slice for the given `slot` and `slice` index.
    ///
    /// Returns `None` if blockstore does not hold that slice yet.
    pub fn get_slice(&self, slot: Slot, slice: usize) -> Option<&Slice> {
        self.slices.get(&(slot, slice))
    }

    /// Gives reference to stored shred for the given `slot`, `slice` and `shred` index.
    ///
    /// Returns `None` if blockstore does not hold that shred yet.
    pub fn get_shred(&self, slot: Slot, slice: usize, shred: usize) -> Option<&Shred> {
        self.shreds
            .get(&(slot, slice))
            .and_then(|v| v.iter().find(|s| s.payload().index_in_slice == shred))
    }

    /// Gives the number of stored slices for a given `slot`.
    pub fn stored_slices_for_slot(&self, slot: Slot) -> usize {
        self.slices
            .range(&(slot, 0)..)
            .take_while(|(key, _)| key.0 == slot)
            .count()
    }

    /// Gives the number of stored shreds for a given `slot` (across all slices).
    pub fn stored_shreds_for_slot(&self, slot: Slot) -> usize {
        self.shreds
            .range(&(slot, 0)..)
            .take_while(|(key, _)| key.0 == slot)
            .map(|(_, slice)| slice.len())
            .sum()
    }

    /// Gives the number of stored shreds for a given slot and slice.
    pub fn stored_shreds_for_slice(&self, slot: Slot, slice: usize) -> usize {
        self.shreds.get(&(slot, slice)).map_or(0, Vec::len)
    }

    /// Generates a Merkle proof for the given `slice` within the given `slot`.
    ///
    /// # Panics
    ///
    /// Panics if the double-Merkle tree for the given `slot` does not exist.
    #[must_use]
    pub fn create_double_merkle_proof(&self, slot: Slot, slice: usize) -> Vec<Hash> {
        let tree = self.double_merkle_trees.get(&slot).unwrap();
        tree.create_proof(slice)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ValidatorInfo;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{DATA_SHREDS, MAX_DATA_PER_SLICE, TOTAL_SHREDS};

    use color_eyre::Result;
    use rand::RngCore;
    use tokio::sync::mpsc;

    fn test_setup(tx: Sender<VotorEvent>) -> (SecretKey, Blockstore) {
        let sk = SecretKey::new(&mut rand::rng());
        let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
        let info = ValidatorInfo {
            id: 0,
            stake: 1,
            pubkey: sk.to_pk(),
            voting_pubkey: voting_sk.to_pk(),
            all2all_address: String::new(),
            disseminator_address: String::new(),
            repair_address: String::new(),
        };
        let validators = vec![info];
        let epoch_info = EpochInfo::new(0, validators);
        (sk, Blockstore::new(Arc::new(epoch_info), tx))
    }

    fn create_random_block(slot: Slot, num_slices: usize) -> Vec<Slice> {
        let mut slices = Vec::new();
        let mut rng = rand::rng();
        for slice_index in 0..num_slices {
            let mut buf = vec![0u8; MAX_DATA_PER_SLICE];
            rng.fill_bytes(&mut buf);
            slices.push(Slice {
                slot,
                slice_index,
                is_last: slice_index == num_slices - 1,
                merkle_root: None,
                data: buf,
            });
        }
        slices
    }

    #[tokio::test]
    async fn store_simple_block() -> Result<()> {
        let (tx, rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.canonical_block_hash(0).is_none());

        // generate two slices for slot 0
        let slices = create_random_block(0, 2);

        // first slice is not enough
        let shreds = RegularShredder::shred(&slices[0], &sk)?;
        for shred in shreds {
            blockstore.add_shred(shred).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_none());
        assert_eq!(blockstore.blocks.len(), 0);

        // after second slice we should have the block
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds {
            blockstore.add_shred(shred).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_some());
        assert_eq!(blockstore.blocks.len(), 1);

        drop(rx);
        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_shreds() -> Result<()> {
        let (tx, rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.canonical_block_hash(0).is_none());

        // generate a single slice for slot 0
        let slices = create_random_block(0, 1);

        // insert shreds in reverse order
        let shreds = RegularShredder::shred(&slices[0], &sk)?;
        for shred in shreds.into_iter().rev() {
            blockstore.add_shred(shred).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_some());

        drop(rx);
        Ok(())
    }

    #[tokio::test]
    async fn just_enough_shreds() -> Result<()> {
        let (tx, rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.canonical_block_hash(0).is_none());

        // generate a larger block for slot 0
        let slices = create_random_block(0, 4);
        assert_eq!(blockstore.stored_slices_for_slot(0), 0);

        // insert just enough shreds to reconstruct slice 0 (from beginning)
        let shreds = RegularShredder::shred(&slices[0], &sk)?;
        for shred in shreds.into_iter().take(DATA_SHREDS) {
            blockstore.add_shred(shred).await;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 1);

        // insert just enough shreds to reconstruct slice 1 (from end)
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds.into_iter().skip(TOTAL_SHREDS - DATA_SHREDS) {
            blockstore.add_shred(shred).await;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 2);

        // insert just enough shreds to reconstruct slice 2 (from middle)
        let shreds = RegularShredder::shred(&slices[2], &sk)?;
        for shred in shreds.into_iter().skip(DATA_SHREDS / 2) {
            blockstore.add_shred(shred).await;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 3);

        // insert just enough shreds to reconstruct slice 3 (split)
        let shreds = RegularShredder::shred(&slices[3], &sk)?;
        for (_, shred) in shreds
            .into_iter()
            .enumerate()
            .filter(|(i, _)| *i < DATA_SHREDS / 2 || *i >= TOTAL_SHREDS - DATA_SHREDS / 2)
        {
            blockstore.add_shred(shred).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_some());

        // slices are deleted after reconstruction
        assert_eq!(blockstore.stored_slices_for_slot(0), 0);

        drop(rx);
        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_slices() -> Result<()> {
        let (tx, rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.canonical_block_hash(0).is_none());

        // generate two slices for slot 0
        let slices = create_random_block(0, 2);

        // second slice alone is not enough
        let shreds = RegularShredder::shred(&slices[0], &sk)?;
        for shred in shreds {
            blockstore.add_shred(shred).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_none());

        // stored all shreds for slot 0
        assert_eq!(blockstore.stored_shreds_for_slot(0), TOTAL_SHREDS);

        // after also also inserting first slice we should have the block
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds {
            blockstore.add_shred(shred).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_some());

        // stored all shreds
        assert_eq!(blockstore.stored_shreds_for_slot(0), 2 * TOTAL_SHREDS);

        drop(rx);
        Ok(())
    }

    #[tokio::test]
    async fn duplicate_shreds() -> Result<()> {
        let (tx, rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        let slices = create_random_block(0, 1);

        // insert many duplicate shreds
        let shreds = RegularShredder::shred(&slices[0], &sk)?;
        for shred in vec![shreds[0].clone(); 1024] {
            blockstore.add_shred(shred).await;
        }

        // should only store one copy
        assert_eq!(blockstore.stored_shreds_for_slot(0), 1);

        drop(rx);
        Ok(())
    }

    #[tokio::test]
    async fn invalid_shreds() -> Result<()> {
        let (tx, rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        let slices = create_random_block(0, 1);

        // insert many duplicate shreds
        let shreds = RegularShredder::shred(&slices[0], &sk)?;
        for shred in vec![shreds[0].clone(); 1024] {
            blockstore.add_shred(shred).await;
        }

        // should only store one copy
        assert_eq!(blockstore.stored_shreds_for_slot(0), 1);

        drop(rx);
        Ok(())
    }

    #[tokio::test]
    async fn pruning() -> Result<()> {
        let (tx, rx) = mpsc::channel(1000);
        let (sk, mut blockstore) = test_setup(tx);
        let block0 = create_random_block(0, 1);
        let block1 = create_random_block(1, 1);
        let block2 = create_random_block(2, 1);

        // insert shreds
        let mut shreds = RegularShredder::shred(&block0[0], &sk)?;
        shreds.extend(RegularShredder::shred(&block1[0], &sk)?);
        shreds.extend(RegularShredder::shred(&block2[0], &sk)?);
        for shred in shreds {
            blockstore.add_shred(shred).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_some());
        assert!(blockstore.canonical_block_hash(1).is_some());
        assert!(blockstore.canonical_block_hash(2).is_some());

        // stored all shreds
        assert_eq!(blockstore.stored_shreds_for_slot(0), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(1), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(2), TOTAL_SHREDS);

        // some (and only some) shreds deleted after partial pruning
        blockstore.prune(1);
        assert_eq!(blockstore.stored_shreds_for_slot(0), 0);
        assert_eq!(blockstore.stored_shreds_for_slot(1), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(2), TOTAL_SHREDS);

        // no shreds left after full pruning
        blockstore.prune(3);
        assert_eq!(blockstore.stored_shreds_for_slot(0), 0);
        assert_eq!(blockstore.stored_shreds_for_slot(1), 0);
        assert_eq!(blockstore.stored_shreds_for_slot(2), 0);
        let shred_count = blockstore.shreds.values().map(|s| s.len()).sum::<usize>();
        assert_eq!(shred_count, 0);

        drop(rx);
        Ok(())
    }
}
