// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding blocks for each slot.
//!
//!

use std::collections::BTreeMap;
use std::sync::Arc;

use log::{debug, trace, warn};
use tokio::sync::mpsc::Sender;

use crate::crypto::signature::PublicKey;
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
pub struct Blockstore {
    ///
    block_data: BTreeMap<Slot, SlotBlockData>,

    /// Event channel for sending notifications to Votor.
    votor_channel: Sender<VotorEvent>,
    /// Information about all active validators.
    epoch_info: Arc<EpochInfo>,
}

///
pub struct SlotBlockData {
    ///
    slot: Slot,
    /// Stores raw shreds per slice, indexed by slot and slice index.
    shreds: BTreeMap<usize, Vec<Shred>>,
    /// Stores so far reconstructed slices, indexed by slot and slice index.
    slices: BTreeMap<usize, Slice>,
    ///
    // repair_shreds: BTreeMap<(Hash, usize), Vec<Shred>>,
    ///
    // repair_slices: BTreeMap<(Hash, usize), Slice>,
    /// Stores actual fully reconstructed block data for all relevant blocks.
    blocks: BTreeMap<Hash, Block>,
    /// Holds currently canonical block hash for a given slot number.
    canonical: Option<Hash>,
    /// Holds hashes of alternative blocks for a given slot number.
    alternatives: Vec<Hash>,
    /// Indicates for which slots we already received at least one shred.
    first_shred_seen: bool,
    /// Stores double-Merkle tree for each canonical block.
    double_merkle_tree: Option<MerkleTree>,
    /// Stores last slice index for each slot.
    last_slice: Option<usize>,
    /// Set of slots for which conflicting shreds have been seen (leader equivocated).
    equivocated: bool,
    /// Cache of previously verified Merkle roots.
    merkle_root_cache: BTreeMap<usize, Hash>,
}

impl Blockstore {
    /// Initializes a new empty blockstore.
    ///
    /// For each later reconstructed block this blockstore will send a
    /// [`VotorEvent::Block`] to the provided `votor_channel`.
    pub fn new(epoch_info: Arc<EpochInfo>, votor_channel: Sender<VotorEvent>) -> Self {
        Self {
            block_data: BTreeMap::new(),
            votor_channel,
            epoch_info,
        }
    }

    /// Stores a new shred in the blockstore.
    ///
    /// Shreds received by Rotor should set `check_equivocation` to `true`.
    /// If `check_equivocation` is `true` and the leader was observed to equivocate,
    /// i.e., produced conflicting blocks/slices, the shred is dropped.
    ///
    /// Reconstructs the corresponding slice and block if possible and necessary.
    /// If the added shred belongs to the last slice, all later shreds are deleted.
    ///
    /// Returns `Some(slot, block_info)` if a block was reconstructed, `None` otherwise.
    /// In the `Some`-case, `block_info` is the [`BlockInfo`] of the reconstructed block.
    #[fastrace::trace(short_name = true)]
    pub async fn add_shred(
        &mut self,
        shred: Shred,
        check_equivocation: bool,
    ) -> Option<(Slot, BlockInfo)> {
        let slot = shred.payload().slot;
        let leader_pk = self.epoch_info.leader(slot).pubkey;
        let (block_info, event) = self
            .slot_data_mut(slot)
            .add_shred(shred.clone(), check_equivocation, leader_pk)
            .await;

        // potentially notify Votor of first slice
        if let Some(event) = event {
            self.votor_channel.send(event).await.unwrap();
        }

        // return early if no block was reconstructed
        let block_info = block_info?;

        // notify Votor of block and print block info
        let event = VotorEvent::Block { slot, block_info };
        self.votor_channel.send(event).await.unwrap();
        debug!(
            "reconstructed block {} in slot {} with parent {} in slot {}",
            &hex::encode(block_info.hash)[..8],
            slot,
            &hex::encode(block_info.parent_hash)[..8],
            block_info.parent_slot,
        );

        Some((slot, block_info))
    }

    /// Gives the canonical block hash for a given `slot`, if any.
    ///
    /// This is usually the first version of the block stored in the blockstore.
    /// Returns `None` if blockstore does not hold any version of the block yet.
    #[must_use]
    pub fn canonical_block_hash(&self, slot: Slot) -> Option<Hash> {
        self.slot_data(slot)?.canonical
    }

    /// Gives the number of stored slices for a given `slot`.
    pub fn stored_slices_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot).map_or(0, |s| s.slices.len())
    }

    /// Gives the number of stored shreds for a given `slot` (across all slices).
    pub fn stored_shreds_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot)
            .map_or(0, |s| s.shreds.values().map(Vec::len).sum::<usize>())
    }

    /// Gives the number of stored shreds for a given slot and slice.
    pub fn stored_shreds_for_slice(&self, slot: Slot, slice: usize) -> usize {
        self.slot_data(slot)
            .map_or(0, |s| s.shreds.get(&slice).map_or(0, Vec::len))
    }

    /// Gives any relevant alternative block hashes for a given slot, if any.
    #[must_use]
    pub fn alternative_block_hashes(&self, slot: Slot) -> &[Hash] {
        self.slot_data(slot)
            .map_or(&[], |s| s.alternatives.as_ref())
    }

    /// Gives reference to stored block for the given `slot` and `hash`.
    ///
    /// Returns `None` if blockstore does not hold that block yet.
    pub fn get_block(&self, slot: Slot, hash: Hash) -> Option<&Block> {
        self.slot_data(slot)?.blocks.get(&hash)
    }

    /// Gives reference to stored slice for the given `slot` and `slice` index.
    ///
    /// Returns `None` if blockstore does not hold that slice yet.
    pub fn get_slice(&self, slot: Slot, slice: usize) -> Option<&Slice> {
        self.slot_data(slot)?.slices.get(&slice)
    }

    /// Gives reference to stored shred for the given `slot`, `slice` and `shred` index.
    ///
    /// Returns `None` if blockstore does not hold that shred yet.
    pub fn get_shred(&self, slot: Slot, slice: usize, shred: usize) -> Option<&Shred> {
        self.slot_data(slot)?
            .shreds
            .get(&slice)
            .and_then(|v| v.iter().find(|s| s.payload().index_in_slice == shred))
    }

    /// Generates a Merkle proof for the given `slice` within the given `slot`.
    ///
    /// # Panics
    ///
    /// Panics if the double-Merkle tree for the given `slot` does not exist.
    #[must_use]
    pub fn create_double_merkle_proof(&self, slot: Slot, slice: usize) -> Vec<Hash> {
        let slot_data = self.slot_data(slot).unwrap();
        let tree = slot_data.double_merkle_tree.as_ref().unwrap();
        tree.create_proof(slice)
    }

    /// Deletes everything before the given `slot` from the blockstore.
    pub fn prune(&mut self, slot: Slot) {
        self.block_data = self.block_data.split_off(&slot);
    }

    ///
    fn slot_data(&self, slot: Slot) -> Option<&SlotBlockData> {
        self.block_data.get(&slot)
    }

    ///
    fn slot_data_mut(&mut self, slot: Slot) -> &mut SlotBlockData {
        self.block_data
            .entry(slot)
            .or_insert_with(|| SlotBlockData::new(slot))
    }
}

impl SlotBlockData {
    fn new(slot: Slot) -> Self {
        Self {
            slot,
            shreds: BTreeMap::new(),
            slices: BTreeMap::new(),
            blocks: BTreeMap::new(),
            canonical: None,
            alternatives: Vec::new(),
            first_shred_seen: false,
            double_merkle_tree: None,
            last_slice: None,
            equivocated: false,
            merkle_root_cache: BTreeMap::new(),
        }
    }

    async fn add_shred(
        &mut self,
        shred: Shred,
        check_equivocation: bool,
        leader_pk: PublicKey,
    ) -> (Option<BlockInfo>, Option<VotorEvent>) {
        assert_eq!(shred.payload().slot, self.slot);
        if check_equivocation && self.equivocated {
            debug!("recevied shred from equivocating leader, not adding to blockstore");
            return (None, None);
        }
        let slice = shred.payload().slice_index;
        let index = shred.payload().index_in_slice;
        let is_last_slice = shred.payload().is_last_slice;
        let slice_shreds = self.shreds.entry(slice).or_default();

        // check Merkle root and signature
        let cached_merkle_root = self.merkle_root_cache.get(&slice);
        if !shred.verify(&leader_pk, cached_merkle_root) {
            debug!("dropping invalid shred");
            return (None, None);
        } else if cached_merkle_root.is_none() {
            self.merkle_root_cache.insert(slice, shred.merkle_root);
        } else if cached_merkle_root != Some(&shred.merkle_root) {
            if !self.equivocated {
                self.equivocated = true;
                warn!("shreds show leader equivocation in slot {}", self.slot);
            }
            if check_equivocation {
                return (None, None);
            }
        }

        // store and handle this shred if and only if:
        //   - it is not yet stored in the blockstore
        //   - it is not (known to be) after the last slice
        let exists = slice_shreds.iter().any(|s| {
            s.payload().index_in_slice == index
                && shred.payload_type.is_data() == s.payload_type.is_data()
        });
        let after_last = self.last_slice.is_some_and(|last_slice| slice > last_slice);
        if exists || after_last {
            return (None, None);
        }
        slice_shreds.push(shred);

        // store last slice index, delete later shreds
        if is_last_slice && self.last_slice.is_none() {
            self.last_slice = Some(slice);

            // delete shreds after last slice, if there are any
            let keys_to_delete: Vec<_> = self
                .shreds
                .range(&slice + 1..)
                .map(|(k, _)| k)
                .copied()
                .collect();
            for key in keys_to_delete {
                self.shreds.remove(&key);
            }
        }

        // maybe send first shred notification
        let event = match self.first_shred_seen {
            true => None,
            false => {
                self.first_shred_seen = true;
                Some(VotorEvent::FirstShred(self.slot))
            }
        };

        // maybe reconstruct slice and block
        if self.try_reconstruct_slice(slice) {
            (self.try_reconstruct_block().await, event)
        } else {
            (None, event)
        }
    }

    /// Reconstructs the slice if the blockstore contains enough shreds.
    ///
    /// Returns `true` if a slice was reconstructed, `false` otherwise.
    fn try_reconstruct_slice(&mut self, slice: usize) -> bool {
        let slice_shreds = self.shreds.get(&slice).unwrap();
        if slice_shreds.len() < shredder::DATA_SHREDS || self.slices.contains_key(&slice) {
            return false;
        }

        let reconstructed_slice = RegularShredder::deshred(slice_shreds).unwrap();
        self.slices.insert(slice, reconstructed_slice);
        trace!("reconstructed slice {} in slot {}", slice, self.slot);
        true
    }

    /// Reconstructs the block if the blockstore contains all slices.
    ///
    /// Returns `Some(slot, block_info)` if a block was reconstructed, `None` otherwise.
    /// In the `Some`-case, `block_info` is the [`BlockInfo`] of the reconstructed block.
    async fn try_reconstruct_block(&mut self) -> Option<BlockInfo> {
        if self.canonical.is_some() {
            trace!("already have block for slot {}", self.slot);
            return None;
        }
        let last_slice = self.last_slice?;
        if self.slices.len() != last_slice + 1 {
            trace!("don't have all slices for slot {} yet", self.slot);
            return None;
        }

        // calculate double-Merkle tree & block hash
        let merkle_roots = self
            .slices
            .values()
            .map(|s| s.merkle_root.as_ref().unwrap())
            .collect::<Vec<_>>();
        let tree = MerkleTree::new(&merkle_roots);
        let block_hash = tree.get_root();
        self.double_merkle_tree = Some(tree);

        // reconstruct block header
        let first_slice = self.slices.get(&0).unwrap();
        let parent_slot = u64::from_be_bytes(first_slice.data[0..8].try_into().unwrap());
        let parent_hash = first_slice.data[8..40].try_into().unwrap();
        self.canonical = Some(block_hash);
        // TODO: reconstruct actual block content
        let block = Block {
            slot: self.slot,
            block_hash,
            parent: parent_slot,
            parent_hash,
            transactions: vec![],
        };
        let block_info = BlockInfo::from(&block);
        self.blocks.insert(block_hash, block);

        // clean up raw slices
        for slice_index in 0..=last_slice {
            self.slices.remove(&slice_index);
        }

        Some(block_info)
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
        assert!(blockstore.slot_data(0).is_none());

        // generate two slices for slot 0
        let slices = create_random_block(0, 2);

        // first slice is not enough
        let shreds = RegularShredder::shred(&slices[0], &sk)?;
        for shred in shreds {
            blockstore.add_shred(shred, true).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_none());

        // after second slice we should have the block
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds {
            blockstore.add_shred(shred, true).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_some());

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
            blockstore.add_shred(shred, true).await;
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
            blockstore.add_shred(shred, true).await;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 1);

        // insert just enough shreds to reconstruct slice 1 (from end)
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds.into_iter().skip(TOTAL_SHREDS - DATA_SHREDS) {
            blockstore.add_shred(shred, true).await;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 2);

        // insert just enough shreds to reconstruct slice 2 (from middle)
        let shreds = RegularShredder::shred(&slices[2], &sk)?;
        for shred in shreds.into_iter().skip(DATA_SHREDS / 2) {
            blockstore.add_shred(shred, true).await;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 3);

        // insert just enough shreds to reconstruct slice 3 (split)
        let shreds = RegularShredder::shred(&slices[3], &sk)?;
        for (_, shred) in shreds
            .into_iter()
            .enumerate()
            .filter(|(i, _)| *i < DATA_SHREDS / 2 || *i >= TOTAL_SHREDS - DATA_SHREDS / 2)
        {
            blockstore.add_shred(shred, true).await;
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
            blockstore.add_shred(shred, true).await;
        }
        assert!(blockstore.canonical_block_hash(0).is_none());

        // stored all shreds for slot 0
        assert_eq!(blockstore.stored_shreds_for_slot(0), TOTAL_SHREDS);

        // after also also inserting first slice we should have the block
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds {
            blockstore.add_shred(shred, true).await;
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
            blockstore.add_shred(shred, true).await;
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
            blockstore.add_shred(shred, true).await;
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
            blockstore.add_shred(shred, true).await;
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
        let shred_count = blockstore
            .block_data
            .values()
            .map(|d| d.shreds.values().map(|s| s.len()).sum::<usize>())
            .sum::<usize>();
        assert_eq!(shred_count, 0);

        drop(rx);
        Ok(())
    }
}
