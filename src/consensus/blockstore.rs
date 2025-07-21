// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding blocks for each slot.
//!
//!

mod slot_block_data;

use std::collections::BTreeMap;
use std::sync::Arc;

use log::debug;
use tokio::sync::mpsc::Sender;

use crate::crypto::Hash;
use crate::shredder::{Shred, Slice};
use crate::{Block, Slot};

use super::epoch_info::EpochInfo;
use super::votor::VotorEvent;

use slot_block_data::{AddShredError, SlotBlockData};

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
    /// Data structure holding the actual block data per slot.
    block_data: BTreeMap<Slot, SlotBlockData>,

    /// Event channel for sending notifications to Votor.
    votor_channel: Sender<VotorEvent>,
    /// Information about all active validators.
    epoch_info: Arc<EpochInfo>,
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
    pub async fn add_shred_from_disseminator(
        &mut self,
        shred: Shred,
    ) -> Result<Option<(Slot, BlockInfo)>, AddShredError> {
        let slot = shred.payload().slot;
        let leader_pk = self.epoch_info.leader(slot).pubkey;
        match self
            .slot_data_mut(slot)
            .add_shred_from_disseminator(shred, leader_pk)?
        {
            Some(event) => Ok(self.send_votor_event(event).await),
            None => Ok(None),
        }
    }

    #[fastrace::trace(short_name = true)]
    pub async fn add_shred_from_repair(
        &mut self,
        hash: Hash,
        shred: Shred,
    ) -> Result<Option<(Slot, BlockInfo)>, AddShredError> {
        let slot = shred.payload().slot;
        let leader_pk = self.epoch_info.leader(slot).pubkey;
        match self
            .slot_data_mut(slot)
            .add_shred_from_repair(hash, shred, leader_pk)?
        {
            Some(event) => Ok(self.send_votor_event(event).await),
            None => Ok(None),
        }
    }

    async fn send_votor_event(&self, event: VotorEvent) -> Option<(Slot, BlockInfo)> {
        match event {
            VotorEvent::FirstShred(_) => {
                self.votor_channel.send(event).await.unwrap();
                None
            }
            VotorEvent::Block { slot, block_info } => {
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
            ev => panic!("unexpected event {ev:?}"),
        }
    }

    /// Gives the canonical block hash for a given `slot`, if any.
    ///
    /// This is usually the first version of the block stored in the blockstore.
    /// Returns `None` if blockstore does not hold any version of the block yet.
    #[must_use]
    pub fn canonical_block_hash(&self, slot: Slot) -> Option<Hash> {
        self.slot_data(slot)?
            .canonical
            .completed
            .as_ref()
            .map(|c| c.0)
    }

    /// Gives the number of stored slices for a given `slot`.
    pub fn stored_slices_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot).map_or(0, |s| s.canonical.slices.len())
    }

    /// Gives the number of stored shreds for a given `slot` (across all slices).
    pub fn stored_shreds_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot)
            .map_or(0, |s| s.canonical.shreds.values().map(Vec::len).sum())
    }

    /// Gives the number of stored shreds for a given slot and slice.
    pub fn stored_shreds_for_slice(&self, slot: Slot, slice: usize) -> usize {
        self.slot_data(slot)
            .map_or(0, |s| s.canonical.shreds.get(&slice).map_or(0, Vec::len))
    }

    /// Gives reference to stored block for the given `slot` and `hash`.
    ///
    /// Returns `None` if blockstore does not hold that block yet.
    pub fn get_block(&self, slot: Slot, hash: Hash) -> Option<&Block> {
        let slot_data = self.slot_data(slot)?;
        if let Some((h, block)) = slot_data.canonical.completed.as_ref() {
            if *h == hash {
                return Some(block);
            }
        }
        slot_data
            .alternatives
            .get(&hash)
            .and_then(|data| data.completed.as_ref().map(|(_, block)| Some(block)))
            .flatten()
    }

    /// Gives reference to stored slice for the given `slot` and `slice` index.
    ///
    /// Returns `None` if blockstore does not hold that slice yet.
    pub fn get_slice(&self, slot: Slot, slice: usize) -> Option<&Slice> {
        self.slot_data(slot)?.canonical.slices.get(&slice)
    }

    /// Gives reference to stored shred for the given `slot`, `slice` and `shred` index.
    ///
    /// Returns `None` if blockstore does not hold that shred yet.
    // TODO: support alternative/repaired blocks here
    pub fn get_shred(&self, slot: Slot, slice: usize, shred: usize) -> Option<&Shred> {
        self.slot_data(slot)?
            .canonical
            .shreds
            .get(&slice)
            .and_then(|v| v.iter().find(|s| s.payload().index_in_slice == shred))
    }

    /// Generates a Merkle proof for the given `slice` within the given `slot`.
    ///
    /// # Panics
    ///
    /// Panics if the double-Merkle tree for the given `slot` does not exist.
    // TODO: support alternative/repaired blocks here
    #[must_use]
    pub fn create_double_merkle_proof(&self, slot: Slot, slice: usize) -> Vec<Hash> {
        let slot_data = self.slot_data(slot).unwrap();
        let tree = slot_data.canonical.double_merkle_tree.as_ref().unwrap();
        tree.create_proof(slice)
    }

    /// Deletes everything before the given `slot` from the blockstore.
    pub fn prune(&mut self, slot: Slot) {
        self.block_data = self.block_data.split_off(&slot);
    }

    /// Reads slot data for the given `slot`.
    fn slot_data(&self, slot: Slot) -> Option<&SlotBlockData> {
        self.block_data.get(&slot)
    }

    /// Writes slot data for the given `slot`, initializing it if necessary.
    fn slot_data_mut(&mut self, slot: Slot) -> &mut SlotBlockData {
        self.block_data
            .entry(slot)
            .or_insert_with(|| SlotBlockData::new(slot))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ValidatorInfo;
    use crate::crypto::aggsig;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{
        DATA_SHREDS, MAX_DATA_PER_SLICE, RegularShredder, Shredder, TOTAL_SHREDS,
    };

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
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(0).is_none());

        // after second slice we should have the block
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds {
            blockstore.add_shred_from_disseminator(shred).await?;
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
            blockstore.add_shred_from_disseminator(shred).await?;
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
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 1);

        // insert just enough shreds to reconstruct slice 1 (from end)
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds.into_iter().skip(TOTAL_SHREDS - DATA_SHREDS) {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 2);

        // insert just enough shreds to reconstruct slice 2 (from middle)
        let shreds = RegularShredder::shred(&slices[2], &sk)?;
        for shred in shreds.into_iter().skip(DATA_SHREDS / 2) {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(0), 3);

        // insert just enough shreds to reconstruct slice 3 (split)
        let shreds = RegularShredder::shred(&slices[3], &sk)?;
        for (_, shred) in shreds
            .into_iter()
            .enumerate()
            .filter(|(i, _)| *i < DATA_SHREDS / 2 || *i >= TOTAL_SHREDS - DATA_SHREDS / 2)
        {
            blockstore.add_shred_from_disseminator(shred).await?;
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
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(0).is_none());

        // stored all shreds for slot 0
        assert_eq!(blockstore.stored_shreds_for_slot(0), TOTAL_SHREDS);

        // after also also inserting first slice we should have the block
        let shreds = RegularShredder::shred(&slices[1], &sk)?;
        for shred in shreds {
            blockstore.add_shred_from_disseminator(shred).await?;
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
            blockstore.add_shred_from_disseminator(shred).await?;
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
            let _ = blockstore.add_shred_from_disseminator(shred).await;
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
            blockstore.add_shred_from_disseminator(shred).await?;
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
            .map(|d| d.canonical.shreds.values().map(|s| s.len()).sum::<usize>())
            .sum::<usize>();
        assert_eq!(shred_count, 0);

        drop(rx);
        Ok(())
    }
}
