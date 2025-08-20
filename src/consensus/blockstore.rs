// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding blocks for each slot.

mod slot_block_data;

use std::collections::BTreeMap;
use std::sync::Arc;

use async_trait::async_trait;
use log::debug;
use mockall::automock;
use tokio::sync::mpsc::Sender;

use crate::crypto::Hash;
use crate::shredder::Shred;
use crate::types::SliceIndex;
use crate::{Block, Slot};

use super::epoch_info::EpochInfo;
use super::votor::VotorEvent;

use slot_block_data::{AddShredError, SlotBlockData};

/// Information about a block within a slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

#[async_trait]
#[automock]
pub trait Blockstore {
    async fn add_shred_from_disseminator(
        &mut self,
        shred: Shred,
    ) -> Result<Option<(Slot, BlockInfo)>, AddShredError>;
    async fn add_shred_from_repair(
        &mut self,
        hash: Hash,
        shred: Shred,
    ) -> Result<Option<(Slot, BlockInfo)>, AddShredError>;
    fn canonical_block_hash(&self, slot: Slot) -> Option<Hash>;
    fn stored_shreds_for_slot(&self, slot: Slot) -> usize;
    #[allow(clippy::needless_lifetimes)]
    fn get_block<'a>(&'a self, slot: Slot, hash: Hash) -> Option<&'a Block>;
    #[allow(clippy::needless_lifetimes)]
    fn get_shred<'a>(&'a self, slot: Slot, slice: SliceIndex, shred: usize) -> Option<&'a Shred>;
    fn create_double_merkle_proof(&self, slot: Slot, slice: SliceIndex) -> Vec<Hash>;
}

/// Blockstore is the fundamental data structure holding block data per slot.
pub struct BlockstoreImpl {
    /// Data structure holding the actual block data per slot.
    block_data: BTreeMap<Slot, SlotBlockData>,

    /// Event channel for sending notifications to Votor.
    votor_channel: Sender<VotorEvent>,
    /// Information about all active validators.
    epoch_info: Arc<EpochInfo>,
}

impl BlockstoreImpl {
    /// Initializes a new empty blockstore.
    ///
    /// Blockstore will send the following `VotorEvent`s to the provided `votor_channel`:
    /// - [`VotorEvent::FirstShred`] when receiving the first shred for a slot
    ///   from the block dissemination protocol
    /// - [`VotorEvent::Block`] for any reconstructed block
    pub fn new(epoch_info: Arc<EpochInfo>, votor_channel: Sender<VotorEvent>) -> Self {
        Self {
            block_data: BTreeMap::new(),
            votor_channel,
            epoch_info,
        }
    }

    /// Gives the number of stored slices for a given `slot`.
    pub fn stored_slices_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot).map_or(0, |s| s.canonical.slices.len())
    }

    /// Deletes everything before the given `slot` from the blockstore.
    pub fn prune(&mut self, slot: Slot) {
        self.block_data = self.block_data.split_off(&slot);
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

#[async_trait]
impl Blockstore for BlockstoreImpl {
    /// Stores a new shred in the blockstore.
    ///
    /// This shred is stored in the default spot without a known block hash.
    /// For shreds obtained through repair, `add_shred_from_repair`
    /// should be used instead.
    /// Compared to that function, this one checks for leader equivocation.
    ///
    /// Reconstructs the corresponding slice and block if possible and necessary.
    /// If the added shred belongs to the last slice, all later shreds are deleted.
    ///
    /// Returns `Some(slot, block_info)` if a block was reconstructed, `None` otherwise.
    /// In the `Some`-case, `block_info` is the [`BlockInfo`] of the reconstructed block.
    #[fastrace::trace(short_name = true)]
    async fn add_shred_from_disseminator(
        &mut self,
        shred: Shred,
    ) -> Result<Option<(Slot, BlockInfo)>, AddShredError> {
        let slot = shred.payload().header.slot;
        let leader_pk = self.epoch_info.leader(slot).pubkey;
        match self
            .slot_data_mut(slot)
            .add_shred_from_disseminator(shred, leader_pk)?
        {
            Some(event) => Ok(self.send_votor_event(event).await),
            None => Ok(None),
        }
    }

    /// Stores a new shred from repair in the blockstore.
    ///
    /// This shred is stored in a spot associated with the given block`hash`.
    /// For shreds obtained through block dissemination, `add_shred_from_disseminator`
    /// should be used instead.
    /// Compared to that function, this one does not check for leader equivocation.
    ///
    /// Reconstructs the corresponding slice and block if possible and necessary.
    /// If the added shred belongs to the last slice, all later shreds are deleted.
    ///
    /// Returns `Some(slot, block_info)` if a block was reconstructed, `None` otherwise.
    /// In the `Some`-case, `block_info` is the [`BlockInfo`] of the reconstructed block.
    #[fastrace::trace(short_name = true)]
    async fn add_shred_from_repair(
        &mut self,
        hash: Hash,
        shred: Shred,
    ) -> Result<Option<(Slot, BlockInfo)>, AddShredError> {
        let slot = shred.payload().header.slot;
        let leader_pk = self.epoch_info.leader(slot).pubkey;
        match self
            .slot_data_mut(slot)
            .add_shred_from_repair(hash, shred, leader_pk)?
        {
            Some(event) => Ok(self.send_votor_event(event).await),
            None => Ok(None),
        }
    }

    /// Gives the canonical block hash for a given `slot`, if any.
    ///
    /// This is usually the first version of the block stored in the blockstore.
    /// Returns `None` if blockstore does not hold any version of the block yet.
    fn canonical_block_hash(&self, slot: Slot) -> Option<Hash> {
        self.slot_data(slot)?
            .canonical
            .completed
            .as_ref()
            .map(|c| c.0)
    }

    /// Gives the number of stored shreds for a given `slot` (across all slices).
    fn stored_shreds_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot)
            .map_or(0, |s| s.canonical.shreds.values().map(Vec::len).sum())
    }

    /// Gives reference to stored block for the given `slot` and `hash`.
    ///
    /// Returns `None` if blockstore does not hold that block yet.
    fn get_block(&self, slot: Slot, hash: Hash) -> Option<&Block> {
        let slot_data = self.slot_data(slot)?;
        if let Some((h, block)) = slot_data.canonical.completed.as_ref()
            && *h == hash
        {
            return Some(block);
        }
        slot_data
            .alternatives
            .get(&hash)
            .and_then(|data| data.completed.as_ref().map(|(_, block)| Some(block)))
            .flatten()
    }

    /// Gives reference to stored shred for the given `slot`, `slice` and `shred` index.
    ///
    /// Returns `None` if blockstore does not hold that shred yet.
    // TODO: support alternative/repaired blocks here
    fn get_shred(&self, slot: Slot, slice: SliceIndex, shred: usize) -> Option<&Shred> {
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
    fn create_double_merkle_proof(&self, slot: Slot, slice: SliceIndex) -> Vec<Hash> {
        let slot_data = self.slot_data(slot).unwrap();
        let tree = slot_data.canonical.double_merkle_tree.as_ref().unwrap();
        tree.create_proof(slice.inner())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ValidatorInfo;
    use crate::crypto::signature::SecretKey;
    use crate::crypto::{MerkleTree, aggsig};
    use crate::shredder::{DATA_SHREDS, RegularShredder, Shredder, TOTAL_SHREDS};
    use crate::test_utils::create_random_block;
    use crate::types::SliceIndex;

    use color_eyre::Result;
    use tokio::sync::mpsc;

    fn test_setup(tx: Sender<VotorEvent>) -> (SecretKey, BlockstoreImpl) {
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
        (sk, BlockstoreImpl::new(Arc::new(epoch_info), tx))
    }

    #[tokio::test]
    async fn store_one_slice_block() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.slot_data(slot).is_none());

        // generate single-slice block
        let slice = create_random_block(slot, 1)[0].clone();

        let shreds = RegularShredder::shred(slice, &sk)?;
        let slice_hash = shreds[0].merkle_root;
        for shred in shreds {
            // store shred
            blockstore
                .add_shred_from_disseminator(shred.clone())
                .await?;

            // check shred is stored
            let Some(stored_shred) =
                blockstore.get_shred(slot, SliceIndex::first(), shred.payload().index_in_slice)
            else {
                panic!("shred not stored");
            };
            assert_eq!(stored_shred.payload().data, shred.payload().data);
        }

        // create and check double-Merkle proof
        let proof = blockstore.create_double_merkle_proof(slot, SliceIndex::first());
        let slot_data = blockstore.slot_data(slot).unwrap();
        let tree = slot_data.canonical.double_merkle_tree.as_ref().unwrap();
        let root = tree.get_root();
        assert!(MerkleTree::check_proof(&slice_hash, 0, root, &proof));

        Ok(())
    }

    #[tokio::test]
    async fn store_two_slice_block() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.slot_data(slot).is_none());

        // generate two-slice block
        let slices = create_random_block(slot, 2);

        // first slice is not enough
        let shreds = RegularShredder::shred(slices[0].clone(), &sk)?;
        for shred in shreds {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(slot).is_none());

        // after second slice we should have the block
        let shreds = RegularShredder::shred(slices[1].clone(), &sk)?;
        for shred in shreds {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(slot).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn store_block_from_repair() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.slot_data(slot).is_none());

        // generate and shred two slices
        let slices = create_random_block(slot, 2);
        let slice0_shreds = RegularShredder::shred(slices[0].clone(), &sk)?;
        let slice1_shreds = RegularShredder::shred(slices[1].clone(), &sk)?;

        // calculate block hash
        let merkle_roots = vec![slice0_shreds[0].merkle_root, slice1_shreds[0].merkle_root];
        let tree = MerkleTree::new(&merkle_roots);
        let block_hash = tree.get_root();

        // first slice is not enough
        for shred in slice0_shreds {
            blockstore.add_shred_from_repair(block_hash, shred).await?;
        }
        assert!(blockstore.canonical_block_hash(slot).is_none());

        // after second slice we should have the block
        for shred in slice1_shreds {
            blockstore.add_shred_from_repair(block_hash, shred).await?;
        }
        assert!(blockstore.canonical_block_hash(slot).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.canonical_block_hash(slot).is_none());

        // generate a single slice for slot 0
        let slices = create_random_block(slot, 1);

        // insert shreds in reverse order
        let shreds = RegularShredder::shred(slices[0].clone(), &sk)?;
        for shred in shreds.into_iter().rev() {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(slot).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn just_enough_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.canonical_block_hash(slot).is_none());

        // generate a larger block for slot 0
        let slices = create_random_block(slot, 4);
        assert_eq!(blockstore.stored_slices_for_slot(slot), 0);

        // insert just enough shreds to reconstruct slice 0 (from beginning)
        let shreds = RegularShredder::shred(slices[0].clone(), &sk)?;
        for shred in shreds.into_iter().take(DATA_SHREDS) {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(slot), 1);

        // insert just enough shreds to reconstruct slice 1 (from end)
        let shreds = RegularShredder::shred(slices[1].clone(), &sk)?;
        for shred in shreds.into_iter().skip(TOTAL_SHREDS - DATA_SHREDS) {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(slot), 2);

        // insert just enough shreds to reconstruct slice 2 (from middle)
        let shreds = RegularShredder::shred(slices[2].clone(), &sk)?;
        for shred in shreds.into_iter().skip(DATA_SHREDS / 2) {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(slot), 3);

        // insert just enough shreds to reconstruct slice 3 (split)
        let shreds = RegularShredder::shred(slices[3].clone(), &sk)?;
        for (_, shred) in shreds
            .into_iter()
            .enumerate()
            .filter(|(i, _)| *i < DATA_SHREDS / 2 || *i >= TOTAL_SHREDS - DATA_SHREDS / 2)
        {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(slot).is_some());

        // slices are deleted after reconstruction
        assert_eq!(blockstore.stored_slices_for_slot(slot), 0);

        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_slices() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.canonical_block_hash(slot).is_none());

        // generate two slices for slot 0
        let slices = create_random_block(slot, 2);

        // second slice alone is not enough
        let shreds = RegularShredder::shred(slices[0].clone(), &sk)?;
        for shred in shreds {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(slot).is_none());

        // stored all shreds for slot 0
        assert_eq!(blockstore.stored_shreds_for_slot(slot), TOTAL_SHREDS);

        // after also also inserting first slice we should have the block
        let shreds = RegularShredder::shred(slices[1].clone(), &sk)?;
        for shred in shreds {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(slot).is_some());

        // stored all shreds
        assert_eq!(blockstore.stored_shreds_for_slot(slot), 2 * TOTAL_SHREDS);

        Ok(())
    }

    #[tokio::test]
    async fn duplicate_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        let slices = create_random_block(slot, 1);

        // insert many duplicate shreds
        let shreds = RegularShredder::shred(slices[0].clone(), &sk)?;
        for shred in vec![shreds[0].clone(); 2] {
            // ignore errors
            let _ = blockstore.add_shred_from_disseminator(shred).await;
        }

        // should only store one copy
        assert_eq!(blockstore.stored_shreds_for_slot(slot), 1);

        Ok(())
    }

    #[tokio::test]
    async fn invalid_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        let slices = create_random_block(slot, 1);

        // insert shreds with wrong Merkle root
        let shreds = RegularShredder::shred(slices[0].clone(), &sk)?;
        for mut shred in shreds {
            shred.merkle_root = Hash::default();
            let res = blockstore.add_shred_from_disseminator(shred).await;
            assert!(res.is_err());
            assert_eq!(res.err(), Some(AddShredError::InvalidSignature));
        }

        Ok(())
    }

    #[tokio::test]
    async fn pruning() -> Result<()> {
        let block0_slot = Slot::genesis().next();
        let block1_slot = block0_slot.next();
        let block2_slot = block1_slot.next();
        let block3_slot = block2_slot.next();
        let future_slot = block3_slot.next();
        let (tx, _rx) = mpsc::channel(1000);
        let (sk, mut blockstore) = test_setup(tx);
        let block0 = create_random_block(block0_slot, 1);
        let block1 = create_random_block(block1_slot, 1);
        let block2 = create_random_block(block2_slot, 1);

        // insert shreds
        let mut shreds = RegularShredder::shred(block0[0].clone(), &sk)?;
        shreds.extend(RegularShredder::shred(block1[0].clone(), &sk)?);
        shreds.extend(RegularShredder::shred(block2[0].clone(), &sk)?);
        for shred in shreds {
            blockstore.add_shred_from_disseminator(shred).await?;
        }
        assert!(blockstore.canonical_block_hash(block0_slot).is_some());
        assert!(blockstore.canonical_block_hash(block1_slot).is_some());
        assert!(blockstore.canonical_block_hash(block2_slot).is_some());

        // stored all shreds
        assert_eq!(blockstore.stored_shreds_for_slot(block0_slot), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(block1_slot), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(block2_slot), TOTAL_SHREDS);

        // some (and only some) shreds deleted after partial pruning
        blockstore.prune(block1_slot);
        assert_eq!(blockstore.stored_shreds_for_slot(block0_slot), 0);
        assert_eq!(blockstore.stored_shreds_for_slot(block1_slot), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(block2_slot), TOTAL_SHREDS);

        // no shreds left after full pruning
        blockstore.prune(future_slot);
        assert_eq!(blockstore.stored_shreds_for_slot(block0_slot), 0);
        assert_eq!(blockstore.stored_shreds_for_slot(block1_slot), 0);
        assert_eq!(blockstore.stored_shreds_for_slot(block2_slot), 0);
        let shred_count = blockstore
            .block_data
            .values()
            .map(|d| d.canonical.shreds.values().map(|s| s.len()).sum::<usize>())
            .sum::<usize>();
        assert_eq!(shred_count, 0);

        Ok(())
    }
}
