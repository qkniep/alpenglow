// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding blocks for each slot.

mod slot_block_data;

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use log::debug;
use mockall::automock;
use tokio::sync::mpsc::Sender;

use self::slot_block_data::{AddShredError, SlotBlockData};
use super::epoch_info::EpochInfo;
use super::votor::VotorEvent;
use crate::consensus::blockstore::slot_block_data::BlockData;
use crate::crypto::merkle::{BlockHash, DoubleMerkleProof, MerkleRoot, SliceRoot};
use crate::shredder::{RegularShredder, Shred, ShredIndex, ValidatedShred};
use crate::types::SliceIndex;
use crate::{Block, BlockId, Slot};

/// Information about a block within a slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockInfo {
    pub(crate) hash: BlockHash,
    pub(crate) parent: BlockId,
}

impl From<&Block> for BlockInfo {
    fn from(block: &Block) -> Self {
        BlockInfo {
            hash: block.hash.clone(),
            parent: (block.parent, block.parent_hash.clone()),
        }
    }
}

/// Interface for the blockstore.
///
/// This is only used for mocking of [`BlockstoreImpl`].
#[async_trait]
#[automock]
pub trait Blockstore {
    async fn add_shred_from_disseminator(
        &mut self,
        shred: Shred,
    ) -> Result<Option<BlockInfo>, AddShredError>;
    async fn add_shred_from_repair(
        &mut self,
        hash: BlockHash,
        shred: Shred,
    ) -> Result<Option<BlockInfo>, AddShredError>;
    #[allow(clippy::needless_lifetimes)]
    fn disseminated_block_hash<'a>(&'a self, slot: Slot) -> Option<&'a BlockHash>;
    #[allow(clippy::needless_lifetimes)]
    fn get_block<'a>(&'a self, block_id: &BlockId) -> Option<&'a Block>;
    fn get_last_slice_index(&self, block_id: &BlockId) -> Option<SliceIndex>;
    fn get_slice_root<'a>(&'a self, block_id: &BlockId, slice: SliceIndex)
    -> Option<&'a SliceRoot>;
    #[allow(clippy::needless_lifetimes)]
    fn get_shred<'a>(
        &'a self,
        block_id: &BlockId,
        slice_index: SliceIndex,
        shred_index: ShredIndex,
    ) -> Option<&'a ValidatedShred>;
    fn create_double_merkle_proof(
        &self,
        block_id: &BlockId,
        slice_index: SliceIndex,
    ) -> Option<DoubleMerkleProof>;
}

/// Blockstore is the fundamental data structure holding block data per slot.
pub struct BlockstoreImpl {
    /// Data structure holding the actual block data per slot.
    block_data: BTreeMap<Slot, SlotBlockData>,
    /// Shredder to use for reconstructing slices.
    shredder: Arc<Mutex<RegularShredder>>,

    /// Event channel for sending notifications to Votor.
    votor_channel: Sender<VotorEvent>,
    /// Information about all active validators.
    epoch_info: Arc<EpochInfo>,
}

impl BlockstoreImpl {
    /// Initializes a new empty blockstore.
    ///
    /// Blockstore will send the following [`VotorEvent`]s to the provided `votor_channel`:
    /// - [`VotorEvent::FirstShred`] when receiving the first shred for a slot
    ///   from the block dissemination protocol
    /// - [`VotorEvent::Block`] for any reconstructed block
    pub fn new(epoch_info: Arc<EpochInfo>, votor_channel: Sender<VotorEvent>) -> Self {
        Self {
            block_data: BTreeMap::new(),
            shredder: Arc::new(Mutex::new(RegularShredder::default())),
            votor_channel,
            epoch_info,
        }
    }

    /// Deletes everything before the given `slot` from the blockstore.
    pub fn prune(&mut self, slot: Slot) {
        self.block_data = self.block_data.split_off(&slot);
    }

    async fn send_votor_event(&self, event: VotorEvent) -> Option<BlockInfo> {
        match &event {
            VotorEvent::FirstShred(_) => {
                self.votor_channel.send(event).await.unwrap();
                None
            }
            VotorEvent::Block { slot, block_info } => {
                let block_info = block_info.clone();
                debug!(
                    "reconstructed block {} in slot {} with parent {} in slot {}",
                    &hex::encode(block_info.hash.as_hash())[..8],
                    slot,
                    &hex::encode(block_info.parent.1.as_hash())[..8],
                    block_info.parent.0,
                );
                self.votor_channel.send(event).await.unwrap();

                Some(block_info)
            }
            ev => panic!("unexpected event {ev:?}"),
        }
    }

    /// Gives reference to stored block data for the given `block_id`.
    ///
    /// Considers both, the disseminated block and any repaired blocks.
    ///
    /// Returns [`None`] if blockstore does not know about this block yet.
    fn get_block_data(&self, block_id: &BlockId) -> Option<&BlockData> {
        let (slot, hash) = block_id;
        let slot_data = self.slot_data(*slot)?;
        if let Some((h, _)) = &slot_data.disseminated.completed
            && h == hash
        {
            return Some(&slot_data.disseminated);
        }
        slot_data.repaired.get(hash)
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

    /// Gives the shred for the given `slot`, `slice` and `shred` index.
    ///
    /// Considers only the disseminated block.
    ///
    /// Only used for testing.
    #[cfg(test)]
    fn get_disseminated_shred(
        &self,
        slot: Slot,
        slice: SliceIndex,
        shred_index: ShredIndex,
    ) -> Option<&ValidatedShred> {
        self.slot_data(slot).and_then(|s| {
            s.disseminated
                .shreds
                .get(&slice)
                .and_then(|shreds| shreds[*shred_index].as_ref())
        })
    }

    /// Gives the number of stored shreds for a given `slot` (across all slices).
    ///
    /// Only used for testing.
    #[cfg(test)]
    fn stored_shreds_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot).map_or(0, |s| {
            let mut cnt = 0;
            for shreds in s.disseminated.shreds.values() {
                cnt += shreds.iter().filter(|s| s.is_some()).count();
            }
            cnt
        })
    }

    /// Gives the number of stored slices for a given `slot`.
    ///
    /// Only used for testing.
    #[cfg(test)]
    pub(crate) fn stored_slices_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot)
            .map_or(0, |s| s.disseminated.slices.len())
    }
}

#[async_trait]
impl Blockstore for BlockstoreImpl {
    /// Stores a new shred in the blockstore.
    ///
    /// This shred is stored in the default spot without a known block hash.
    /// For shreds obtained through repair, `add_shred_from_repair` should be used instead.
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
    ) -> Result<Option<BlockInfo>, AddShredError> {
        let slot = shred.payload().header.slot;
        let leader_pk = self.epoch_info.leader(slot).pubkey;
        let shredder = self.shredder.clone();
        match self
            .slot_data_mut(slot)
            .add_shred_from_disseminator(shred, leader_pk, shredder)?
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
    /// If the added shred belongs to last slice, deletes later slices and their shreds.
    ///
    /// Returns `Some(slot, block_info)` if a block was reconstructed, `None` otherwise.
    /// In the `Some`-case, `block_info` is the [`BlockInfo`] of the reconstructed block.
    #[fastrace::trace(short_name = true)]
    async fn add_shred_from_repair(
        &mut self,
        hash: BlockHash,
        shred: Shred,
    ) -> Result<Option<BlockInfo>, AddShredError> {
        let slot = shred.payload().header.slot;
        let leader_pk = self.epoch_info.leader(slot).pubkey;
        let shredder = self.shredder.clone();
        match self
            .slot_data_mut(slot)
            .add_shred_from_repair(hash, shred, leader_pk, shredder)?
        {
            Some(event) => Ok(self.send_votor_event(event).await),
            None => Ok(None),
        }
    }

    /// Gives the disseminated block hash for a given `slot`, if any.
    ///
    /// This refers to the block we received from block dissemination.
    ///
    /// Returns `None` if we have no block or only blocks from repair.
    fn disseminated_block_hash(&self, slot: Slot) -> Option<&BlockHash> {
        self.slot_data(slot)?
            .disseminated
            .completed
            .as_ref()
            .map(|c| &c.0)
    }

    /// Gives reference to stored block for the given `block_id`.
    ///
    /// Considers both, the disseminated block and any repaired blocks.
    /// However, the dissminated block can only be considered if it's complete.
    ///
    /// Returns `None` if blockstore does not know a block for that hash.
    fn get_block(&self, block_id: &BlockId) -> Option<&Block> {
        let block_data = self.get_block_data(block_id)?;
        if let Some((hash, block)) = block_data.completed.as_ref() {
            debug_assert_eq!(*hash, block_id.1);
            Some(block)
        } else {
            None
        }
    }

    /// Gives the last slice index for the given `block_id`.
    ///
    /// Returns `None` if blockstore does not know the last slice yet.
    fn get_last_slice_index(&self, block_id: &BlockId) -> Option<SliceIndex> {
        let block_data = self.get_block_data(block_id)?;
        block_data.last_slice
    }

    /// Gives the Merkle root for the given `slice_index` of the given `block_id`.
    ///
    /// Returns `None` if blockstore does not hold any shred for that slice.
    fn get_slice_root(&self, block_id: &BlockId, slice_index: SliceIndex) -> Option<&SliceRoot> {
        let block_data = self.get_block_data(block_id)?;
        let slice_shreds = block_data.shreds.get(&slice_index)?;
        slice_shreds.iter().flatten().next().map(|s| &s.merkle_root)
    }

    /// Gives reference to stored shred for given `block_id`, `slice_index` and `shred_index`.
    ///
    /// Returns `None` if blockstore does not hold that shred.
    fn get_shred(
        &self,
        block_id: &BlockId,
        slice_index: SliceIndex,
        shred_index: ShredIndex,
    ) -> Option<&ValidatedShred> {
        let block_data = self.get_block_data(block_id)?;
        let slice_shreds = block_data.shreds.get(&slice_index)?;
        slice_shreds[*shred_index].as_ref()
    }

    /// Generates a Merkle proof for the given `slice_index` of the given `block_id`.
    ///
    /// Returns `None` if blockstore does not hold that block yet.
    fn create_double_merkle_proof(
        &self,
        block_id: &BlockId,
        slice_index: SliceIndex,
    ) -> Option<DoubleMerkleProof> {
        let block_data = self.get_block_data(block_id)?;
        let tree = block_data.double_merkle_tree.as_ref()?;
        Some(tree.create_proof(slice_index.inner()))
    }
}

#[cfg(test)]
mod tests {
    use color_eyre::Result;
    use tokio::sync::mpsc;

    use super::*;
    use crate::ValidatorInfo;
    use crate::crypto::merkle::DoubleMerkleTree;
    use crate::crypto::signature::SecretKey;
    use crate::crypto::{Hash, aggsig};
    use crate::network::dontcare_sockaddr;
    use crate::shredder::{DATA_SHREDS, TOTAL_SHREDS};
    use crate::test_utils::create_random_shredded_block;
    use crate::types::SliceIndex;

    fn test_setup(tx: Sender<VotorEvent>) -> (SecretKey, BlockstoreImpl) {
        let sk = SecretKey::new(&mut rand::rng());
        let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
        let info = ValidatorInfo {
            id: 0,
            stake: 1,
            pubkey: sk.to_pk(),
            voting_pubkey: voting_sk.to_pk(),
            all2all_address: dontcare_sockaddr(),
            disseminator_address: dontcare_sockaddr(),
            repair_request_address: dontcare_sockaddr(),
            repair_response_address: dontcare_sockaddr(),
        };
        let validators = vec![info];
        let epoch_info = EpochInfo::new(0, validators);
        (sk, BlockstoreImpl::new(Arc::new(epoch_info), tx))
    }

    async fn add_shred_ignore_duplicate(
        blockstore: &mut BlockstoreImpl,
        shred: Shred,
    ) -> Result<Option<BlockInfo>, AddShredError> {
        match blockstore.add_shred_from_disseminator(shred).await {
            Ok(output) => Ok(output),
            Err(AddShredError::Duplicate) => Ok(None),
            Err(e) => Err(e),
        }
    }

    #[tokio::test]
    async fn store_one_slice_block() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.slot_data(slot).is_none());

        // generate single-slice block
        let (block_hash, _, shreds) = create_random_shredded_block(slot, 1, &sk);
        let block_id = (slot, block_hash);

        let slice_hash = &shreds[0][0].merkle_root;
        for shred in &shreds[0] {
            // store shred
            add_shred_ignore_duplicate(&mut blockstore, shred.clone().into_shred()).await?;

            // check shred is stored
            let Some(stored_shred) = blockstore.get_disseminated_shred(
                slot,
                SliceIndex::first(),
                shred.payload().shred_index,
            ) else {
                panic!("shred not stored");
            };
            assert_eq!(stored_shred.payload().data, shred.payload().data);
        }

        // create and check double-Merkle proof
        let proof = blockstore
            .create_double_merkle_proof(&block_id, SliceIndex::first())
            .unwrap();
        let slot_data = blockstore.slot_data(slot).unwrap();
        let tree = slot_data.disseminated.double_merkle_tree.as_ref().unwrap();
        let root = tree.get_root();
        assert!(DoubleMerkleTree::check_proof(slice_hash, 0, &root, &proof));

        Ok(())
    }

    #[tokio::test]
    async fn store_two_slice_block() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.slot_data(slot).is_none());

        // generate two-slice block
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 2, &sk);

        // first slice is not enough
        for shred in slices[0].clone() {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_none());

        // after second slice we should have the block
        for shred in slices[1].clone() {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn store_block_from_repair() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.slot_data(slot).is_none());

        // generate and shred two slices
        let (block_hash, _tree, slices) = create_random_shredded_block(slot, 2, &sk);

        // first slice is not enough
        for shred in slices[0].clone().into_iter().take(DATA_SHREDS) {
            blockstore
                .add_shred_from_repair(block_hash.clone(), shred.into_shred())
                .await?;
        }
        assert!(blockstore.get_block(&(slot, block_hash.clone())).is_none());

        // after second slice we should have the block
        for shred in slices[1].clone().into_iter().take(DATA_SHREDS) {
            blockstore
                .add_shred_from_repair(block_hash.clone(), shred.into_shred())
                .await?;
        }
        assert!(blockstore.get_block(&(slot, block_hash)).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.disseminated_block_hash(slot).is_none());

        // generate a single slice for slot 0
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &sk);

        // insert shreds in reverse order
        for shred in slices[0].clone().into_iter().rev() {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn just_enough_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.disseminated_block_hash(slot).is_none());

        // generate a larger block for slot 0
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 4, &sk);
        assert_eq!(blockstore.stored_slices_for_slot(slot), 0);

        // insert just enough shreds to reconstruct slice 0 (from beginning)
        for shred in slices[0].clone().into_iter().take(DATA_SHREDS) {
            blockstore
                .add_shred_from_disseminator(shred.into_shred())
                .await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(slot), 1);

        // insert just enough shreds to reconstruct slice 1 (from end)
        for shred in slices[1]
            .clone()
            .into_iter()
            .skip(TOTAL_SHREDS - DATA_SHREDS)
        {
            blockstore
                .add_shred_from_disseminator(shred.into_shred())
                .await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(slot), 2);

        // insert just enough shreds to reconstruct slice 2 (from middle)
        for shred in slices[2]
            .clone()
            .into_iter()
            .skip((TOTAL_SHREDS - DATA_SHREDS) / 2)
            .take(DATA_SHREDS)
        {
            blockstore
                .add_shred_from_disseminator(shred.into_shred())
                .await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(slot), 3);

        // insert just enough shreds to reconstruct slice 3 (split)
        for (_, shred) in slices[3]
            .clone()
            .into_iter()
            .enumerate()
            .filter(|(i, _)| *i < DATA_SHREDS / 2 || *i >= TOTAL_SHREDS - DATA_SHREDS / 2)
        {
            blockstore
                .add_shred_from_disseminator(shred.into_shred())
                .await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_some());

        // slices are deleted after reconstruction
        assert_eq!(blockstore.stored_slices_for_slot(slot), 0);

        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_slices() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.disseminated_block_hash(slot).is_none());

        // generate two slices for slot 0
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 2, &sk);

        // second slice alone is not enough
        for shred in slices[0].clone() {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_none());

        // stored all shreds for slot 0
        assert_eq!(blockstore.stored_shreds_for_slot(slot), TOTAL_SHREDS);

        // after also also inserting first slice we should have the block
        for shred in slices[1].clone() {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_some());

        // stored all shreds
        assert_eq!(blockstore.stored_shreds_for_slot(slot), 2 * TOTAL_SHREDS);

        Ok(())
    }

    #[tokio::test]
    async fn duplicate_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &sk);

        // inserting single shred should not throw errors
        let res = blockstore
            .add_shred_from_disseminator(slices[0][0].clone().into_shred())
            .await;
        assert!(res.is_ok());

        // inserting same shred again should give duplicate error
        let res = blockstore
            .add_shred_from_disseminator(slices[0][0].clone().into_shred())
            .await;
        assert_eq!(res, Err(AddShredError::Duplicate));

        // should only store one copy
        assert_eq!(blockstore.stored_shreds_for_slot(slot), 1);

        Ok(())
    }

    #[tokio::test]
    async fn invalid_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &sk);

        // insert shreds with wrong Merkle root
        for shred in slices[0].clone() {
            let mut shred = shred.into_shred();
            shred.merkle_root = Hash::default().into();
            let res = add_shred_ignore_duplicate(&mut blockstore, shred).await;
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
        let block0 = create_random_shredded_block(block0_slot, 1, &sk);
        let block1 = create_random_shredded_block(block1_slot, 1, &sk);
        let block2 = create_random_shredded_block(block2_slot, 1, &sk);

        // insert shreds
        let mut shreds = vec![];
        shreds.extend(block0.2.into_iter().flatten());
        shreds.extend(block1.2.into_iter().flatten());
        shreds.extend(block2.2.into_iter().flatten());
        for shred in shreds {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(block0_slot).is_some());
        assert!(blockstore.disseminated_block_hash(block1_slot).is_some());
        assert!(blockstore.disseminated_block_hash(block2_slot).is_some());

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
            .map(|d| {
                d.disseminated
                    .shreds
                    .values()
                    .map(|s| s.len())
                    .sum::<usize>()
            })
            .sum::<usize>();
        assert_eq!(shred_count, 0);

        Ok(())
    }
}
