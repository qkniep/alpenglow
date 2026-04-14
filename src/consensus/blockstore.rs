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

use self::slot_block_data::{AddShredError, BlockDataEvent, SlotBlockData};
use super::epoch_info::ValidatorEpochInfo;
use super::votor::VotorEvent;
use crate::consensus::blockstore::slot_block_data::BlockData;
use crate::crypto::merkle::{BlockHash, DoubleMerkleProof, MerkleRoot, SliceRoot};
use crate::execution::{ExecutionEvent, InProgressBlock};
use crate::shredder::{RegularShredder, Shred, ShredIndex, ShredderPool, ValidatedShred};
use crate::types::SliceIndex;
use crate::{Block, BlockId, Slot, Transaction};

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
    /// Adds a shred from dissemination; emits execution events per slice.
    /// Returns an error if the shred is invalid or a duplicate.
    async fn add_shred_from_disseminator(&mut self, shred: Shred) -> Result<(), AddShredError>;
    async fn add_own_shred_as_leader(
        &mut self,
        shred: ValidatedShred,
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
    #[allow(clippy::needless_lifetimes)]
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
    /// Shredders used for reconstructing blocks.
    shredders: ShredderPool<RegularShredder>,

    /// Event channel for sending notifications to Votor.
    votor_channel: Sender<VotorEvent>,
    /// Optional channel for streaming execution events to the execution engine.
    exec_channel: Option<Sender<ExecutionEvent>>,
    /// Information about all active validators.
    epoch_info: Arc<ValidatorEpochInfo>,
}

impl BlockstoreImpl {
    /// Initializes a new empty blockstore.
    ///
    /// `votor_channel`: receives [`VotorEvent::FirstShred`] and
    /// (for the leader path) [`VotorEvent::Block`].
    ///
    /// `exec_channel`: if provided, receives [`ExecutionEvent`]s for each
    /// decoded slice on the dissemination path. The execution loop is
    /// responsible for validating and then forwarding [`VotorEvent::Block`]
    /// to the votor.
    pub fn new(
        epoch_info: Arc<ValidatorEpochInfo>,
        votor_channel: Sender<VotorEvent>,
        exec_channel: Option<Sender<ExecutionEvent>>,
    ) -> Self {
        Self {
            block_data: BTreeMap::new(),
            shredders: ShredderPool::with_size(1),
            votor_channel,
            exec_channel,
            epoch_info,
        }
    }

    /// Deletes everything before the given `slot` from the blockstore.
    pub fn prune(&mut self, slot: Slot) {
        self.block_data = self.block_data.split_off(&slot);
    }

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

    fn slot_data(&self, slot: Slot) -> Option<&SlotBlockData> {
        self.block_data.get(&slot)
    }

    fn slot_data_mut(&mut self, slot: Slot) -> &mut SlotBlockData {
        self.block_data
            .entry(slot)
            .or_insert_with(|| SlotBlockData::new(slot))
    }

    /// Processes [`BlockDataEvent`]s from the leader path.
    ///
    /// Emits [`VotorEvent::FirstShred`] and [`VotorEvent::Block`] directly
    /// (bypassing execution), since the leader already validated their own block.
    async fn handle_leader_events(
        &self,
        slot: Slot,
        events: Vec<BlockDataEvent>,
    ) -> Option<BlockInfo> {
        let mut result = None;
        for event in events {
            match event {
                BlockDataEvent::FirstShred => {
                    self.votor_channel
                        .send(VotorEvent::FirstShred(slot))
                        .await
                        .unwrap();
                }
                BlockDataEvent::SliceReconstructed(_) => {
                    // Leader handles execution events in BlockProducer; skip here.
                }
                BlockDataEvent::BlockReady {
                    block_info,
                    state_hash: _,
                } => {
                    debug!(
                        "leader completed block {} in slot {} with parent {} in slot {}",
                        &hex::encode(block_info.hash.as_hash())[..8],
                        slot,
                        &hex::encode(block_info.parent.1.as_hash())[..8],
                        block_info.parent.0,
                    );
                    self.votor_channel
                        .send(VotorEvent::Block {
                            slot,
                            block_info: block_info.clone(),
                        })
                        .await
                        .unwrap();
                    result = Some(block_info);
                }
            }
        }
        result
    }

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

    #[cfg(test)]
    pub(crate) fn stored_slices_for_slot(&self, slot: Slot) -> usize {
        self.slot_data(slot)
            .map_or(0, |s| s.disseminated.slices.len())
    }
}

#[async_trait]
impl Blockstore for BlockstoreImpl {
    /// Stores a shred from block dissemination.
    ///
    /// Emits execution events per reconstructed slice (if an exec channel is
    /// configured). [`VotorEvent::Block`] is NOT emitted here for the
    /// dissemination path; the execution loop emits it after validating the
    /// execution state hash.
    #[fastrace::trace(short_name = true)]
    async fn add_shred_from_disseminator(&mut self, shred: Shred) -> Result<(), AddShredError> {
        let slot = shred.payload().header.slot;
        let leader_pk = self.epoch_info.epoch_info().leader(slot).pubkey;
        let mut shredder = self
            .shredders
            .checkout()
            .expect("should have a shredder because of exclusive access");

        let events = self
            .slot_data_mut(slot)
            .add_shred_from_disseminator(shred, leader_pk, &mut shredder)
            .inspect_err(|err| {
                if *err == AddShredError::InvalidShred {
                    // send InvalidBlock after the match below
                }
            });

        match events {
            Ok(events) => {
                for event in events {
                    match event {
                        BlockDataEvent::FirstShred => {
                            self.votor_channel
                                .send(VotorEvent::FirstShred(slot))
                                .await
                                .unwrap();
                        }
                        BlockDataEvent::SliceReconstructed(slice_index) => {
                            let Some(exec_tx) = &self.exec_channel else {
                                continue;
                            };
                            let slot_data = self.slot_data(slot).unwrap();
                            let slice = &slot_data.disseminated.slices[&slice_index];

                            if slice_index.is_first() {
                                exec_tx
                                    .send(ExecutionEvent::BeginBlock {
                                        id: InProgressBlock::Pending(slot),
                                        parent: slice.parent.clone(),
                                    })
                                    .await
                                    .unwrap();
                            }

                            let transactions = deserialize_transactions(&slice.data);
                            exec_tx
                                .send(ExecutionEvent::Transactions {
                                    id: InProgressBlock::Pending(slot),
                                    transactions,
                                })
                                .await
                                .unwrap();
                        }
                        BlockDataEvent::BlockReady {
                            block_info,
                            state_hash,
                        } => {
                            debug!(
                                "reconstructed block {} in slot {} with parent {} in slot {}",
                                &hex::encode(block_info.hash.as_hash())[..8],
                                slot,
                                &hex::encode(block_info.parent.1.as_hash())[..8],
                                block_info.parent.0,
                            );
                            if let Some(exec_tx) = &self.exec_channel {
                                exec_tx
                                    .send(ExecutionEvent::EndBlock {
                                        block_id: (slot, block_info.hash),
                                        parent_id: block_info.parent,
                                        expected_state_hash: state_hash,
                                    })
                                    .await
                                    .unwrap();
                            }
                        }
                    }
                }
                Ok(())
            }
            Err(AddShredError::InvalidShred) => {
                self.votor_channel
                    .send(VotorEvent::InvalidBlock(slot))
                    .await
                    .unwrap();
                Err(AddShredError::InvalidShred)
            }
            Err(e) => Err(e),
        }
    }

    /// Stores a pre-validated shred produced by this node as leader.
    ///
    /// Emits [`VotorEvent::Block`] directly (bypassing execution validation),
    /// since the leader validated the block during production.
    #[fastrace::trace(short_name = true)]
    async fn add_own_shred_as_leader(
        &mut self,
        shred: ValidatedShred,
    ) -> Result<Option<BlockInfo>, AddShredError> {
        let slot = shred.payload().header.slot;
        let mut shredder = self
            .shredders
            .checkout()
            .expect("should have a shredder because of exclusive access");
        let events = self
            .slot_data_mut(slot)
            .add_own_shred_as_leader(shred, &mut shredder)?;
        Ok(self.handle_leader_events(slot, events).await)
    }

    /// Stores a shred received via repair.
    ///
    /// For now, emits [`VotorEvent::Block`] directly (no execution events).
    #[fastrace::trace(short_name = true)]
    async fn add_shred_from_repair(
        &mut self,
        hash: BlockHash,
        shred: Shred,
    ) -> Result<Option<BlockInfo>, AddShredError> {
        let slot = shred.payload().header.slot;
        let leader_pk = self.epoch_info.epoch_info().leader(slot).pubkey;
        let mut shredder = self
            .shredders
            .checkout()
            .expect("should have a shredder because of exclusive access");
        let events = self.slot_data_mut(slot).add_shred_from_repair(
            hash,
            shred,
            leader_pk,
            &mut shredder,
        )?;
        Ok(self.handle_leader_events(slot, events).await)
    }

    fn disseminated_block_hash(&self, slot: Slot) -> Option<&BlockHash> {
        self.slot_data(slot)?
            .disseminated
            .completed
            .as_ref()
            .map(|c| &c.0)
    }

    fn get_block(&self, block_id: &BlockId) -> Option<&Block> {
        let block_data = self.get_block_data(block_id)?;
        if let Some((hash, block)) = block_data.completed.as_ref() {
            debug_assert_eq!(*hash, block_id.1);
            Some(block)
        } else {
            None
        }
    }

    fn get_last_slice_index(&self, block_id: &BlockId) -> Option<SliceIndex> {
        self.get_block_data(block_id)?.last_slice
    }

    fn get_slice_root<'a>(
        &'a self,
        block_id: &BlockId,
        slice_index: SliceIndex,
    ) -> Option<&'a SliceRoot> {
        self.get_block_data(block_id)?
            .merkle_root_cache
            .get(&slice_index)
    }

    fn get_shred(
        &self,
        block_id: &BlockId,
        slice_index: SliceIndex,
        shred_index: ShredIndex,
    ) -> Option<&ValidatedShred> {
        let block_data = self.get_block_data(block_id)?;
        block_data.shreds.get(&slice_index)?[*shred_index].as_ref()
    }

    fn create_double_merkle_proof(
        &self,
        block_id: &BlockId,
        slice_index: SliceIndex,
    ) -> Option<DoubleMerkleProof> {
        let tree = self.get_block_data(block_id)?.double_merkle_tree.as_ref()?;
        Some(tree.create_proof(slice_index.inner()))
    }
}

/// Deserializes the transaction payload stored in a slice's data field.
///
/// The data field is `wincode::serialize(Vec<Vec<u8>>)` where each inner
/// `Vec<u8>` is a `wincode::serialize(Transaction)`.
fn deserialize_transactions(data: &[u8]) -> Vec<Transaction> {
    let raw: Vec<Vec<u8>> = wincode::deserialize(data).unwrap_or_default();
    raw.into_iter()
        .filter_map(|b| wincode::deserialize::<Transaction>(&b).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use color_eyre::Result;
    use tokio::sync::mpsc;

    use super::*;
    use crate::consensus::EpochInfo;
    use crate::crypto::aggsig;
    use crate::crypto::merkle::DoubleMerkleTree;
    use crate::crypto::signature::SecretKey;
    use crate::network::dontcare_sockaddr;
    use crate::shredder::{DATA_SHREDS, TOTAL_SHREDS};
    use crate::test_utils::create_random_shredded_block;
    use crate::types::SliceIndex;
    use crate::{Stake, ValidatorId, ValidatorInfo};

    fn test_setup(tx: Sender<VotorEvent>) -> (SecretKey, BlockstoreImpl) {
        let sk = SecretKey::new(&mut rand::rng());
        let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
        let id = ValidatorId::new(0);
        let info = ValidatorInfo {
            id,
            stake: Stake::new(1),
            pubkey: sk.to_pk(),
            voting_pubkey: voting_sk.to_pk(),
            all2all_address: dontcare_sockaddr(),
            disseminator_address: dontcare_sockaddr(),
            repair_request_address: dontcare_sockaddr(),
            repair_response_address: dontcare_sockaddr(),
        };
        let validators = vec![info];
        let epoch_info = Arc::new(ValidatorEpochInfo::new(id, EpochInfo::new(validators)));
        (sk, BlockstoreImpl::new(epoch_info, tx, None))
    }

    async fn add_shred_ignore_duplicate(
        blockstore: &mut BlockstoreImpl,
        shred: Shred,
    ) -> Result<(), AddShredError> {
        match blockstore.add_shred_from_disseminator(shred).await {
            Ok(()) => Ok(()),
            Err(AddShredError::Duplicate) => Ok(()),
            Err(e) => Err(e),
        }
    }

    #[tokio::test]
    async fn store_one_slice_block() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        assert!(blockstore.slot_data(slot).is_none());

        let (block_hash, _, shreds) = create_random_shredded_block(slot, 1, &sk);
        let block_id = (slot, block_hash);

        let slice_hash = shreds[0][0].merkle_root();
        for shred in &shreds[0] {
            add_shred_ignore_duplicate(&mut blockstore, shred.clone().into_shred()).await?;

            let Some(stored_shred) = blockstore.get_disseminated_shred(
                slot,
                SliceIndex::first(),
                shred.payload().shred_index,
            ) else {
                panic!("shred not stored");
            };
            assert_eq!(stored_shred.payload().data, shred.payload().data);
        }

        let proof = blockstore
            .create_double_merkle_proof(&block_id, SliceIndex::first())
            .unwrap();
        let slot_data = blockstore.slot_data(slot).unwrap();
        let tree = slot_data.disseminated.double_merkle_tree.as_ref().unwrap();
        let root = tree.get_root();
        assert!(DoubleMerkleTree::check_proof(&slice_hash, 0, &root, &proof));

        Ok(())
    }

    #[tokio::test]
    async fn store_two_slice_block() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);

        let (_hash, _tree, slices) = create_random_shredded_block(slot, 2, &sk);

        for shred in slices[0].clone() {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_none());

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

        let (block_hash, _tree, slices) = create_random_shredded_block(slot, 2, &sk);

        for shred in slices[0].clone().into_iter().take(DATA_SHREDS) {
            blockstore
                .add_shred_from_repair(block_hash.clone(), shred.into_shred())
                .await?;
        }
        assert!(blockstore.get_block(&(slot, block_hash.clone())).is_none());

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

        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &sk);

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

        let (_hash, _tree, slices) = create_random_shredded_block(slot, 4, &sk);
        assert_eq!(blockstore.stored_slices_for_slot(slot), 0);

        for shred in slices[0].clone().into_iter().take(DATA_SHREDS) {
            blockstore
                .add_shred_from_disseminator(shred.into_shred())
                .await?;
        }
        assert_eq!(blockstore.stored_slices_for_slot(slot), 1);

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
        assert_eq!(blockstore.stored_slices_for_slot(slot), 0);

        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_slices() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);

        let (_hash, _tree, slices) = create_random_shredded_block(slot, 2, &sk);

        for shred in slices[0].clone() {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_none());
        assert_eq!(blockstore.stored_shreds_for_slot(slot), TOTAL_SHREDS);

        for shred in slices[1].clone() {
            add_shred_ignore_duplicate(&mut blockstore, shred.into_shred()).await?;
        }
        assert!(blockstore.disseminated_block_hash(slot).is_some());
        assert_eq!(blockstore.stored_shreds_for_slot(slot), 2 * TOTAL_SHREDS);

        Ok(())
    }

    #[tokio::test]
    async fn duplicate_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &sk);

        let res = blockstore
            .add_shred_from_disseminator(slices[0][0].clone().into_shred())
            .await;
        assert!(res.is_ok());

        let res = blockstore
            .add_shred_from_disseminator(slices[0][0].clone().into_shred())
            .await;
        assert_eq!(res, Err(AddShredError::Duplicate));

        assert_eq!(blockstore.stored_shreds_for_slot(slot), 1);

        Ok(())
    }

    #[tokio::test]
    async fn invalid_shreds() -> Result<()> {
        let slot = Slot::genesis().next();
        let (tx, _rx) = mpsc::channel(100);
        let (sk, mut blockstore) = test_setup(tx);
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &sk);

        for shred in slices[0].clone() {
            let mut shred = shred.into_shred();
            shred.payload_mut().data.fill(0);
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

        assert_eq!(blockstore.stored_shreds_for_slot(block0_slot), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(block1_slot), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(block2_slot), TOTAL_SHREDS);

        blockstore.prune(block1_slot);
        assert_eq!(blockstore.stored_shreds_for_slot(block0_slot), 0);
        assert_eq!(blockstore.stored_shreds_for_slot(block1_slot), TOTAL_SHREDS);
        assert_eq!(blockstore.stored_shreds_for_slot(block2_slot), TOTAL_SHREDS);

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
