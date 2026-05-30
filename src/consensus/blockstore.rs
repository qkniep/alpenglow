// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding blocks for each slot.

mod slot_block_data;

use std::collections::BTreeMap;
use std::sync::Arc;

mod reconstruction_worker;

use async_trait::async_trait;
use tokio::sync::RwLock;
use tokio::sync::mpsc::UnboundedSender;

pub use self::reconstruction_worker::ReconstructionWorker;
pub use self::slot_block_data::AddShredError;
use self::slot_block_data::{SlotBlockData, StoreOutcome};
use crate::consensus::blockstore::slot_block_data::BlockData;
use crate::crypto::merkle::{BlockHash, DoubleMerkleProof, SliceRoot};
use crate::shredder::{
    DeshredError, RegularShredder, ShredIndex, ShredderPool, TOTAL_SHREDS, ValidatedShred,
};
use crate::types::{ReconstructedSlice, SliceIndex};
use crate::{Block, BlockId, Slot};

/// A unit of off-lock reconstruction work handed to the [`ReconstructionWorker`].
///
/// The shred set is cloned out from under the blockstore lock so the expensive
/// [`crate::shredder::Shredder::deshred`] runs without holding it.
pub struct ReconstructJob {
    /// Which block the reconstructed slice belongs to.
    pub(crate) target: ReconstructTarget,
    /// The slice to reconstruct.
    pub(crate) slice_index: SliceIndex,
    /// A snapshot of the slice's shreds, taken under the lock.
    pub(crate) shreds: Box<[Option<ValidatedShred>; TOTAL_SHREDS]>,
}

/// Identifies which block data a [`ReconstructJob`] targets.
#[derive(Clone, Debug)]
pub enum ReconstructTarget {
    /// The block received via dissemination for the given slot.
    Disseminated(Slot),
    /// The block (identified by hash) being assembled via repair for the given slot.
    Repaired(Slot, BlockHash),
}

impl ReconstructTarget {
    pub(crate) const fn slot(&self) -> Slot {
        match self {
            Self::Disseminated(slot) | Self::Repaired(slot, _) => *slot,
        }
    }
}

/// Events emitted by [`BlockstoreImpl`] to [`super::votor::Votor`].
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum BlockstoreEvent {
    /// First valid shred of the leader's block was received for the slot.
    FirstShred(Slot),
    /// New (complete) block was received in blockstore.
    Block { slot: Slot, block_info: BlockInfo },
    /// Blockstore detected an invalid block from the leader for this slot.
    InvalidBlock(Slot),
}

impl BlockstoreEvent {
    /// Returns the slot this event refers to.
    pub(crate) const fn slot(&self) -> Slot {
        match self {
            Self::FirstShred(slot) | Self::InvalidBlock(slot) => *slot,
            Self::Block { slot, .. } => *slot,
        }
    }
}

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
#[cfg_attr(test, mockall::automock)]
pub trait Blockstore {
    async fn add_shred_from_dissemination(
        &mut self,
        shred: ValidatedShred,
    ) -> Result<Option<BlockstoreEvent>, AddShredError>;
    async fn add_shred_from_repair(
        &mut self,
        hash: BlockHash,
        shred: ValidatedShred,
    ) -> Result<Option<BlockstoreEvent>, AddShredError>;
    async fn add_own_shred(
        &mut self,
        shred: ValidatedShred,
    ) -> Result<Option<BlockstoreEvent>, AddShredError>;
    async fn commit_reconstructed_slice(
        &mut self,
        target: ReconstructTarget,
        slice_index: SliceIndex,
        result: Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError>,
    ) -> Result<Option<BlockstoreEvent>, AddShredError>;
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

/// Shared, lock-protected handle to a [`Blockstore`] trait object.
pub type SharedBlockstore = Arc<RwLock<dyn Blockstore + Send + Sync>>;

/// Blockstore is the fundamental data structure holding block data per slot.
pub struct BlockstoreImpl {
    /// Data structure holding the actual block data per slot.
    block_data: BTreeMap<Slot, SlotBlockData>,
    /// Shredders used for the synchronous leader path ([`Self::add_own_shred`]).
    shredders: ShredderPool<RegularShredder>,
    /// Queue of off-lock reconstruction jobs for the [`ReconstructionWorker`].
    reconstruct_tx: UnboundedSender<ReconstructJob>,
}

impl BlockstoreImpl {
    /// Initializes a new empty blockstore.
    ///
    /// Adding shreds may produce [`BlockstoreEvent`]s, which are returned to
    /// the caller to be forwarded to Votor (so the potentially-blocking send
    /// happens outside the blockstore lock):
    /// - [`BlockstoreEvent::FirstShred`] when receiving the first shred for a slot
    ///   from the block dissemination protocol
    /// - [`BlockstoreEvent::Block`] for any reconstructed block
    /// - [`BlockstoreEvent::InvalidBlock`] if leader misbehavior is detected for a block
    ///
    /// On the dissemination and repair paths, slice reconstruction is offloaded to the
    /// [`ReconstructionWorker`] (fed via `reconstruct_tx`) so the expensive Reed–Solomon
    /// and Merkle work does not run under the blockstore lock.
    pub fn new(reconstruct_tx: UnboundedSender<ReconstructJob>) -> Self {
        Self {
            block_data: BTreeMap::new(),
            shredders: ShredderPool::with_size(1),
            reconstruct_tx,
        }
    }

    /// Deletes everything before the given `slot` from the blockstore.
    pub fn prune(&mut self, slot: Slot) {
        self.block_data = self.block_data.split_off(&slot);
    }

    /// Clones the shreds for `slice_index` of `target` and enqueues a reconstruction
    /// job for the [`ReconstructionWorker`].
    ///
    /// The clone is taken under the lock; the expensive `deshred` then runs off-lock.
    fn offload_reconstruction(&self, target: ReconstructTarget, slice_index: SliceIndex) {
        let block_data = match &target {
            ReconstructTarget::Disseminated(slot) => {
                self.block_data.get(slot).map(|sd| &sd.disseminated)
            }
            ReconstructTarget::Repaired(slot, hash) => self
                .block_data
                .get(slot)
                .and_then(|sd| sd.repaired.get(hash)),
        };
        let Some(shreds) = block_data.and_then(|bd| bd.shreds.get(&slice_index)) else {
            return;
        };
        let job = ReconstructJob {
            shreds: Box::new(shreds.clone()),
            target,
            slice_index,
        };
        // Unbounded, non-blocking send; only errors if the worker has shut down.
        let _ = self.reconstruct_tx.send(job);
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
    /// Stores a shred received via block dissemination.
    ///
    /// This shred is stored in the default spot without a known block hash.
    /// Checks for leader equivocation (unlike [`Blockstore::add_shred_from_repair`]).
    ///
    /// This only performs the cheap store; when a slice becomes reconstructable it is
    /// offloaded to the [`ReconstructionWorker`], so reconstruction does not run under the
    /// lock. Returns `Ok(Some(`[`BlockstoreEvent::FirstShred`]`))` / `Ok(None)` / a store-phase
    /// `Err` — **never** [`BlockstoreEvent::Block`] (that is emitted later by the worker).
    ///
    /// Note that an [`AddShredError::InvalidShred`] from dissemination should be surfaced to
    /// Votor as a [`BlockstoreEvent::InvalidBlock`]; the caller is responsible for emitting it.
    #[hotpath::measure]
    #[fastrace::trace(short_name = true)]
    async fn add_shred_from_dissemination(
        &mut self,
        shred: ValidatedShred,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        let slot = shred.payload().header.slot;
        match self.slot_data_mut(slot).store_from_dissemination(shred)? {
            StoreOutcome::FirstShred => Ok(Some(BlockstoreEvent::FirstShred(slot))),
            StoreOutcome::Stored => Ok(None),
            StoreOutcome::SliceReady(slice_index) => {
                self.offload_reconstruction(ReconstructTarget::Disseminated(slot), slice_index);
                Ok(None)
            }
        }
    }

    /// Stores a shred received via repair, associated with the given block `hash`.
    ///
    /// Does not check for leader equivocation across blocks. Like
    /// [`Blockstore::add_shred_from_dissemination`], reconstruction is offloaded to the
    /// [`ReconstructionWorker`]; this never returns [`BlockstoreEvent::Block`].
    #[hotpath::measure]
    #[fastrace::trace(short_name = true)]
    async fn add_shred_from_repair(
        &mut self,
        hash: BlockHash,
        shred: ValidatedShred,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        let slot = shred.payload().header.slot;
        match self
            .slot_data_mut(slot)
            .store_from_repair(hash.clone(), shred)?
        {
            StoreOutcome::FirstShred => Ok(Some(BlockstoreEvent::FirstShred(slot))),
            StoreOutcome::Stored => Ok(None),
            StoreOutcome::SliceReady(slice_index) => {
                self.offload_reconstruction(ReconstructTarget::Repaired(slot, hash), slice_index);
                Ok(None)
            }
        }
    }

    /// Stores and synchronously reconstructs a shred for the node's own produced block.
    ///
    /// Used by the leader, which needs its block available immediately and is the sole
    /// writer of its own slot — so reconstruction runs inline rather than via the worker.
    /// Returns [`BlockstoreEvent::FirstShred`] / [`BlockstoreEvent::Block`] / `None` as the
    /// fully-synchronous path.
    #[hotpath::measure]
    #[fastrace::trace(short_name = true)]
    async fn add_own_shred(
        &mut self,
        shred: ValidatedShred,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        let slot = shred.payload().header.slot;
        match self.slot_data_mut(slot).store_from_dissemination(shred)? {
            StoreOutcome::FirstShred => Ok(Some(BlockstoreEvent::FirstShred(slot))),
            StoreOutcome::Stored => Ok(None),
            StoreOutcome::SliceReady(slice_index) => {
                let mut shredder = self
                    .shredders
                    .checkout()
                    .expect("should have a shredder because of exclusive access");
                self.slot_data_mut(slot)
                    .reconstruct_own_slice(slice_index, &mut shredder)
            }
        }
    }

    /// Commits an off-lock-reconstructed slice (called by the [`ReconstructionWorker`]).
    ///
    /// Inserts the reconstructed slice and runs block reconstruction under the lock,
    /// returning any [`BlockstoreEvent::Block`] for the caller to forward.
    #[hotpath::measure]
    async fn commit_reconstructed_slice(
        &mut self,
        target: ReconstructTarget,
        slice_index: SliceIndex,
        result: Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError>,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        // do not create slot state here; if the slot is gone there is nothing to commit
        let Some(slot_data) = self.block_data.get_mut(&target.slot()) else {
            return Ok(None);
        };
        match target {
            ReconstructTarget::Disseminated(_) => {
                slot_data.commit_disseminated_slice(slice_index, result)
            }
            ReconstructTarget::Repaired(_, hash) => {
                slot_data.commit_repaired_slice(&hash, slice_index, result)
            }
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
    fn get_slice_root<'a>(
        &'a self,
        block_id: &BlockId,
        slice_index: SliceIndex,
    ) -> Option<&'a SliceRoot> {
        let block_data = self.get_block_data(block_id)?;
        block_data.merkle_root_cache.get(&slice_index)
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
    use anyhow::Result;
    use tokio::sync::mpsc::{self, UnboundedReceiver};

    use super::*;
    use crate::crypto::merkle::DoubleMerkleTree;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{DATA_SHREDS, Shredder, TOTAL_SHREDS};
    use crate::test_utils::create_random_shredded_block;
    use crate::types::SliceIndex;

    struct TestContext {
        sk: SecretKey,
        blockstore: BlockstoreImpl,
        reconstruct_rx: UnboundedReceiver<ReconstructJob>,
        shredder: RegularShredder,
    }

    fn setup() -> TestContext {
        let sk = SecretKey::new(&mut rand::rng());
        let (reconstruct_tx, reconstruct_rx) = mpsc::unbounded_channel();
        let blockstore = BlockstoreImpl::new(reconstruct_tx);
        TestContext {
            sk,
            blockstore,
            reconstruct_rx,
            shredder: RegularShredder::default(),
        }
    }

    impl TestContext {
        /// Drains all pending reconstruction jobs and commits them, emulating the
        /// [`ReconstructionWorker`] synchronously. Returns any events produced.
        async fn reconstruct_pending(&mut self) -> Vec<BlockstoreEvent> {
            let mut events = vec![];
            while let Ok(job) = self.reconstruct_rx.try_recv() {
                let ReconstructJob {
                    target,
                    slice_index,
                    shreds,
                } = job;
                let result = self.shredder.deshred(&shreds);
                if let Ok(Some(event)) = self
                    .blockstore
                    .commit_reconstructed_slice(target, slice_index, result)
                    .await
                {
                    events.push(event);
                }
            }
            events
        }
    }

    async fn add_shred_ignore_duplicate(
        blockstore: &mut BlockstoreImpl,
        shred: ValidatedShred,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        match blockstore.add_shred_from_dissemination(shred).await {
            Ok(output) => Ok(output),
            Err(AddShredError::Duplicate) => Ok(None),
            Err(e) => Err(e),
        }
    }

    #[tokio::test]
    async fn store_one_slice_block() -> Result<()> {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        assert!(ctx.blockstore.slot_data(slot).is_none());

        // generate single-slice block
        let (block_hash, _, shreds) = create_random_shredded_block(slot, 1, &ctx.sk);
        let block_id = (slot, block_hash);

        let slice_hash = shreds[0][0].merkle_root();
        for shred in &shreds[0] {
            // store shred
            add_shred_ignore_duplicate(&mut ctx.blockstore, shred.clone()).await?;

            // check shred is stored
            let Some(stored_shred) = ctx.blockstore.get_disseminated_shred(
                slot,
                SliceIndex::first(),
                shred.payload().shred_index,
            ) else {
                panic!("shred not stored");
            };
            assert_eq!(stored_shred.payload().data, shred.payload().data);
        }
        ctx.reconstruct_pending().await;

        // create and check double-Merkle proof
        let proof = ctx
            .blockstore
            .create_double_merkle_proof(&block_id, SliceIndex::first())
            .unwrap();
        let slot_data = ctx.blockstore.slot_data(slot).unwrap();
        let tree = slot_data.disseminated.double_merkle_tree.as_ref().unwrap();
        let root = tree.get_root();
        assert!(DoubleMerkleTree::check_proof(slice_hash, 0, &root, &proof));

        Ok(())
    }

    #[tokio::test]
    async fn store_two_slice_block() -> Result<()> {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        assert!(ctx.blockstore.slot_data(slot).is_none());

        // generate two-slice block
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 2, &ctx.sk);

        // first slice is not enough
        for shred in slices[0].clone() {
            add_shred_ignore_duplicate(&mut ctx.blockstore, shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_none());

        // after second slice we should have the block
        for shred in slices[1].clone() {
            add_shred_ignore_duplicate(&mut ctx.blockstore, shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn store_block_from_repair() -> Result<()> {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        assert!(ctx.blockstore.slot_data(slot).is_none());

        // generate and shred two slices
        let (block_hash, _tree, slices) = create_random_shredded_block(slot, 2, &ctx.sk);

        // first slice is not enough
        for shred in slices[0].clone().into_iter().take(DATA_SHREDS) {
            ctx.blockstore
                .add_shred_from_repair(block_hash.clone(), shred)
                .await?;
        }
        ctx.reconstruct_pending().await;
        assert!(
            ctx.blockstore
                .get_block(&(slot, block_hash.clone()))
                .is_none()
        );

        // after second slice we should have the block
        for shred in slices[1].clone().into_iter().take(DATA_SHREDS) {
            ctx.blockstore
                .add_shred_from_repair(block_hash.clone(), shred)
                .await?;
        }
        ctx.reconstruct_pending().await;
        assert!(ctx.blockstore.get_block(&(slot, block_hash)).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_shreds() -> Result<()> {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_none());

        // generate a single slice for slot 0
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &ctx.sk);

        // insert shreds in reverse order
        for shred in slices[0].clone().into_iter().rev() {
            add_shred_ignore_duplicate(&mut ctx.blockstore, shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_some());

        Ok(())
    }

    #[tokio::test]
    async fn just_enough_shreds() -> Result<()> {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_none());

        // generate a larger block for slot 0
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 4, &ctx.sk);
        assert_eq!(ctx.blockstore.stored_slices_for_slot(slot), 0);

        // insert just enough shreds to reconstruct slice 0 (from beginning)
        for shred in slices[0].clone().into_iter().take(DATA_SHREDS) {
            ctx.blockstore.add_shred_from_dissemination(shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert_eq!(ctx.blockstore.stored_slices_for_slot(slot), 1);

        // insert just enough shreds to reconstruct slice 1 (from end)
        for shred in slices[1]
            .clone()
            .into_iter()
            .skip(TOTAL_SHREDS - DATA_SHREDS)
        {
            ctx.blockstore.add_shred_from_dissemination(shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert_eq!(ctx.blockstore.stored_slices_for_slot(slot), 2);

        // insert just enough shreds to reconstruct slice 2 (from middle)
        for shred in slices[2]
            .clone()
            .into_iter()
            .skip((TOTAL_SHREDS - DATA_SHREDS) / 2)
            .take(DATA_SHREDS)
        {
            ctx.blockstore.add_shred_from_dissemination(shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert_eq!(ctx.blockstore.stored_slices_for_slot(slot), 3);

        // insert just enough shreds to reconstruct slice 3 (split)
        for (_, shred) in slices[3]
            .clone()
            .into_iter()
            .enumerate()
            .filter(|(i, _)| *i < DATA_SHREDS / 2 || *i >= TOTAL_SHREDS - DATA_SHREDS / 2)
        {
            ctx.blockstore.add_shred_from_dissemination(shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_some());

        // slices are deleted after reconstruction
        assert_eq!(ctx.blockstore.stored_slices_for_slot(slot), 0);

        Ok(())
    }

    #[tokio::test]
    async fn out_of_order_slices() -> Result<()> {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_none());

        // generate two slices for slot 0
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 2, &ctx.sk);

        // second slice alone is not enough
        for shred in slices[0].clone() {
            add_shred_ignore_duplicate(&mut ctx.blockstore, shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_none());

        // stored all shreds for slot 0
        assert_eq!(ctx.blockstore.stored_shreds_for_slot(slot), TOTAL_SHREDS);

        // after also also inserting first slice we should have the block
        for shred in slices[1].clone() {
            add_shred_ignore_duplicate(&mut ctx.blockstore, shred).await?;
        }
        ctx.reconstruct_pending().await;
        assert!(ctx.blockstore.disseminated_block_hash(slot).is_some());

        // stored all shreds
        assert_eq!(
            ctx.blockstore.stored_shreds_for_slot(slot),
            2 * TOTAL_SHREDS
        );

        Ok(())
    }

    #[tokio::test]
    async fn duplicate_shreds() -> Result<()> {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &ctx.sk);

        // inserting single shred should not throw errors
        let res = ctx
            .blockstore
            .add_shred_from_dissemination(slices[0][0].clone())
            .await;
        assert!(res.is_ok());

        // inserting same shred again should give duplicate error
        let res = ctx
            .blockstore
            .add_shred_from_dissemination(slices[0][0].clone())
            .await;
        assert_eq!(res, Err(AddShredError::Duplicate));

        // should only store one copy
        assert_eq!(ctx.blockstore.stored_shreds_for_slot(slot), 1);

        Ok(())
    }

    #[tokio::test]
    async fn reconstruction_offloaded_exactly_once() -> Result<()> {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        let (_hash, _tree, slices) = create_random_shredded_block(slot, 1, &ctx.sk);

        // the DATA_SHREDS-th shred makes the slice reconstructable -> exactly one job
        for shred in slices[0].clone().into_iter().take(DATA_SHREDS) {
            ctx.blockstore.add_shred_from_dissemination(shred).await?;
        }
        let mut jobs = 0;
        while ctx.reconstruct_rx.try_recv().is_ok() {
            jobs += 1;
        }
        assert_eq!(jobs, 1, "exactly one reconstruction job should be enqueued");

        // further shreds for the same (not-yet-reconstructed) slice must not re-offload
        for shred in slices[0].clone().into_iter().skip(DATA_SHREDS) {
            ctx.blockstore.add_shred_from_dissemination(shred).await?;
        }
        assert!(
            ctx.reconstruct_rx.try_recv().is_err(),
            "no further jobs should be enqueued for the same slice"
        );

        Ok(())
    }

    #[tokio::test]
    async fn pruning() -> Result<()> {
        let mut ctx = setup();
        let block0_slot = Slot::genesis().next();
        let block1_slot = block0_slot.next();
        let block2_slot = block1_slot.next();
        let block3_slot = block2_slot.next();
        let future_slot = block3_slot.next();
        let block0 = create_random_shredded_block(block0_slot, 1, &ctx.sk);
        let block1 = create_random_shredded_block(block1_slot, 1, &ctx.sk);
        let block2 = create_random_shredded_block(block2_slot, 1, &ctx.sk);
        let blockstore = &mut ctx.blockstore;

        // insert shreds
        let mut shreds = vec![];
        shreds.extend(block0.2.into_iter().flatten());
        shreds.extend(block1.2.into_iter().flatten());
        shreds.extend(block2.2.into_iter().flatten());
        for shred in shreds {
            add_shred_ignore_duplicate(blockstore, shred).await?;
        }
        ctx.reconstruct_pending().await;
        let blockstore = &mut ctx.blockstore;
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
