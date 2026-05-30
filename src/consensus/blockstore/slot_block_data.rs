// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding shreds, slices and blocks for a specific slot.
//!
//!

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use log::{debug, trace, warn};
use thiserror::Error;

use super::{BlockInfo, BlockstoreEvent};
use crate::crypto::merkle::{BlockHash, DoubleMerkleTree, SliceRoot};
use crate::shredder::{
    DATA_SHREDS, DeshredError, RegularShredder, Shredder, TOTAL_SHREDS, ValidatedShred,
};
use crate::types::{ReconstructedSlice, SliceIndex};
use crate::{Block, Slot};

/// Errors that may be encountered when adding a shred.
///
/// Signature verification is performed by the caller (via [`ValidatedShred`])
/// before invoking the blockstore, so signature failures cannot surface here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum AddShredError {
    #[error("shred is already stored")]
    Duplicate,
    #[error("shred shows leader equivocation")]
    Equivocation,
    #[error("shred was invalid and leader did not equivocate")]
    InvalidShred,
}

/// Holds all data corresponding to any blocks for a single slot.
pub(super) struct SlotBlockData {
    /// Slot number this data corresponds to.
    slot: Slot,
    /// Spot for storing the block that was received via block dissemination.
    pub(super) disseminated: BlockData,
    /// Spot for storing blocks that might later be received via repair.
    pub(super) repaired: BTreeMap<BlockHash, BlockData>,
    /// Tracks whether we observed the leader misbehaving.
    /// If we do, we stop adding [`ValidatedShred`]s from dissemination.
    leader_misbehaved: bool,
}

impl SlotBlockData {
    /// Creates a new empty structure for a slot's block data.
    pub(super) fn new(slot: Slot) -> Self {
        Self {
            slot,
            disseminated: BlockData::new(slot),
            repaired: BTreeMap::new(),
            leader_misbehaved: false,
        }
    }

    /// Stores a shred received via block dissemination (cheap, no reconstruction).
    ///
    /// The shred must already have a verified leader signature (see [`ValidatedShred`]).
    /// Checks for leader equivocation against any previously stored shred for the slice.
    /// When the returned [`StoreOutcome`] is [`StoreOutcome::SliceReady`], the caller is
    /// responsible for reconstructing that slice (off-lock) and committing it via
    /// [`SlotBlockData::commit_disseminated_slice`].
    pub(super) fn store_from_dissemination(
        &mut self,
        shred: ValidatedShred,
    ) -> Result<StoreOutcome, AddShredError> {
        debug_assert_eq!(shred.payload().header.slot, self.slot);
        if self.leader_misbehaved {
            debug!("received shred from misbehaving leader, not adding to blockstore");
            return Err(AddShredError::InvalidShred);
        }
        self.disseminated
            .add_shred(shred)
            .inspect_err(|err| match err {
                AddShredError::Equivocation | AddShredError::InvalidShred => {
                    self.leader_misbehaved = true;
                }
                AddShredError::Duplicate => (),
            })
    }

    /// Stores a shred received via repair to the spot given by block hash.
    ///
    /// The shred must already have a verified leader signature (see [`ValidatedShred`]).
    /// Performs validity checks except for leader equivocation across blocks.
    /// See [`SlotBlockData::store_from_dissemination`] for the [`StoreOutcome`] contract.
    pub(super) fn store_from_repair(
        &mut self,
        hash: BlockHash,
        shred: ValidatedShred,
    ) -> Result<StoreOutcome, AddShredError> {
        debug_assert_eq!(shred.payload().header.slot, self.slot);
        let block_data = self
            .repaired
            .entry(hash)
            .or_insert_with(|| BlockData::new(self.slot));
        block_data.add_shred(shred).inspect_err(|err| match err {
            AddShredError::Equivocation | AddShredError::InvalidShred => {
                self.leader_misbehaved = true;
            }
            AddShredError::Duplicate => (),
        })
    }

    /// Synchronously reconstructs slice `index` of the disseminated block.
    ///
    /// Used by the leader for its own freshly-produced block, where the block needs
    /// to be available immediately. Returns the resulting [`BlockstoreEvent`], if any.
    pub(super) fn reconstruct_own_slice(
        &mut self,
        index: SliceIndex,
        shredder: &mut RegularShredder,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        self.disseminated
            .reconstruct_slice_sync(index, shredder)
            .inspect_err(|err| match err {
                AddShredError::Equivocation | AddShredError::InvalidShred => {
                    self.leader_misbehaved = true;
                }
                AddShredError::Duplicate => (),
            })
    }

    /// Commits an off-lock-reconstructed slice into the disseminated block.
    ///
    /// `result` is the output of [`Shredder::deshred`] for the slice, computed off-lock.
    pub(super) fn commit_disseminated_slice(
        &mut self,
        index: SliceIndex,
        result: Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError>,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        self.disseminated
            .commit_reconstructed_slice(index, result)
            .inspect_err(|err| match err {
                AddShredError::Equivocation | AddShredError::InvalidShred => {
                    self.leader_misbehaved = true;
                }
                AddShredError::Duplicate => (),
            })
    }

    /// Commits an off-lock-reconstructed slice into the repaired block for `hash`.
    pub(super) fn commit_repaired_slice(
        &mut self,
        hash: &BlockHash,
        index: SliceIndex,
        result: Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError>,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        let Some(block_data) = self.repaired.get_mut(hash) else {
            return Ok(None);
        };
        block_data
            .commit_reconstructed_slice(index, result)
            .inspect_err(|err| match err {
                AddShredError::Equivocation | AddShredError::InvalidShred => {
                    self.leader_misbehaved = true;
                }
                AddShredError::Duplicate => (),
            })
    }
}

/// Outcome of storing a shred (the cheap, under-lock phase of adding a shred).
pub(super) enum StoreOutcome {
    /// The first shred of this block was stored; nothing to reconstruct yet.
    FirstShred,
    /// The shred was stored; no slice became ready to reconstruct.
    Stored,
    /// The shred was stored and the given slice now has enough shreds to be
    /// reconstructed and has not been reconstructed yet. The caller should
    /// reconstruct it (off-lock) and commit it.
    SliceReady(SliceIndex),
}

/// Returned value from [`BlockData::try_reconstruct_block`]
enum ReconstructBlockResult {
    /// Either block was already reconstructed or not enough data.
    NoAction,
    /// Encountered an error reconstructing the block.
    Error,
    /// Block successfully reconstructed.
    /// [`BlockInfo`] describing the block is returned.
    Complete(BlockInfo),
}

/// Holds all data corresponding to a single block.
pub(super) struct BlockData {
    /// Slot number this block is in.
    slot: Slot,
    /// Potentially completely restored block.
    pub(super) completed: Option<(BlockHash, Block)>,
    /// Any shreds of this block stored so far, indexed by slice index.
    pub(super) shreds: BTreeMap<SliceIndex, [Option<ValidatedShred>; TOTAL_SHREDS]>,
    /// Any already reconstructed slices of this block.
    pub(super) slices: BTreeMap<SliceIndex, ReconstructedSlice>,
    /// Index of the slice marked as last, if any.
    pub(super) last_slice: Option<SliceIndex>,
    /// Double merkle tree of this block, only known if block has been reconstructed.
    pub(super) double_merkle_tree: Option<DoubleMerkleTree>,
    /// Cache of Merkle roots for which the leader signature has been verified.
    pub(super) merkle_root_cache: BTreeMap<SliceIndex, SliceRoot>,
}

impl BlockData {
    /// Create a new spot for storing data of a single block.
    pub(super) fn new(slot: Slot) -> Self {
        Self {
            slot,
            completed: None,
            shreds: BTreeMap::new(),
            slices: BTreeMap::new(),
            last_slice: None,
            double_merkle_tree: None,
            merkle_root_cache: BTreeMap::new(),
        }
    }

    /// Stores a shred, without performing any (expensive) slice reconstruction.
    ///
    /// Returns a [`StoreOutcome`] indicating whether this was the first shred, whether
    /// a slice has become reconstructable, or that there is nothing further to do.
    fn add_shred(&mut self, shred: ValidatedShred) -> Result<StoreOutcome, AddShredError> {
        debug_assert_eq!(shred.payload().header.slot, self.slot);
        let slice_index = shred.payload().header.slice_index;
        let is_last = shred.payload().header.is_last;
        let shred_index = shred.payload().shred_index;

        // different valid signatures for the same slice -> leader equivocation
        if let Some(cached) = self.merkle_root_cache.get(&slice_index)
            && cached != shred.merkle_root()
        {
            return Err(AddShredError::Equivocation);
        }

        // populate Merkle root cache
        if let Entry::Vacant(entry) = self.merkle_root_cache.entry(slice_index) {
            entry.insert(shred.merkle_root().clone());
        }

        match (is_last, self.last_slice) {
            (true, None) => {
                self.last_slice = Some(slice_index);
                self.slices.retain(|&ind, _| ind <= slice_index);
                self.shreds.retain(|&ind, _| ind <= slice_index);
            }
            (true, Some(l)) => {
                if slice_index != l {
                    return Err(AddShredError::InvalidShred);
                }
            }
            (false, None) => (),
            (false, Some(l)) => {
                if slice_index >= l {
                    return Err(AddShredError::InvalidShred);
                }
            }
        }

        let is_first_shred = self.shreds.is_empty();
        let slice_shreds = self
            .shreds
            .entry(slice_index)
            .or_insert([const { None }; TOTAL_SHREDS]);
        if slice_shreds[*shred_index].is_some() {
            debug!(
                "dropping duplicate shred {}-{} in slot {}",
                slice_index, shred_index, self.slot
            );
            return Err(AddShredError::Duplicate);
        }
        slice_shreds[*shred_index] = Some(shred);

        if is_first_shred {
            return Ok(StoreOutcome::FirstShred);
        }

        // Signal that this slice can now be reconstructed, exactly once: the
        // shred count passes through `DATA_SHREDS` a single time (duplicates are
        // rejected above), and we gate on the slice not already being reconstructed.
        if !self.slices.contains_key(&slice_index)
            && slice_shreds.iter().filter(|s| s.is_some()).count() == DATA_SHREDS
        {
            return Ok(StoreOutcome::SliceReady(slice_index));
        }
        Ok(StoreOutcome::Stored)
    }

    /// Reconstructs slice `index` in place (synchronous deshred + commit).
    ///
    /// Used by the leader path, where reconstruction happens inline rather than
    /// being offloaded to the reconstruction worker.
    fn reconstruct_slice_sync(
        &mut self,
        index: SliceIndex,
        shredder: &mut RegularShredder,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        let result = match self.shreds.get(&index) {
            Some(slice_shreds) => shredder.deshred(slice_shreds),
            None => return Ok(None),
        };
        self.commit_reconstructed_slice(index, result)
    }

    /// Commits a (possibly off-lock) reconstructed slice, then tries to reconstruct
    /// the block. Re-validates against state that may have changed since the slice
    /// was deemed reconstructable (block completed, a later `is_last` shred arrived,
    /// or the slice was already reconstructed).
    ///
    /// `result` is the output of [`Shredder::deshred`] for the slice.
    #[hotpath::measure]
    fn commit_reconstructed_slice(
        &mut self,
        index: SliceIndex,
        result: Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError>,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        if self.completed.is_some() {
            trace!("already have block for slot {}", self.slot);
            return Ok(None);
        }
        // a later `is_last` shred may have run `retain`, making this slice obsolete
        if let Some(last) = self.last_slice
            && index > last
        {
            return Ok(None);
        }
        // already reconstructed (e.g. a duplicate trigger)
        if self.slices.contains_key(&index) {
            return Ok(None);
        }

        let (reconstructed_slice, reconstructed_shreds) = match result {
            Ok(output) => output,
            Err(DeshredError::NotEnoughShreds) => return Ok(None),
            Err(rest) => {
                warn!(
                    "deshreding slice {index} in slot {} failed with {rest:?}",
                    self.slot
                );
                return Err(AddShredError::InvalidShred);
            }
        };
        if reconstructed_slice.parent.is_none() && reconstructed_slice.slice_index.is_first() {
            warn!(
                "reconstructed slice {} in slot {} expected to contain parent",
                index, self.slot
            );
            return Err(AddShredError::InvalidShred);
        }

        // insert reconstructed slice and the full reconstructed shred set
        let Some(slice_shreds) = self.shreds.get_mut(&index) else {
            return Ok(None);
        };
        let mut reconstructed_shreds = reconstructed_shreds.map(Some);
        std::mem::swap(slice_shreds, &mut reconstructed_shreds);
        self.slices.insert(index, reconstructed_slice);
        trace!("reconstructed slice {} in slot {}", index, self.slot);

        match self.try_reconstruct_block() {
            ReconstructBlockResult::NoAction => Ok(None),
            ReconstructBlockResult::Error => Err(AddShredError::InvalidShred),
            ReconstructBlockResult::Complete(block_info) => Ok(Some(BlockstoreEvent::Block {
                slot: self.slot,
                block_info,
            })),
        }
    }

    /// Reconstructs the block if the blockstore contains all slices.
    ///
    /// See [`ReconstructBlockResult`] for more info on what the function returns.
    #[hotpath::measure]
    fn try_reconstruct_block(&mut self) -> ReconstructBlockResult {
        if self.completed.is_some() {
            trace!("already have block for slot {}", self.slot);
            return ReconstructBlockResult::NoAction;
        }
        let Some(last_slice) = self.last_slice else {
            return ReconstructBlockResult::NoAction;
        };
        if self.slices.len() != last_slice.inner() + 1 {
            trace!("don't have all slices for slot {} yet", self.slot);
            return ReconstructBlockResult::NoAction;
        }

        // calculate double-Merkle tree & block hash
        let merkle_roots = self.slices.values().map(|s| s.merkle_root());
        let tree = DoubleMerkleTree::new(merkle_roots);
        let block_hash = tree.get_root();
        self.double_merkle_tree = Some(tree);

        // reconstruct block header
        let first_slice = self.slices.get(&SliceIndex::first()).unwrap();
        // based on the logic in `try_reconstruct_slice`, first_slice should be valid i.e. it must contain a parent.
        let mut parent = first_slice.parent.clone().unwrap();
        let mut parent_switched = false;

        let mut transactions = vec![];
        for (ind, slice) in &self.slices {
            // handle optimistic handover
            if !ind.is_first()
                && let Some(new_parent) = slice.parent.clone()
            {
                if new_parent == parent {
                    warn!("parent switched to same value");
                    return ReconstructBlockResult::Error;
                }
                if parent_switched {
                    warn!("parent switched more than once");
                    return ReconstructBlockResult::Error;
                }
                parent_switched = true;
                parent = new_parent;
            }

            let mut txs = match wincode::deserialize(&slice.data) {
                Ok(r) => r,
                Err(err) => {
                    warn!("decoding slice {ind} failed with {err:?}");
                    return ReconstructBlockResult::Error;
                }
            };
            transactions.append(&mut txs);
        }

        let block = Block {
            _slot: self.slot,
            hash: block_hash.clone(),
            parent: parent.0,
            parent_hash: parent.1,
            _transactions: transactions,
        };
        let block_info = BlockInfo::from(&block);
        debug!(
            "reconstructed block {} in slot {} with parent {} in slot {}",
            block_info.hash.short_hex(),
            self.slot,
            block_info.parent.1.short_hex(),
            block_info.parent.0,
        );
        self.completed = Some((block_hash, block));

        // clean up raw slices
        for slice_index in last_slice.until() {
            self.slices.remove(&slice_index);
        }

        ReconstructBlockResult::Complete(block_info)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{DATA_SHREDS, ShredIndex, TOTAL_SHREDS};
    use crate::test_utils::create_random_block;
    use crate::types::Slice;

    /// Stores a shred and synchronously reconstructs the slice when ready.
    ///
    /// Mirrors the leader (`add_own_shred`) path so tests can drive store +
    /// reconstruction in one call.
    fn add_shred_sync(
        block_data: &mut BlockData,
        shred: ValidatedShred,
        shredder: &mut RegularShredder,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        match block_data.add_shred(shred)? {
            StoreOutcome::FirstShred => Ok(Some(BlockstoreEvent::FirstShred(block_data.slot))),
            StoreOutcome::Stored => Ok(None),
            StoreOutcome::SliceReady(index) => block_data.reconstruct_slice_sync(index, shredder),
        }
    }

    fn handle_slice(
        block_data: &mut BlockData,
        slice: Slice,
        sk: &SecretKey,
    ) -> (Vec<BlockstoreEvent>, Result<(), AddShredError>) {
        let mut shredder = RegularShredder::default();
        let shreds = shredder.shred(slice, sk).unwrap();
        let mut events = vec![];
        for shred in shreds {
            match add_shred_sync(block_data, shred, &mut shredder) {
                Ok(Some(event)) => {
                    events.push(event);
                }
                Ok(None) | Err(AddShredError::Duplicate) => (),
                Err(err) => return (events, Err(err)),
            }
        }
        (events, Ok(()))
    }

    fn get_block_hash_from_votor_event(event: &BlockstoreEvent) -> BlockHash {
        match event {
            BlockstoreEvent::Block {
                slot: _,
                block_info: BlockInfo { hash, parent: _ },
            } => hash.clone(),
            _ => panic!(),
        }
    }

    #[test]
    fn reconstruct_slice_and_shreds() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);

        // manage to construct block from just enough shreds
        let slices = create_random_block(slot, 1);
        let mut block_data = BlockData::new(slot);
        let mut shredder = RegularShredder::default();
        let shreds = shredder.shred(slices[0].clone(), &sk).unwrap();
        let mut events = vec![];
        for shred in shreds.into_iter().skip(TOTAL_SHREDS - DATA_SHREDS) {
            if let Some(event) = add_shred_sync(&mut block_data, shred, &mut shredder).unwrap() {
                events.push(event);
            }
        }
        assert!(block_data.completed.is_some());

        // all shreds should have been reconstructed
        let slice_shreds = block_data.shreds.get(&SliceIndex::first()).unwrap();
        assert_eq!(slice_shreds.len(), TOTAL_SHREDS);
        for shred_index in ShredIndex::all() {
            assert!(slice_shreds[*shred_index].is_some());
        }
    }

    #[test]
    fn reconstruct_slice_invalid_parent() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);

        // manage to construct a valid block
        let slices = create_random_block(slot, 1);
        let (events, res) =
            handle_slice(&mut BlockData::new(slices[0].slot), slices[0].clone(), &sk);
        let () = res.unwrap();
        assert_eq!(events.len(), 2);
        let first_shred_event = BlockstoreEvent::FirstShred(slot);
        assert_eq!(events[0].clone(), first_shred_event);
        let hash = get_block_hash_from_votor_event(&events[1]);
        let block_event = BlockstoreEvent::Block {
            slot,
            block_info: BlockInfo {
                hash,
                parent: slices[0].parent.clone().unwrap(),
            },
        };
        assert_eq!(events[1].clone(), block_event);

        // do not construct a valid block when slice is invalid
        let mut slices = create_random_block(slot, 1);
        slices[0].parent = None;
        let (events, res) =
            handle_slice(&mut BlockData::new(slices[0].slot), slices[0].clone(), &sk);
        assert_eq!(res.unwrap_err(), AddShredError::InvalidShred);
        assert_eq!(events.len(), 1);
        let first_shred_event = BlockstoreEvent::FirstShred(slot);
        assert_eq!(events[0].clone(), first_shred_event);
    }

    // If a subsequent slice switches parent to the original, the block is not reconstructed.
    #[test]
    fn reconstruct_block_optimistic_handover_duplicate_parent() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);
        let mut slices = create_random_block(slot, 3);
        slices[2].parent = slices[0].parent.clone();

        let mut block_data = BlockData::new(slot);
        let mut events = vec![];
        for (ind, slice) in slices.into_iter().enumerate() {
            let (mut evs, res) = handle_slice(&mut block_data, slice, &sk);
            events.append(&mut evs);
            if ind == 0 || ind == 1 {
                let () = res.unwrap();
            } else {
                assert_eq!(res.unwrap_err(), AddShredError::InvalidShred);
            }
        }
        assert_eq!(events.len(), 1);
        match events[0] {
            BlockstoreEvent::FirstShred(s) => assert_eq!(slot, s),
            _ => panic!(),
        }
    }

    // Two switches of parents do not reconstruct block.
    #[test]
    fn reconstruct_block_optimistic_handover_two_switches() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);
        let mut slices = create_random_block(slot, 3);
        let parent = slices[0].parent.clone().unwrap();
        let slice_1_parent = (parent.0.next(), parent.1.clone());
        assert!(slice_1_parent.0 < slot);
        let slice_2_parent = (parent.0.next().next(), parent.1);
        assert!(slice_2_parent.0 < slot);
        slices[1].parent = Some(slice_1_parent);
        slices[2].parent = Some(slice_2_parent);

        let mut block_data = BlockData::new(slot);
        let mut events = vec![];
        for (ind, slice) in slices.into_iter().enumerate() {
            let (mut evs, res) = handle_slice(&mut block_data, slice, &sk);
            events.append(&mut evs);
            if ind == 0 || ind == 1 {
                let () = res.unwrap();
            } else {
                assert_eq!(res.unwrap_err(), AddShredError::InvalidShred);
            }
        }
        assert_eq!(events.len(), 1);
        match events[0] {
            BlockstoreEvent::FirstShred(s) => assert_eq!(slot, s),
            _ => panic!(),
        }
    }

    // Optimistic handover works.
    #[test]
    fn reconstruct_block_optimistic_handover_works() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);
        let mut slices = create_random_block(slot, 3);
        let parent = slices[0].parent.clone().unwrap();
        let slice_1_parent = (parent.0.next(), parent.1);
        assert!(slice_1_parent.0 < slot);
        slices[1].parent = Some(slice_1_parent.clone());

        let mut block_data = BlockData::new(slot);
        let mut events = vec![];
        for slice in slices {
            let (mut evs, res) = handle_slice(&mut block_data, slice, &sk);
            events.append(&mut evs);
            let () = res.unwrap();
        }
        assert_eq!(events.len(), 2);
        match events[0] {
            BlockstoreEvent::FirstShred(s) => assert_eq!(slot, s),
            _ => panic!(),
        }
        match &events[1] {
            BlockstoreEvent::Block {
                slot: ret_slot,
                block_info,
            } => {
                assert_eq!(*ret_slot, slot);
                assert_eq!(block_info.parent, slice_1_parent);
            }
            _ => panic!(),
        }
    }
}
