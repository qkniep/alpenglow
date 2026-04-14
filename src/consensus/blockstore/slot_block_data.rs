// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding shreds, slices and blocks for a specific slot.

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use log::{debug, trace, warn};
use thiserror::Error;

use super::BlockInfo;
use crate::crypto::Hash;
use crate::crypto::merkle::{BlockHash, DoubleMerkleTree, SliceRoot};
use crate::crypto::signature::PublicKey;
use crate::shredder::{
    DeshredError, RegularShredder, Shred, ShredVerifyError, Shredder, TOTAL_SHREDS, ValidatedShred,
};
use crate::types::{ReconstructedSlice, SliceIndex};
use crate::{Block, Slot};

/// Errors that may be encountered when adding a shred.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum AddShredError {
    #[error("shred has invalid signature")]
    InvalidSignature,
    #[error("shred is already stored")]
    Duplicate,
    #[error("shred shows leader equivocation")]
    Equivocation,
    #[error("shred was invalid and leader did not equivocate")]
    InvalidShred,
}

impl From<ShredVerifyError> for AddShredError {
    fn from(src: ShredVerifyError) -> Self {
        match src {
            ShredVerifyError::InvalidSignature => AddShredError::InvalidSignature,
            ShredVerifyError::Equivocation => AddShredError::Equivocation,
        }
    }
}

/// Events emitted by [`BlockData`] when shreds are added.
///
/// These are interpreted by [`super::super::BlockstoreImpl`], which routes them
/// to the votor event channel and/or the execution event channel as appropriate.
pub(super) enum BlockDataEvent {
    /// First shred for this slot was received.
    FirstShred,
    /// A slice was successfully reconstructed from shreds.
    SliceReconstructed(SliceIndex),
    /// All slices are present and the block is fully reconstructed.
    ///
    /// `state_hash` is the execution state hash extracted from the last slice's
    /// data suffix, placed there by the proposer before shredding.
    BlockReady {
        block_info: BlockInfo,
        state_hash: Hash,
    },
}

/// Holds all data corresponding to any blocks for a single slot.
pub struct SlotBlockData {
    /// Slot number this data corresponds to.
    slot: Slot,
    /// Spot for storing the block that was received via block dissemination.
    pub(super) disseminated: BlockData,
    /// Spot for storing blocks that might later be received via repair.
    pub(super) repaired: BTreeMap<BlockHash, BlockData>,
    /// Tracks whether we observed the leader misbehaving.
    /// Once misbehavior is observed, we stop accepting additional [`Shred`]s through dissemination.
    leader_misbehaved: bool,
}

impl SlotBlockData {
    /// Creates a new empty structure for a slot's block data.
    pub fn new(slot: Slot) -> Self {
        Self {
            slot,
            disseminated: BlockData::new(slot),
            repaired: BTreeMap::new(),
            leader_misbehaved: false,
        }
    }

    /// Adds a shred received via block dissemination.
    pub fn add_shred_from_disseminator(
        &mut self,
        shred: Shred,
        leader_pk: PublicKey,
        shredder: &mut RegularShredder,
    ) -> Result<Vec<BlockDataEvent>, AddShredError> {
        assert_eq!(shred.payload().header.slot, self.slot);
        if self.leader_misbehaved {
            debug!("received shred from misbehaving leader, not adding to blockstore");
            return Err(AddShredError::InvalidShred);
        }
        self.disseminated
            .add_shred(shred, leader_pk, shredder)
            .inspect_err(|err| match err {
                AddShredError::Equivocation | AddShredError::InvalidShred => {
                    self.leader_misbehaved = true;
                }
                _ => (),
            })
    }

    /// Adds a pre-validated shred produced by this node as leader.
    pub fn add_own_shred_as_leader(
        &mut self,
        validated_shred: ValidatedShred,
        shredder: &mut RegularShredder,
    ) -> Result<Vec<BlockDataEvent>, AddShredError> {
        self.disseminated
            .add_validated_shred(validated_shred, shredder)
    }

    /// Adds a shred received via repair to the spot given by block hash.
    pub fn add_shred_from_repair(
        &mut self,
        hash: BlockHash,
        shred: Shred,
        leader_pk: PublicKey,
        shredder: &mut RegularShredder,
    ) -> Result<Vec<BlockDataEvent>, AddShredError> {
        assert_eq!(shred.payload().header.slot, self.slot);
        let block_data = self
            .repaired
            .entry(hash)
            .or_insert_with(|| BlockData::new(self.slot));
        block_data
            .add_shred(shred, leader_pk, shredder)
            .inspect_err(|err| match err {
                AddShredError::Equivocation | AddShredError::InvalidShred => {
                    self.leader_misbehaved = true;
                }
                _ => (),
            })
    }
}

/// Returned value from [`BlockData::try_reconstruct_slice`]
enum ReconstructSliceResult {
    /// Either slice was already reconstructed or not enough data.
    NoAction,
    /// Encountered an error reconstructing the slice.
    Error,
    /// Slice successfully reconstructed.
    Complete,
}

/// Returned value from [`BlockData::try_reconstruct_block`]
enum ReconstructBlockResult {
    /// Either block was already reconstructed or not enough data.
    NoAction,
    /// Encountered an error reconstructing the block.
    Error,
    /// Block successfully reconstructed.
    Complete(BlockInfo, Hash),
}

/// Holds all data corresponding to a single block.
pub struct BlockData {
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
    /// Execution state hash extracted from the last slice's data, once reconstructed.
    last_slice_state_hash: Option<Hash>,
}

impl BlockData {
    /// Create a new spot for storing data of a single block.
    pub fn new(slot: Slot) -> Self {
        Self {
            slot,
            completed: None,
            shreds: BTreeMap::new(),
            slices: BTreeMap::new(),
            last_slice: None,
            double_merkle_tree: None,
            merkle_root_cache: BTreeMap::new(),
            last_slice_state_hash: None,
        }
    }

    fn add_shred(
        &mut self,
        shred: Shred,
        leader_pk: PublicKey,
        shredder: &mut RegularShredder,
    ) -> Result<Vec<BlockDataEvent>, AddShredError> {
        assert!(shred.payload().header.slot == self.slot);
        let slice_index = shred.payload().header.slice_index;
        let cached_merkle_root = self.merkle_root_cache.get(&slice_index);
        let validated_shred = ValidatedShred::try_new(shred, cached_merkle_root, &leader_pk)?;
        self.add_validated_shred(validated_shred, shredder)
    }

    fn add_validated_shred(
        &mut self,
        validated_shred: ValidatedShred,
        shredder: &mut RegularShredder,
    ) -> Result<Vec<BlockDataEvent>, AddShredError> {
        let header = &validated_shred.payload().header;
        assert!(header.slot == self.slot);
        let slice_index = header.slice_index;

        // populate Merkle root cache
        let cached_merkle_root = self.merkle_root_cache.entry(slice_index);
        if let Entry::Vacant(entry) = cached_merkle_root {
            let derived_root = validated_shred.merkle_root();
            entry.insert(derived_root);
        }

        match (header.is_last, self.last_slice) {
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
        let shred_index = validated_shred.payload().shred_index;
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
        slice_shreds[*shred_index] = Some(validated_shred);

        if is_first_shred {
            return Ok(vec![BlockDataEvent::FirstShred]);
        }

        let mut events = Vec::new();
        match self.try_reconstruct_slice(slice_index, shredder) {
            ReconstructSliceResult::NoAction => {}
            ReconstructSliceResult::Error => return Err(AddShredError::InvalidShred),
            ReconstructSliceResult::Complete => {
                events.push(BlockDataEvent::SliceReconstructed(slice_index));
                match self.try_reconstruct_block() {
                    ReconstructBlockResult::NoAction => {}
                    ReconstructBlockResult::Error => return Err(AddShredError::InvalidShred),
                    ReconstructBlockResult::Complete(block_info, state_hash) => {
                        events.push(BlockDataEvent::BlockReady {
                            block_info,
                            state_hash,
                        });
                    }
                }
            }
        }
        Ok(events)
    }

    /// Reconstructs the slice if the blockstore contains enough shreds.
    ///
    /// For the last slice, strips the trailing [`STATE_HASH_SIZE`] bytes (the
    /// execution state hash appended by the proposer) from the slice data and
    /// stores it in [`Self::last_slice_state_hash`] for later use in
    /// [`Self::try_reconstruct_block`].
    fn try_reconstruct_slice(
        &mut self,
        index: SliceIndex,
        shredder: &mut RegularShredder,
    ) -> ReconstructSliceResult {
        if self.completed.is_some() {
            trace!("already have block for slot {}", self.slot);
            return ReconstructSliceResult::NoAction;
        }

        let entry = match self.slices.entry(index) {
            Entry::Occupied(_) => return ReconstructSliceResult::NoAction,
            Entry::Vacant(entry) => entry,
        };

        let slice_shreds = self.shreds.get_mut(&index).unwrap();
        let (mut reconstructed_slice, reconstructed_shreds) = match shredder.deshred(slice_shreds) {
            Ok(output) => output,
            Err(DeshredError::NotEnoughShreds) => return ReconstructSliceResult::NoAction,
            rest => {
                warn!("deshredding failed with {rest:?}");
                return ReconstructSliceResult::Error;
            }
        };
        if reconstructed_slice.parent.is_none() && reconstructed_slice.slice_index.is_first() {
            warn!(
                "reconstructed slice {} in slot {} expected to contain parent",
                index, self.slot
            );
            return ReconstructSliceResult::Error;
        }

        // For the last slice, extract and strip the execution state hash suffix.
        if reconstructed_slice.is_last {
            match reconstructed_slice.strip_state_hash_suffix() {
                Some(state_hash) => self.last_slice_state_hash = Some(state_hash),
                None => {
                    warn!(
                        "last slice {} in slot {} too short to contain state hash",
                        index, self.slot
                    );
                    return ReconstructSliceResult::Error;
                }
            }
        }

        entry.insert(reconstructed_slice);
        let mut reconstructed_shreds = reconstructed_shreds.map(Some);
        std::mem::swap(slice_shreds, &mut reconstructed_shreds);
        trace!("reconstructed slice {} in slot {}", index, self.slot);

        ReconstructSliceResult::Complete
    }

    /// Reconstructs the block if all slices are present.
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
        let Some(state_hash) = self.last_slice_state_hash.clone() else {
            // This should not happen: last_slice is set iff try_reconstruct_slice
            // ran for the last slice, which always sets last_slice_state_hash.
            warn!(
                "block complete but state hash missing in slot {}",
                self.slot
            );
            return ReconstructBlockResult::Error;
        };

        // calculate double-Merkle tree & block hash
        let merkle_roots = self.slices.values().map(|s| s.merkle_root());
        let tree = DoubleMerkleTree::new(merkle_roots);
        let block_hash = tree.get_root();
        self.double_merkle_tree = Some(tree);

        // reconstruct block header
        let first_slice = self.slices.get(&SliceIndex::first()).unwrap();
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
        self.completed = Some((block_hash, block));

        for slice_index in last_slice.until() {
            self.slices.remove(&slice_index);
        }

        ReconstructBlockResult::Complete(block_info, state_hash)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{DATA_SHREDS, ShredIndex, TOTAL_SHREDS};
    use crate::test_utils::create_random_block;
    use crate::types::Slice;

    fn handle_slice(
        block_data: &mut BlockData,
        slice: Slice,
        sk: &SecretKey,
    ) -> (Vec<BlockDataEvent>, Result<(), AddShredError>) {
        let mut shredder = RegularShredder::default();
        let pk = sk.to_pk();
        let shreds = shredder.shred(slice, sk).unwrap();
        let mut events = vec![];
        for shred in shreds {
            match block_data.add_shred(shred.into_shred(), pk, &mut shredder) {
                Ok(evs) => events.extend(evs),
                Err(AddShredError::Duplicate) => {}
                Err(err) => return (events, Err(err)),
            }
        }
        (events, Ok(()))
    }

    fn get_block_info_from_events(events: &[BlockDataEvent]) -> Option<&BlockInfo> {
        events.iter().find_map(|e| match e {
            BlockDataEvent::BlockReady { block_info, .. } => Some(block_info),
            _ => None,
        })
    }

    #[test]
    fn reconstruct_slice_and_shreds() {
        let sk = SecretKey::new(&mut rand::rng());
        let pk = sk.to_pk();
        let slot = Slot::new(123);

        let slices = create_random_block(slot, 1);
        let mut block_data = BlockData::new(slot);
        let mut shredder = RegularShredder::default();
        let shreds = shredder.shred(slices[0].clone(), &sk).unwrap();
        let mut events = vec![];
        for shred in shreds.into_iter().skip(TOTAL_SHREDS - DATA_SHREDS) {
            events.extend(
                block_data
                    .add_shred(shred.into_shred(), pk, &mut shredder)
                    .unwrap(),
            );
        }
        assert!(block_data.completed.is_some());

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

        // valid block reconstructs successfully
        let slices = create_random_block(slot, 1);
        let (events, res) =
            handle_slice(&mut BlockData::new(slices[0].slot), slices[0].clone(), &sk);
        let () = res.unwrap();
        assert_eq!(events.len(), 3); // FirstShred + SliceReconstructed + BlockReady
        assert!(matches!(events[0], BlockDataEvent::FirstShred));
        assert!(matches!(events[1], BlockDataEvent::SliceReconstructed(_)));
        assert!(get_block_info_from_events(&events).is_some());

        // block with missing parent does not reconstruct
        let mut slices = create_random_block(slot, 1);
        slices[0].parent = None;
        let (events, res) =
            handle_slice(&mut BlockData::new(slices[0].slot), slices[0].clone(), &sk);
        assert_eq!(res.unwrap_err(), AddShredError::InvalidShred);
        assert_eq!(events.len(), 1);
        assert!(matches!(events[0], BlockDataEvent::FirstShred));
    }

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
        // Block reconstruction failed, so no BlockReady event fired.
        // SliceReconstructed events may have been emitted for slices that decoded
        // successfully before the error was detected.
        assert!(
            !events
                .iter()
                .any(|e| matches!(e, BlockDataEvent::BlockReady { .. }))
        );
    }

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
        assert!(
            !events
                .iter()
                .any(|e| matches!(e, BlockDataEvent::BlockReady { .. }))
        );
    }

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

        let block_info = get_block_info_from_events(&events).expect("block should be ready");
        assert_eq!(block_info.parent, slice_1_parent);
    }
}
