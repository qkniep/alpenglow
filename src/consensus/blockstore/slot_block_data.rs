// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding shreds, slices and blocks for a specific slot.
//!
//!

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use log::{debug, trace, warn};
use thiserror::Error;

use super::BlockInfo;
use crate::consensus::votor::VotorEvent;
use crate::crypto::signature::PublicKey;
use crate::crypto::{Hash, MerkleTree};
use crate::network::BINCODE_CONFIG;
use crate::shredder::{
    DeshredError, RegularShredder, Shred, ShredVerifyError, Shredder, ValidatedShred,
};
use crate::types::{Slice, SliceIndex};
use crate::{Block, Slot};

/// Errors that may be encountered when adding a shred.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
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
            ShredVerifyError::InvalidProof | ShredVerifyError::InvalidSignature => {
                AddShredError::InvalidSignature
            }
            ShredVerifyError::Equivocation => AddShredError::Equivocation,
        }
    }
}

/// Holds all data corresponding to any blocks for a single slot.
pub struct SlotBlockData {
    /// Slot number this data corresponds to.
    slot: Slot,
    /// Spot for storing the block that was received via block dissemination.
    pub(super) disseminated: BlockData,
    /// Spot for storing blocks that might later be received via repair.
    pub(super) repaired: BTreeMap<Hash, BlockData>,
    /// Whether conflicting shreds have been seen for this slot.
    pub(super) equivocated: bool,
}

impl SlotBlockData {
    /// Creates a new empty structure for a slot's block data.
    pub fn new(slot: Slot) -> Self {
        Self {
            slot,
            disseminated: BlockData::new(slot),
            repaired: BTreeMap::new(),
            equivocated: false,
        }
    }

    /// Adds a shred receive via block dissemination in the corresponding spot.
    ///
    /// Performs the necessary validity checks, including checks for leader equivocation.
    pub fn add_shred_from_disseminator(
        &mut self,
        shred: Shred,
        leader_pk: PublicKey,
    ) -> Result<Option<VotorEvent>, AddShredError> {
        assert_eq!(shred.payload().header.slot, self.slot);
        if self.equivocated {
            debug!("recevied shred from equivocating leader, not adding to blockstore");
            return Err(AddShredError::Equivocation);
        }
        self.disseminated
            .add_shred(shred, leader_pk)
            .inspect_err(|err| {
                if matches!(err, AddShredError::Equivocation) {
                    self.equivocated = true;
                }
            })
    }

    /// Adds a shred received via repair to the spot given by block hash.
    ///
    /// Performs the necessary validity checks, all but leader equivocation.
    pub fn add_shred_from_repair(
        &mut self,
        hash: Hash,
        shred: Shred,
        leader_pk: PublicKey,
    ) -> Result<Option<VotorEvent>, AddShredError> {
        assert_eq!(shred.payload().header.slot, self.slot);
        let block_data = self
            .repaired
            .entry(hash)
            .or_insert_with(|| BlockData::new(self.slot));
        block_data.add_shred(shred, leader_pk).inspect_err(|err| {
            if matches!(err, AddShredError::Equivocation) {
                self.equivocated = true;
            }
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
    /// [`BlockInfo`] describing the block is returned.
    Complete(BlockInfo),
}

pub(super) struct CompletedBlockData {
    double_merkle_tree: MerkleTree,
    shreds: BTreeMap<SliceIndex, Vec<ValidatedShred>>,
    pub(super) hash: Hash,
    block: Block,
}

struct InProgressBlockData {
    shreds: BTreeMap<SliceIndex, Vec<ValidatedShred>>,
    last_slice: Option<SliceIndex>,
    merkle_root_cache: BTreeMap<SliceIndex, Hash>,
}

pub(super) enum BlockDataStatus {
    Completed(CompletedBlockData),
    InProgress(InProgressBlockData),
}

/// Holds all data corresponding to a single block.
pub(super) struct BlockData {
    slot: Slot,
    slices: BTreeMap<SliceIndex, Slice>,
    pub(super) status: BlockDataStatus,
}

impl BlockData {
    /// Create a new spot for storing data of a single block.
    pub fn new(slot: Slot) -> Self {
        let in_progress = InProgressBlockData {
            shreds: BTreeMap::new(),
            last_slice: None,
            merkle_root_cache: BTreeMap::new(),
        };
        Self {
            slot,
            slices: BTreeMap::new(),
            status: BlockDataStatus::InProgress(in_progress),
        }
    }

    fn add_shred(
        &mut self,
        shred: Shred,
        leader_pk: PublicKey,
    ) -> Result<Option<VotorEvent>, AddShredError> {
        assert!(shred.payload().header.slot == self.slot);
        match &mut self.status {
            BlockDataStatus::Completed(_) => Err(AddShredError::Duplicate),
            BlockDataStatus::InProgress(in_progress) => {
                let slice_index = shred.payload().header.slice_index;
                let cached_merkle_root = in_progress.merkle_root_cache.entry(slice_index);
                let validated_shred =
                    ValidatedShred::try_new(shred, cached_merkle_root, &leader_pk)?;
                self.add_validated_shred(validated_shred)
            }
        }
    }

    fn add_validated_shred(
        &mut self,
        validated_shred: ValidatedShred,
    ) -> Result<Option<VotorEvent>, AddShredError> {
        let in_progress = match &mut self.status {
            BlockDataStatus::Completed(_) => return Err(AddShredError::Duplicate),
            BlockDataStatus::InProgress(p) => p,
        };
        let header = &validated_shred.payload().header;
        assert!(header.slot == self.slot);
        let slice_index = header.slice_index;

        match (header.is_last, in_progress.last_slice) {
            (true, None) => {
                in_progress.last_slice = Some(slice_index);
                self.slices.retain(|&ind, _| ind <= slice_index);
                in_progress.shreds.retain(|&ind, _| ind <= slice_index);
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

        let is_first_shred = in_progress.shreds.is_empty();
        let slice_shreds = {
            let shred_index = validated_shred.payload().index_in_slice;
            let slice_shreds = in_progress.shreds.entry(slice_index).or_default();
            let exists = slice_shreds
                .iter()
                .any(|s| s.payload().index_in_slice == shred_index);
            if exists {
                debug!(
                    "dropping duplicate shred {}-{} in slot {}",
                    slice_index, shred_index, self.slot
                );
                return Err(AddShredError::Duplicate);
            }
            slice_shreds
        };

        slice_shreds.push(validated_shred);

        if is_first_shred {
            return Ok(Some(VotorEvent::FirstShred(self.slot)));
        }

        match self.try_reconstruct_slice(slice_index) {
            ReconstructSliceResult::NoAction => Ok(None),
            ReconstructSliceResult::Error => Err(AddShredError::InvalidShred),
            ReconstructSliceResult::Complete => match self.try_reconstruct_block() {
                ReconstructBlockResult::NoAction => Ok(None),
                ReconstructBlockResult::Error => Err(AddShredError::InvalidShred),
                ReconstructBlockResult::Complete(block_info) => Ok(Some(VotorEvent::Block {
                    slot: self.slot,
                    block_info,
                })),
            },
        }
    }

    /// Reconstructs the slice if the blockstore contains enough shreds.
    ///
    /// See [`ReconstructSliceResult`] for more info on what the function returns.
    fn try_reconstruct_slice(&mut self, index: SliceIndex) -> ReconstructSliceResult {
        let in_progress = match &mut self.status {
            BlockDataStatus::Completed(_) => return ReconstructSliceResult::NoAction,
            BlockDataStatus::InProgress(p) => p,
        };

        let entry = match self.slices.entry(index) {
            Entry::Occupied(_) => return ReconstructSliceResult::NoAction,
            Entry::Vacant(entry) => entry,
        };

        // assuming caller has inserted at least one valid shred so unwrap() should be safe
        let slice_shreds = in_progress.shreds.get_mut(&index).unwrap();
        let (reconstructed_slice, mut reconstructed_shreds) =
            match RegularShredder::deshred(slice_shreds) {
                Ok(output) => output,
                Err(DeshredError::NotEnoughShreds) => return ReconstructSliceResult::NoAction,
                rest => {
                    warn!("deshreding failed with {rest:?}");
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

        // insert reconstructed slice and shreds
        entry.insert(reconstructed_slice);
        std::mem::swap(slice_shreds, &mut reconstructed_shreds);
        trace!("reconstructed slice {} in slot {}", index, self.slot);

        ReconstructSliceResult::Complete
    }

    /// Reconstructs the block if the blockstore contains all slices.
    ///
    /// See [`ReconstructBlockResult`] for more info on what the function returns.
    fn try_reconstruct_block(&mut self) -> ReconstructBlockResult {
        let in_progress = match &mut self.status {
            BlockDataStatus::Completed(_) => return ReconstructBlockResult::NoAction,
            BlockDataStatus::InProgress(p) => p,
        };
        let Some(last_slice) = in_progress.last_slice else {
            return ReconstructBlockResult::NoAction;
        };
        if self.slices.len() != last_slice.inner() + 1 {
            trace!("don't have all slices for slot {} yet", self.slot);
            return ReconstructBlockResult::NoAction;
        }

        // calculate double-Merkle tree & block hash
        let merkle_roots = self
            .slices
            .values()
            .map(|s| s.merkle_root.as_ref().unwrap())
            .collect::<Vec<_>>();
        let tree = MerkleTree::new(&merkle_roots);
        let block_hash = tree.get_root();

        // reconstruct block header
        let first_slice = self.slices.get(&SliceIndex::first()).unwrap();
        // based on the logic in `try_reconstruct_slice`, first_slice should be valid i.e. it must contain a parent.
        let mut parent = first_slice.parent.unwrap();
        let mut parent_switched = false;

        let mut transactions = vec![];
        for (ind, slice) in &self.slices {
            // handle optimistic handover
            if !ind.is_first()
                && let Some(new_parent) = slice.parent
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

            let (mut txs, bytes_read) =
                match bincode::serde::decode_from_slice(&slice.data, BINCODE_CONFIG) {
                    Ok(r) => r,
                    Err(err) => {
                        warn!("decoding slice {ind} failed with {err:?}");
                        return ReconstructBlockResult::Error;
                    }
                };
            if bytes_read != slice.data.len() {
                warn!(
                    "decoding slice {}: read {} but actual length is {}",
                    ind,
                    bytes_read,
                    slice.data.len()
                );
                return ReconstructBlockResult::Error;
            }
            transactions.append(&mut txs);
        }

        let block = Block {
            slot: self.slot,
            block_hash,
            parent: parent.0,
            parent_hash: parent.1,
            transactions,
        };
        let block_info = BlockInfo::from(&block);
        self.status = BlockDataStatus::Completed(CompletedBlockData {
            double_merkle_tree: tree,
            // XXX
            shreds: in_progress.shreds.clone(),
            hash: block_hash,
            block,
        });

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
    use crate::shredder::{DATA_SHREDS, TOTAL_SHREDS};
    use crate::test_utils::{assert_votor_events_match, create_random_block};

    fn handle_slice(
        block_data: &mut BlockData,
        slice: Slice,
        sk: &SecretKey,
    ) -> (Vec<VotorEvent>, Result<(), AddShredError>) {
        let pk = sk.to_pk();
        let shreds = RegularShredder::shred(slice, sk).unwrap();
        let mut events = vec![];
        for shred in shreds {
            match block_data.add_shred(shred.into_shred(), pk) {
                Ok(Some(event)) => {
                    events.push(event);
                }
                Ok(None) | Err(AddShredError::Duplicate) => (),
                Err(err) => return (events, Err(err)),
            }
        }
        (events, Ok(()))
    }

    fn get_block_hash_from_votor_event(event: &VotorEvent) -> Hash {
        match event {
            VotorEvent::Block {
                slot: _,
                block_info: BlockInfo { hash, parent: _ },
            } => *hash,
            _ => panic!(),
        }
    }

    #[test]
    fn reconstruct_slice_and_shreds() {
        let sk = SecretKey::new(&mut rand::rng());
        let pk = sk.to_pk();
        let slot = Slot::new(123);

        // manage to construct block from just enough shreds
        let slices = create_random_block(slot, 1);
        let mut block_data = BlockData::new(slot);
        let shreds = RegularShredder::shred(slices[0].clone(), &sk).unwrap();
        let mut events = vec![];
        for shred in shreds.into_iter().skip(TOTAL_SHREDS - DATA_SHREDS) {
            if let Some(event) = block_data.add_shred(shred.into_shred(), pk).unwrap() {
                events.push(event);
            }
        }
        assert!(block_data.completed.is_some());

        // all shreds should have been reconstructed
        let slice_shreds = block_data.shreds.get(&SliceIndex::first()).unwrap();
        assert_eq!(slice_shreds.len(), TOTAL_SHREDS);
        for shred_index in 0..TOTAL_SHREDS {
            assert!(
                slice_shreds
                    .iter()
                    .any(|s| s.payload().index_in_slice == shred_index)
            );
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
        let first_shred_event = VotorEvent::FirstShred(slot);
        assert_votor_events_match(events[0].clone(), first_shred_event);
        let hash = get_block_hash_from_votor_event(&events[1]);
        let block_event = VotorEvent::Block {
            slot,
            block_info: BlockInfo {
                hash,
                parent: slices[0].parent.unwrap(),
            },
        };
        assert_votor_events_match(events[1].clone(), block_event);

        // do not construct a valid block when slice is invalid
        let mut slices = create_random_block(slot, 1);
        slices[0].parent = None;
        let (events, res) =
            handle_slice(&mut BlockData::new(slices[0].slot), slices[0].clone(), &sk);
        assert_eq!(res.unwrap_err(), AddShredError::InvalidShred);
        assert_eq!(events.len(), 1);
        let first_shred_event = VotorEvent::FirstShred(slot);
        assert_votor_events_match(events[0].clone(), first_shred_event);
    }

    // If a subsequent slice switches parent to the original, the block is not reconstructed.
    #[test]
    fn reconstruct_block_optimistic_handover_duplicate_parent() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);
        let mut slices = create_random_block(slot, 3);
        slices[2].parent = slices[0].parent;

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
            VotorEvent::FirstShred(s) => assert_eq!(slot, s),
            _ => panic!(),
        }
    }

    // Two switches of parents do not reconstruct block.
    #[test]
    fn reconstruct_block_optimistic_handover_two_switches() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);
        let mut slices = create_random_block(slot, 3);
        let parent = slices[0].parent.unwrap();
        let slice_1_parent = (parent.0.next(), parent.1);
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
            VotorEvent::FirstShred(s) => assert_eq!(slot, s),
            _ => panic!(),
        }
    }

    // Optimistic handover works.
    #[test]
    fn reconstruct_block_optimistic_handover_works() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);
        let mut slices = create_random_block(slot, 3);
        let parent = slices[0].parent.unwrap();
        let slice_1_parent = (parent.0.next(), parent.1);
        assert!(slice_1_parent.0 < slot);
        slices[1].parent = Some(slice_1_parent);

        let mut block_data = BlockData::new(slot);
        let mut events = vec![];
        for slice in slices {
            let (mut evs, res) = handle_slice(&mut block_data, slice, &sk);
            events.append(&mut evs);
            let () = res.unwrap();
        }
        assert_eq!(events.len(), 2);
        match events[0] {
            VotorEvent::FirstShred(s) => assert_eq!(slot, s),
            _ => panic!(),
        }
        match events[1] {
            VotorEvent::Block {
                slot: ret_slot,
                block_info,
            } => {
                assert_eq!(ret_slot, slot);
                assert_eq!(block_info.parent, slice_1_parent);
            }
            _ => panic!(),
        }
    }
}
