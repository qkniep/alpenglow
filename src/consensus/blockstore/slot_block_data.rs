// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding shreds, slices and blocks for a specific slot.
//!
//!

use std::collections::BTreeMap;

use log::{debug, trace, warn};
use thiserror::Error;

use crate::consensus::votor::VotorEvent;
use crate::crypto::signature::PublicKey;
use crate::crypto::{Hash, MerkleTree};
use crate::shredder::{self, RegularShredder, Shred, Shredder, Slice};
use crate::{Block, Slot};

use super::BlockInfo;

/// Errors that may be encountered when adding a shred.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum AddShredError {
    #[error("Shred has invalid signature")]
    InvalidSignature,
    #[error("Shred is already stored")]
    Duplicate,
    #[error("Shred shows leader equivocation")]
    Equivocation,
    #[error("Shred is after slice marked as last")]
    AfterLastSlice,
}

/// Holds all data corresponding to any blocks for a single slot.
pub struct SlotBlockData {
    /// Slot number this data corresponds to.
    slot: Slot,
    /// Spot for storing the block that was received via block dissemination.
    pub(super) canonical: BlockData,
    /// Spot for storing alternative blocks that might later be received via repair.
    pub(super) alternatives: BTreeMap<Hash, BlockData>,
    /// Whether conflicting shreds have been seen for this slot.
    pub(super) equivocated: bool,
}

/// Holds all data corresponding to a single block.
pub struct BlockData {
    /// Slot number this block is in.
    slot: Slot,
    /// Potentially completely restored block.
    pub(super) completed: Option<(Hash, Block)>,
    /// Any shreds of this block stored so far, indexed by slice index.
    pub(super) shreds: BTreeMap<usize, Vec<Shred>>,
    /// Any already reconstructed slices of this block.
    pub(super) slices: BTreeMap<usize, Slice>,
    /// Index of the slice marked as last, if any.
    pub(super) last_slice: Option<usize>,
    /// Double merkle tree of this block, only known if block has been reconstructed.
    pub(super) double_merkle_tree: Option<MerkleTree>,
    /// Cache of Merkle roots for which the leader signature has been verified.
    pub(super) merkle_root_cache: BTreeMap<usize, Hash>,
}

impl SlotBlockData {
    /// Creates a new empty structure for a slot's block data.
    pub fn new(slot: Slot) -> Self {
        Self {
            slot,
            canonical: BlockData::new(slot),
            alternatives: BTreeMap::new(),
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
        assert_eq!(shred.payload().slot, self.slot);
        if self.equivocated {
            debug!("recevied shred from equivocating leader, not adding to blockstore");
            return Err(AddShredError::Equivocation);
        }
        let add_shred_result = self.canonical.check_shred_to_add(&shred, true, leader_pk);
        if matches!(add_shred_result, Err(AddShredError::Equivocation)) {
            self.equivocated = true;
        }
        add_shred_result?;
        Ok(self.canonical.add_valid_shred(shred))
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
        assert_eq!(shred.payload().slot, self.slot);
        let block_data = self
            .alternatives
            .entry(hash)
            .or_insert_with(|| BlockData::new(self.slot));
        match block_data.check_shred_to_add(&shred, true, leader_pk) {
            Ok(()) => Ok(self.canonical.add_valid_shred(shred)),
            Err(err) => {
                if let AddShredError::Equivocation = &err {
                    self.equivocated = true;
                }
                Err(err)
            }
        }
    }
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
        }
    }

    /// Adds a new valid shred to the block.
    ///
    /// Assumes that the shred is valid, performs no more validity checks.
    ///
    /// Returns:
    /// - `Some(VotorEvent::FirstShred)` if this was the first shred of this block,
    /// - `Some(VotorEvent::Block)` if the block was successfully reconstructed,
    /// - `None` otherwise.
    pub fn add_valid_shred(&mut self, shred: Shred) -> Option<VotorEvent> {
        let slice_index = shred.payload().slice_index;
        let is_last_slice = shred.payload().is_last_slice;
        let is_first_shred = self.shreds.is_empty();
        self.shreds.entry(slice_index).or_default().push(shred);

        // store last slice index, delete everything after last slice
        if is_last_slice && self.last_slice.is_none() {
            self.last_slice = Some(slice_index);
            self.slices.split_off(&(slice_index + 1));
            self.shreds.split_off(&(slice_index + 1));
        }

        // maybe send first shred notification
        if is_first_shred {
            return Some(VotorEvent::FirstShred(self.slot));
        }

        // maybe reconstruct slice and block
        if self.try_reconstruct_slice(slice_index) {
            self.try_reconstruct_block()
                .map(|block_info| VotorEvent::Block {
                    slot: self.slot,
                    block_info,
                })
        } else {
            None
        }
    }

    fn check_shred_to_add(
        &mut self,
        shred: &Shred,
        check_equivocation: bool,
        leader_pk: PublicKey,
    ) -> Result<(), AddShredError> {
        let slice_index = shred.payload().slice_index;
        let shred_index = shred.payload().index_in_slice;
        let slice_shreds = self.shreds.entry(slice_index).or_default();

        // check Merkle root and signature
        let cached_merkle_root = self.merkle_root_cache.get(&slice_index);
        if !shred.verify(&leader_pk, cached_merkle_root) {
            debug!("dropping invalid shred");
            return Err(AddShredError::InvalidSignature);
        } else if cached_merkle_root.is_none() {
            self.merkle_root_cache
                .insert(slice_index, shred.merkle_root);
        } else if check_equivocation && cached_merkle_root != Some(&shred.merkle_root) {
            warn!("shreds show leader equivocation in slot {}", self.slot);
            return Err(AddShredError::Equivocation);
        }

        // store and handle this shred only if it is not yet stored in the blockstore
        let exists = slice_shreds.iter().any(|s| {
            s.payload().index_in_slice == shred_index
                && shred.payload_type.is_data() == s.payload_type.is_data()
        });
        if exists {
            return Err(AddShredError::Duplicate);
        }

        // store and handle this shred only if it is not (known to be) after the last slice
        if self.last_slice.is_some_and(|l| slice_index > l) {
            return Err(AddShredError::AfterLastSlice);
        }

        Ok(())
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
    fn try_reconstruct_block(&mut self) -> Option<BlockInfo> {
        if self.completed.is_some() {
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
        // TODO: reconstruct actual block content
        let block = Block {
            slot: self.slot,
            block_hash,
            parent: parent_slot,
            parent_hash,
            transactions: vec![],
        };
        let block_info = BlockInfo::from(&block);
        self.completed = Some((block_hash, block));

        // clean up raw slices
        for slice_index in 0..=last_slice {
            self.slices.remove(&slice_index);
        }

        Some(block_info)
    }
}
