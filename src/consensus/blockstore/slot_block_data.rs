// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding shreds, slices and blocks for a specific slot.
//!
//!

use std::collections::BTreeMap;

use log::{debug, trace, warn};
use thiserror::Error;

use super::BlockInfo;
use crate::consensus::votor::VotorEvent;
use crate::crypto::signature::PublicKey;
use crate::crypto::{Hash, MerkleTree};
use crate::shredder::{DeshredError, RegularShredder, Shred, Shredder};
use crate::types::{Slice, SliceIndex};
use crate::{Block, Slot};

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
        assert_eq!(shred.payload().header.slot, self.slot);
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
        assert_eq!(shred.payload().header.slot, self.slot);
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

/// Holds all data corresponding to a single block.
pub struct BlockData {
    /// Slot number this block is in.
    slot: Slot,
    /// Potentially completely restored block.
    pub(super) completed: Option<(Hash, Block)>,
    /// Any shreds of this block stored so far, indexed by slice index.
    pub(super) shreds: BTreeMap<SliceIndex, Vec<Shred>>,
    /// Any already reconstructed slices of this block.
    pub(super) slices: BTreeMap<SliceIndex, Slice>,
    /// Index of the slice marked as last, if any.
    pub(super) last_slice: Option<SliceIndex>,
    /// Double merkle tree of this block, only known if block has been reconstructed.
    pub(super) double_merkle_tree: Option<MerkleTree>,
    /// Cache of Merkle roots for which the leader signature has been verified.
    pub(super) merkle_root_cache: BTreeMap<SliceIndex, Hash>,
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
        let slice_index = shred.payload().header.slice_index;
        let is_last_slice = shred.payload().header.is_last;
        let is_first_shred = self.shreds.is_empty();
        self.shreds.entry(slice_index).or_default().push(shred);

        // store last slice index, delete everything after last slice
        if is_last_slice && self.last_slice.is_none() {
            self.last_slice = Some(slice_index);
            self.slices.retain(|&ind, _| ind <= slice_index);
            self.shreds.retain(|&ind, _| ind <= slice_index);
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
        let slice_index = shred.payload().header.slice_index;
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
    fn try_reconstruct_slice(&mut self, slice: SliceIndex) -> bool {
        let slice_shreds = self.shreds.get(&slice).unwrap();
        if self.slices.contains_key(&slice) {
            return false;
        }
        let reconstructed_slice = match RegularShredder::deshred(slice_shreds) {
            Ok(s) => s,
            Err(DeshredError::NotEnoughShreds) => return false,
            rest => {
                warn!("deshreding failed with {rest:?}");
                return false;
            }
        };
        if reconstructed_slice.parent.is_none() && reconstructed_slice.slice_index.is_first() {
            warn!(
                "reconstructed slice {} in slot {} expected to contain parent",
                slice, self.slot
            );
            return false;
        }
        self.slices.insert(slice, reconstructed_slice);
        trace!("reconstructed slice {} in slot {}", slice, self.slot);
        true
    }

    /// Reconstructs the block if the blockstore contains all slices.
    ///
    /// Returns `Some(block_info)` if a block was reconstructed, `None` otherwise.
    /// In the `Some`-case, `block_info` is the [`BlockInfo`] of the reconstructed block.
    fn try_reconstruct_block(&mut self) -> Option<BlockInfo> {
        if self.completed.is_some() {
            trace!("already have block for slot {}", self.slot);
            return None;
        }
        let last_slice = self.last_slice?;
        if self.slices.len() != last_slice.inner() + 1 {
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
                    return None;
                }
                if parent_switched {
                    warn!("parent switched more than once");
                    return None;
                }
                parent_switched = true;
                parent = new_parent;
            }

            let (mut txs, bytes_read) =
                match bincode::serde::decode_from_slice(&slice.data, bincode::config::standard()) {
                    Ok(r) => r,
                    Err(err) => {
                        warn!("decoding slice {ind} failed with {err:?}");
                        return None;
                    }
                };
            if bytes_read != slice.data.len() {
                warn!(
                    "decoding slice {}: read {} but actual length is {}",
                    ind,
                    bytes_read,
                    slice.data.len()
                );
                return None;
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
        self.completed = Some((block_hash, block));

        // clean up raw slices
        for slice_index in last_slice.until() {
            self.slices.remove(&slice_index);
        }

        Some(block_info)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::signature::SecretKey;
    use crate::test_utils::{assert_votor_events_match, create_random_block};

    fn handle_slice(slice: Slice, sk: &SecretKey) -> Vec<VotorEvent> {
        let mut block_data = BlockData::new(slice.slot);
        let shreds = RegularShredder::shred(slice, sk).unwrap();
        let mut events = vec![];
        for shred in shreds {
            if let Some(event) = block_data.add_valid_shred(shred) {
                events.push(event);
            }
        }
        events
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
    fn reconstruct_slice_invalid_parent() {
        let sk = SecretKey::new(&mut rand::rng());
        let slot = Slot::new(123);

        // manage to construct a valid block.
        let slices = create_random_block(slot, 1);
        let events = handle_slice(slices[0].clone(), &sk);
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

        // do not construct a valid block when slice is invalid.
        let mut slices = create_random_block(slot, 1);
        slices[0].parent = None;
        let events = handle_slice(slices[0].clone(), &sk);
        assert_eq!(events.len(), 1);
        let first_shred_event = VotorEvent::FirstShred(slot);
        assert_votor_events_match(events[0].clone(), first_shred_event);
    }
}
