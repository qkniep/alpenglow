// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structure holding shreds, slices and blocks for a specific slot.
//!
//! Two nested containers organize a slot's data:
//! - [`SlotBlockData`] is the per-slot entry point.
//!   Holds at most one block from dissemination but may hold multiple from repair.
//!   Repaired blocks are kept separately in map keyed by [`BlockHash`].
//! - [`BlockData`] holds everything for a single block.
//!   It holds received shreds, the slices reconstructed from them,
//!   and the fully reconstructed block once all slices are present.
//!
//! Reconstruction is bottom-up:
//! 1. enough shreds in a slice reconstruct that slice, and
//! 2. enough slices (through the one marked last) reconstruct the block.
//!
//! Incoming shreds arrive already signature-verified (see [`ValidatedShred`]).
//! They come from one either of two paths:
//! - Dissemination shreds ([`SlotBlockData::add_shred_from_dissemination`])
//!   feed a single [`BlockData`] and are checked for leader equivocation.
//! - Repair shreds ([`SlotBlockData::add_shred_from_repair`])
//!   are filed under their block hash (which is known when initiating repair),
//!   so distinct blocks coexist without being treated as equivocation.

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use log::{debug, trace, warn};
use thiserror::Error;
use wincode::config::DefaultConfig;

use super::{BlockInfo, BlockstoreEvent};
use crate::crypto::merkle::{BlockHash, DoubleMerkleTree};
use crate::shredder::{
    DeshredError, MAX_DATA_PER_SLICE, RegularShredder, Shredder, SliceCommitment, TOTAL_SHREDS,
    ValidatedShred,
};
use crate::types::{ReconstructedSlice, SliceIndex, SlicePayload};
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

    /// Adds a shred receive via block dissemination in the corresponding spot.
    ///
    /// The shred must already have a verified leader signature (see [`ValidatedShred`]).
    /// Checks for leader equivocation against any previously stored shred for the slice.
    pub(super) fn add_shred_from_dissemination(
        &mut self,
        shred: ValidatedShred,
        shredder: &mut RegularShredder,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        debug_assert_eq!(shred.payload().header.slot, self.slot);
        if self.leader_misbehaved {
            debug!("received shred from misbehaving leader, not adding to blockstore");
            return Err(AddShredError::InvalidShred);
        }
        self.disseminated.add_shred(shred, shredder)
    }

    /// Adds a shred received via repair to the spot given by block hash.
    ///
    /// The shred must already have a verified leader signature (see [`ValidatedShred`]).
    /// Performs validity checks except for leader equivocation across blocks.
    pub(super) fn add_shred_from_repair(
        &mut self,
        hash: BlockHash,
        shred: ValidatedShred,
        shredder: &mut RegularShredder,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        debug_assert_eq!(shred.payload().header.slot, self.slot);
        let block_data = self
            .repaired
            .entry(hash)
            .or_insert_with(|| BlockData::new(self.slot));
        block_data.add_shred(shred, shredder)
    }

    /// Records that the leader was observed equivocating for this slot.
    ///
    /// Returns `true` iff this was the first time this method was called.
    pub(super) fn mark_leader_misbehaved(&mut self) -> bool {
        if self.leader_misbehaved {
            return false;
        }
        self.leader_misbehaved = true;
        true
    }

    /// Ingests a slice that the local node produced itself (as the leader).
    ///
    /// Unlike [`Self::add_shred_from_dissemination`] and [`Self::add_shred_from_repair`],
    /// the caller already holds all [`TOTAL_SHREDS`] freshly produced shreds
    /// and the decoded slice payload.
    /// No deshredding, Merkle verification or equivocation check are performed.
    ///
    /// Returns `(is_first_slice, completed_block)`.
    /// The first flag urges the caller to emit a [`BlockstoreEvent::FirstShred`],
    /// the second entry urges the caller to emit a [`BlockstoreEvent::Block`].
    pub(super) fn add_own_slice(
        &mut self,
        payload: SlicePayload,
        shreds: [ValidatedShred; TOTAL_SHREDS],
    ) -> (bool, Option<BlockInfo>) {
        self.disseminated.add_own_slice(payload, shreds)
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
    /// Cache of [`SliceCommitment`]s verified earlier.
    ///
    /// Lets [`ValidatedShred::try_new`] short-circuit verification for the same slice.
    /// This is also what allows us to detect leader equivocation.
    pub(super) commitment_cache: BTreeMap<SliceIndex, SliceCommitment>,
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
            commitment_cache: BTreeMap::new(),
        }
    }

    /// Add a shred to this block.
    ///
    ///
    fn add_shred(
        &mut self,
        shred: ValidatedShred,
        shredder: &mut RegularShredder,
    ) -> Result<Option<BlockstoreEvent>, AddShredError> {
        let header = &shred.payload().header;
        debug_assert_eq!(header.slot, self.slot);
        let slice_index = header.slice_index;
        let is_last = header.is_last;

        // first shred for a slice populates the commitment cache;
        // a later shred with a different valid commitment means the leader equivocated.
        match self.commitment_cache.entry(slice_index) {
            Entry::Occupied(entry) if entry.get() != &shred.commitment() => {
                return Err(AddShredError::Equivocation);
            }
            Entry::Occupied(_) => {}
            Entry::Vacant(entry) => {
                entry.insert(shred.commitment());
            }
        }

        match (is_last, self.last_slice) {
            (true, None) => self.mark_last_slice(slice_index),
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
        let shred_index = shred.payload().shred_index;
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
            return Ok(Some(BlockstoreEvent::FirstShred(self.slot)));
        }

        match self.try_reconstruct_slice(slice_index, shredder) {
            ReconstructSliceResult::NoAction => Ok(None),
            ReconstructSliceResult::Error => Err(AddShredError::InvalidShred),
            ReconstructSliceResult::Complete => match self.try_reconstruct_block() {
                ReconstructBlockResult::NoAction => Ok(None),
                ReconstructBlockResult::Error => Err(AddShredError::InvalidShred),
                ReconstructBlockResult::Complete(block_info) => Ok(Some(BlockstoreEvent::Block {
                    slot: self.slot,
                    block_info,
                })),
            },
        }
    }

    /// Marks `slice_index` as the block's last slice and prunes anything cached beyond it.
    fn mark_last_slice(&mut self, slice_index: SliceIndex) {
        debug_assert!(self.last_slice.is_none());
        self.last_slice = Some(slice_index);
        self.slices.retain(|&ind, _| ind <= slice_index);
        self.shreds.retain(|&ind, _| ind <= slice_index);
    }

    /// Ingests a slice that the local node produced itself (as the leader).
    fn add_own_slice(
        &mut self,
        payload: SlicePayload,
        shreds: [ValidatedShred; TOTAL_SHREDS],
    ) -> (bool, Option<BlockInfo>) {
        // Build the slice from the shreds so the two can't disagree — the
        // dissemination path likewise reconstructs its slice from shreds.
        let any_shred = &shreds[0];
        let slice =
            ReconstructedSlice::from_shreds(payload, any_shred, any_shred.slice_root().clone());
        debug_assert_eq!(slice.slot, self.slot);
        let slice_index = slice.slice_index;
        let is_first = self.shreds.is_empty();

        // Commitment is trusted: we built and signed these shreds ourselves,
        // and each slice is produced exactly once, so the entry is always vacant.
        self.commitment_cache
            .insert(slice_index, any_shred.commitment());

        // The leader produces each slice once, in order, and stops after the
        // last, so a last slice must never already be set. This subsumes the
        // dissemination path's per-arm last-slice checks (no re-marking, nothing
        // at or after the last slice).
        assert!(
            self.last_slice.is_none(),
            "own slice {slice_index:?} added after the last slice in slot {}",
            self.slot,
        );
        if slice.is_last {
            self.mark_last_slice(slice_index);
        }

        // store everything directly — no `deshred()` / RS decode
        self.shreds.insert(slice_index, shreds.map(Some));
        self.slices.insert(slice_index, slice);

        let block_info = match self.try_reconstruct_block() {
            ReconstructBlockResult::NoAction => None,
            ReconstructBlockResult::Complete(block_info) => Some(block_info),
            ReconstructBlockResult::Error => {
                // Our own block, built from data we serialized and signed, must
                // reconstruct. Reaching here means a producer-side logic bug,
                // not adversarial input, so there is no graceful recovery.
                unreachable!(
                    "leader produced a block that failed reconstruction: slot {}, slice {slice_index:?}",
                    self.slot,
                );
            }
        };
        (is_first, block_info)
    }

    /// Reconstructs the slice if the blockstore contains enough shreds.
    ///
    /// See [`ReconstructSliceResult`] for more info on what the function returns.
    #[hotpath::measure]
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

        let slice_shreds = self
            .shreds
            .get_mut(&index)
            .expect("caller must insert at least one shred before reconstructing");
        let (reconstructed_slice, reconstructed_shreds) = match shredder.deshred(slice_shreds) {
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
        let mut reconstructed_shreds = reconstructed_shreds.map(Some);
        std::mem::swap(slice_shreds, &mut reconstructed_shreds);
        trace!("reconstructed slice {} in slot {}", index, self.slot);

        ReconstructSliceResult::Complete
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
        let slice_roots = self.slices.values().map(|s| s.slice_root());
        let tree = DoubleMerkleTree::new(slice_roots);
        let block_hash = tree.get_root();
        self.double_merkle_tree = Some(tree);

        // reconstruct block header
        let first_slice = self
            .slices
            .get(&SliceIndex::first())
            .expect("all slices are present, including the first");
        let mut parent = first_slice
            .parent
            .clone()
            .expect("first slice contains a parent, validated in `try_reconstruct_slice`");
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

            // cap preallocation to the slice size limit (wincode has a 4 MiB default)
            let config =
                DefaultConfig::default().with_preallocation_size_limit::<MAX_DATA_PER_SLICE>();
            let mut txs = match wincode::config::deserialize_exact(&slice.data, config) {
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

    fn handle_slice(
        block_data: &mut BlockData,
        slice: Slice,
        sk: &SecretKey,
    ) -> (Vec<BlockstoreEvent>, Result<(), AddShredError>) {
        let mut shredder = RegularShredder::default();
        let shreds = shredder.shred(slice, sk).unwrap();
        let mut events = vec![];
        for shred in shreds {
            match block_data.add_shred(shred, &mut shredder) {
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
            if let Some(event) = block_data.add_shred(shred, &mut shredder).unwrap() {
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
