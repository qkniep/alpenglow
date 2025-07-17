use std::collections::BTreeMap;

use log::{debug, trace, warn};

use crate::consensus::votor::VotorEvent;
use crate::crypto::signature::PublicKey;
use crate::crypto::{Hash, MerkleTree};
use crate::shredder::{self, RegularShredder, Shred, Shredder, Slice};
use crate::{Block, Slot};

use super::BlockInfo;

///
pub struct SlotBlockData {
    ///
    slot: Slot,
    /// Stores raw shreds per slice, indexed by slice index.
    pub(super) shreds: BTreeMap<usize, Vec<Shred>>,
    /// Stores so far reconstructed slices, indexed by slice index.
    pub(super) slices: BTreeMap<usize, Slice>,
    ///
    // repair_shreds: BTreeMap<(Hash, usize), Vec<Shred>>,
    ///
    // repair_slices: BTreeMap<(Hash, usize), Slice>,
    /// Stores actual fully reconstructed block data for all relevant blocks.
    pub(super) blocks: BTreeMap<Hash, Block>,
    /// Holds currently canonical block hash for a given slot number.
    pub(super) canonical: Option<Hash>,
    /// Holds hashes of alternative blocks for a given slot number.
    pub(super) alternatives: Vec<Hash>,
    /// Stores double-Merkle tree for each canonical block.
    pub(super) double_merkle_tree: Option<MerkleTree>,
    /// Stores last slice index for each slot.
    last_slice: Option<usize>,
    /// Set of slots for which conflicting shreds have been seen (leader equivocated).
    equivocated: bool,
    /// Cache of previously verified Merkle roots.
    merkle_root_cache: BTreeMap<usize, Hash>,
}

impl SlotBlockData {
    pub fn new(slot: Slot) -> Self {
        Self {
            slot,
            shreds: BTreeMap::new(),
            slices: BTreeMap::new(),
            blocks: BTreeMap::new(),
            canonical: None,
            alternatives: Vec::new(),
            double_merkle_tree: None,
            last_slice: None,
            equivocated: false,
            merkle_root_cache: BTreeMap::new(),
        }
    }

    pub fn add_shred(
        &mut self,
        shred: Shred,
        check_equivocation: bool,
        leader_pk: PublicKey,
    ) -> Option<VotorEvent> {
        assert_eq!(shred.payload().slot, self.slot);
        if check_equivocation && self.equivocated {
            debug!("recevied shred from equivocating leader, not adding to blockstore");
            return None;
        }
        let slice = shred.payload().slice_index;
        let index = shred.payload().index_in_slice;
        let is_last_slice = shred.payload().is_last_slice;
        let is_first_shred = self.shreds.is_empty();
        let slice_shreds = self.shreds.entry(slice).or_default();

        // check Merkle root and signature
        let cached_merkle_root = self.merkle_root_cache.get(&slice);
        if !shred.verify(&leader_pk, cached_merkle_root) {
            debug!("dropping invalid shred");
            return None;
        } else if cached_merkle_root.is_none() {
            self.merkle_root_cache.insert(slice, shred.merkle_root);
        } else if cached_merkle_root != Some(&shred.merkle_root) {
            if !self.equivocated {
                self.equivocated = true;
                warn!("shreds show leader equivocation in slot {}", self.slot);
            }
            if check_equivocation {
                return None;
            }
        }

        // store and handle this shred if and only if:
        //   - it is not yet stored in the blockstore
        //   - it is not (known to be) after the last slice
        let exists = slice_shreds.iter().any(|s| {
            s.payload().index_in_slice == index
                && shred.payload_type.is_data() == s.payload_type.is_data()
        });
        let after_last = self.last_slice.is_some_and(|last_slice| slice > last_slice);
        if exists || after_last {
            return None;
        }
        slice_shreds.push(shred);

        // store last slice index, delete later shreds
        if is_last_slice && self.last_slice.is_none() {
            self.last_slice = Some(slice);

            // delete shreds after last slice, if there are any
            let keys_to_delete: Vec<_> = self
                .shreds
                .range(&slice + 1..)
                .map(|(k, _)| k)
                .copied()
                .collect();
            for key in keys_to_delete {
                self.shreds.remove(&key);
            }
        }

        // maybe send first shred notification
        if is_first_shred {
            return Some(VotorEvent::FirstShred(self.slot));
        }

        // maybe reconstruct slice and block
        if self.try_reconstruct_slice(slice) {
            self.try_reconstruct_block()
                .map(|block_info| VotorEvent::Block {
                    slot: self.slot,
                    block_info,
                })
        } else {
            None
        }
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
        if self.canonical.is_some() {
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
        self.canonical = Some(block_hash);
        // TODO: reconstruct actual block content
        let block = Block {
            slot: self.slot,
            block_hash,
            parent: parent_slot,
            parent_hash,
            transactions: vec![],
        };
        let block_info = BlockInfo::from(&block);
        self.blocks.insert(block_hash, block);

        // clean up raw slices
        for slice_index in 0..=last_slice {
            self.slices.remove(&slice_index);
        }

        Some(block_info)
    }
}
