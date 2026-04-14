// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Slice`] and related data structures.

use std::ops::Deref;

use rand::prelude::*;
use wincode::config::DefaultConfig;
use wincode::{SchemaRead, SchemaWrite};

use crate::crypto::Hash;
use crate::crypto::merkle::{BlockHash, SliceRoot};
use crate::shredder::{MAX_DATA_PER_SLICE, ValidatedShred};
use crate::types::SliceIndex;
use crate::{BlockId, Slot};

/// Size in bytes of the execution state hash appended to the last slice's data.
///
/// The proposer appends this suffix before shredding; validators strip it before
/// deserializing transactions. It matches the serialized size of [`struct@Hash`].
pub(crate) const STATE_HASH_SIZE: usize = 32;

/// A slice is the unit of data between block and shred, before shredding.
///
/// It corresponds to a single batch of data that the leader is about to disseminate.
/// During shredding, a slice is turned into multiple shreds.
///
/// Deshredding results in a [`ReconstructedSlice`] instead.
/// It carries the Merkle root, which is only computable after shredding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slice {
    /// Slot number this slice is part of.
    pub slot: Slot,
    /// Index of the slice within its slot.
    pub slice_index: SliceIndex,
    /// Indicates whether this is the last slice in the slot.
    pub is_last: bool,
    /// If first slice in the block or parent changed due to optimistic handover,
    /// then indicates which block is the parent of the block this slice is part of.
    pub parent: Option<(Slot, BlockHash)>,
    /// Payload bytes.
    pub data: Vec<u8>,
}

impl Slice {
    /// Constructs a [`Slice`] from its component parts.
    pub(crate) fn from_parts(header: SliceHeader, payload: SlicePayload) -> Self {
        let SliceHeader {
            slot,
            slice_index,
            is_last,
        } = header;
        let SlicePayload { parent, data } = payload;
        Self {
            slot,
            slice_index,
            is_last,
            parent,
            data,
        }
    }

    /// Deconstructs a [`Slice`] into its components: [`SliceHeader`] and [`SlicePayload`].
    pub(crate) fn deconstruct(self) -> (SliceHeader, SlicePayload) {
        let Slice {
            slot,
            slice_index,
            is_last,
            parent,
            data,
        } = self;
        (
            SliceHeader {
                slot,
                slice_index,
                is_last,
            },
            SlicePayload { parent, data },
        )
    }

    /// Extracts the [`SliceHeader`] from a [`Slice`].
    pub(crate) fn to_header(&self) -> SliceHeader {
        SliceHeader {
            slot: self.slot,
            slice_index: self.slice_index,
            is_last: self.is_last,
        }
    }
}

/// A slice recovered after deshredding.
///
/// Unlike [`Slice`], this type carries the Merkle root over the slice's shreds,
/// which is only computable after shredding and is verified during deshredding.
///
/// All [`Slice`] fields and methods are accessible directly via [`Deref`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReconstructedSlice {
    inner: Slice,
    /// Merkle root hash over all shreds in this slice.
    merkle_root: SliceRoot,
}

impl ReconstructedSlice {
    /// Creates a [`ReconstructedSlice`] from its component parts.
    #[must_use]
    pub(crate) fn from_shreds(
        payload: SlicePayload,
        any_shred: &ValidatedShred,
        merkle_root: SliceRoot,
    ) -> Self {
        let header = any_shred.payload().header;
        Self {
            inner: Slice::from_parts(header, payload),
            merkle_root,
        }
    }

    /// Returns the Merkle root hash over all shreds in this slice.
    #[must_use]
    pub fn merkle_root(&self) -> &SliceRoot {
        &self.merkle_root
    }

    /// Strips the trailing [`STATE_HASH_SIZE`] bytes from the slice data and
    /// returns them as the execution state hash.
    ///
    /// Called during reconstruction of the last slice to separate the
    /// execution state hash (appended by the proposer) from transaction data.
    /// Returns `None` if the data is too short.
    pub(crate) fn strip_state_hash_suffix(&mut self) -> Option<Hash> {
        if self.inner.data.len() < STATE_HASH_SIZE {
            return None;
        }
        let split = self.inner.data.len() - STATE_HASH_SIZE;
        let hash: Hash = wincode::deserialize(&self.inner.data[split..]).ok()?;
        self.inner.data.truncate(split);
        Some(hash)
    }
}

impl Deref for ReconstructedSlice {
    type Target = Slice;

    fn deref(&self) -> &Slice {
        &self.inner
    }
}

/// Struct to hold all the header payload of a [`Slice`].
///
/// This information is included in each shred after shredding.
#[derive(Clone, Copy, Debug, SchemaRead, SchemaWrite)]
pub(crate) struct SliceHeader {
    /// Same as [`Slice::slot`].
    pub(crate) slot: Slot,
    /// Same as [`Slice::slice_index`].
    pub(crate) slice_index: SliceIndex,
    /// Same as [`Slice::is_last`].
    pub(crate) is_last: bool,
}

/// Struct to hold all the actual payload of a [`Slice`].
///
/// This is what actually gets "shredded" into different shreds.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub(crate) struct SlicePayload {
    /// Same as [`Slice::parent`].
    pub(crate) parent: Option<(Slot, BlockHash)>,
    /// Same as [`Slice::data`].
    pub(crate) data: Vec<u8>,
}

impl SlicePayload {
    /// Constructs a new [`SlicePayload`] from its component parts.
    pub(crate) fn new(parent: Option<(Slot, BlockHash)>, data: Vec<u8>) -> Self {
        Self { parent, data }
    }

    /// Serializes the payload into bytes.
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        wincode::serialize(self).unwrap()
    }
}

impl From<SlicePayload> for Vec<u8> {
    fn from(payload: SlicePayload) -> Self {
        wincode::serialize(&payload).unwrap()
    }
}

impl From<&[u8]> for SlicePayload {
    fn from(payload: &[u8]) -> Self {
        assert!(
            payload.len() <= MAX_DATA_PER_SLICE,
            "payload.len()={} {MAX_DATA_PER_SLICE}",
            payload.len()
        );
        wincode::deserialize(payload).unwrap()
    }
}

/// Creates a [`SlicePayload`] with a random payload of desired size (in bytes).
///
/// The payload does not contain valid transactions.
/// This function should only be used for testing and benchmarking.
//
// XXX: This is only used in test and benchmarking code.
// Ensure it is only compiled when we are testing or benchmarking.
pub(crate) fn create_slice_payload_with_invalid_txs(
    parent: Option<BlockId>,
    desired_size: usize,
) -> SlicePayload {
    let parent_bytes =
        <Option<BlockId> as wincode::SchemaWrite<DefaultConfig>>::size_of(&parent).unwrap();
    // 8 bytes for data length (usize), since wincode uses fixed-length integer encoding
    let data_len_bytes = 8;

    let size = desired_size
        .checked_sub(parent_bytes + data_len_bytes)
        .unwrap();
    let mut data = vec![0; size];
    let mut rng = rand::rng();
    rng.fill_bytes(&mut data);

    SlicePayload { parent, data }
}

/// Creates a [`Slice`] with a random payload of desired size (in bytes).
///
/// The slice does not contain valid transactions.
/// This function should only be used for testing and benchmarking.
//
// XXX: This is only used in test and benchmarking code.  Ensure it is only compiled when we are testing or benchmarking.
pub fn create_slice_with_invalid_txs(desired_size: usize) -> Slice {
    let payload = create_slice_payload_with_invalid_txs(None, desired_size);
    let header = SliceHeader {
        slot: Slot::new(0),
        slice_index: SliceIndex::first(),
        is_last: true,
    };
    Slice::from_parts(header, payload)
}
