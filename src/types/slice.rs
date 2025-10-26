// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Slice`] and related data structures.

use std::mem::MaybeUninit;

use rand::{RngCore, rng};
use wincode::{SchemaRead, SchemaWrite};

use crate::Slot;
use crate::crypto::Hash;
use crate::crypto::merkle::{BlockHash, SliceRoot};
use crate::shredder::{MAX_DATA_PER_SLICE, ValidatedShred};
use crate::types::SliceIndex;

/// A slice is the unit of data between block and shred.
///
/// It corresponds to a single batch of data that is disseminated by the leader.
/// During shredding, a slice is turned into multiple shreds.
/// During deshredding, multiple shreds are turned into a slice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slice {
    /// Slot number this slice is part of.
    pub slot: Slot,
    /// Index of the slice within its slot.
    pub slice_index: SliceIndex,
    /// Indicates whether this is the last slice in the slot.
    pub is_last: bool,
    /// Merkle root hash over all shreds in this slice.
    pub merkle_root: Option<SliceRoot>,
    /// If first slice in the block or parent changed due to optimistic handover,
    /// then indicates which block is the parent of the block this slice is part of.
    pub parent: Option<(Slot, BlockHash)>,
    /// Payload bytes.
    pub data: Vec<u8>,
}

impl Slice {
    /// Constructs a [`Slice`] from its component parts.
    pub(crate) fn from_parts(
        header: SliceHeader,
        payload: SlicePayload,
        merkle_root: Option<SliceRoot>,
    ) -> Self {
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
            merkle_root,
            parent,
            data,
        }
    }

    /// Creates a [`Slice`] from raw payload bytes and the metadata extracted from a shred.
    #[must_use]
    pub(crate) fn from_shreds(payload: SlicePayload, any_shred: &ValidatedShred) -> Self {
        let header = any_shred.payload().header.clone();
        let merkle_root = Some(any_shred.merkle_root.clone());
        Self::from_parts(header, payload, merkle_root)
    }

    /// Deconstructs a [`Slice`] into its components: [`SliceHeader`] and [`SlicePayload`].
    pub(crate) fn deconstruct(self) -> (SliceHeader, SlicePayload) {
        let Slice {
            slot,
            slice_index,
            is_last,
            merkle_root: _,
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

/// Struct to hold all the header payload of a [`Slice`].
///
/// This information is included in each shred after shredding.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
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
    pub(crate) parent: Option<(Slot, BlockHash)>,
    pub(crate) data: Vec<u8>,
}

impl SlicePayload {
    /// Constructs a new [`SlicePayload`] from its component parts.
    pub(crate) fn new(parent: Option<(Slot, BlockHash)>, data: Vec<u8>) -> Self {
        Self { parent, data }
    }

    /// Serializes the payload into bytes.
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        bincode::serde::encode_to_vec(self, BINCODE_CONFIG).unwrap()
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

/// Creates a [`SlicePayload`] with a random payload of desired size.
///
/// The payload does not contain valid transactions.
/// This function should only be used for testing and benchmarking.
//
// XXX: This is only used in test and benchmarking code.
// Ensure it is only compiled when we are testing or benchmarking.
pub(crate) fn create_slice_payload_with_invalid_txs(
    parent: Option<(Slot, Hash)>,
    desired_size: usize,
) -> SlicePayload {
    let mut payload = vec![MaybeUninit::uninit(); desired_size];

    let mut used = wincode::serialize_into(&parent, &mut payload).unwrap();
    let left = desired_size.checked_sub(used).unwrap();

    let size = left.checked_sub(8).unwrap();
    let mut data = vec![0; size];
    let mut rng = rng();
    rng.fill_bytes(&mut data);
    used += wincode::serialize_into(data, &mut payload[used..]).unwrap();
    assert_eq!(used, desired_size);

    let len = payload.len();
    let cap = payload.capacity();
    let ptr = payload.as_mut_ptr() as *mut u8;
    std::mem::forget(payload); // prevent dropping uninitialized memory
    let payload: Vec<u8> = unsafe { Vec::from_raw_parts(ptr, len, cap) };
    payload.as_slice().into()
}

/// Creates a [`Slice`] with a random payload of desired size.
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
    Slice::from_parts(header, payload, None)
}
