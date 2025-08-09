// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Slice`] and related data structures.

use rand::{RngCore, rng};
use serde::{Deserialize, Serialize};

use crate::crypto::Hash;
use crate::shredder::{MAX_DATA_PER_SLICE, Shred};
use crate::{Slot, highest_non_zero_byte};

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
    pub slice_index: usize,
    /// Indicates whether this is the last slice in the slot.
    pub is_last: bool,
    /// Merkle root hash over all shreds in this slice.
    pub merkle_root: Option<Hash>,
    /// If first slice in the block or parent changed due to optimistic handover,
    /// then indicates which block is the parent of the block this slice is part of.
    pub parent: Option<(Slot, Hash)>,
    /// Payload bytes.
    pub data: Vec<u8>,
}

impl Slice {
    /// Constructs a [`Slice`] from its component parts.
    pub(crate) fn from_parts(
        header: SliceHeader,
        payload: SlicePayload,
        merkle_root: Option<[u8; 32]>,
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
    pub(crate) fn from_shreds(payload: SlicePayload, any_shred: &Shred) -> Self {
        let header = any_shred.payload().header.clone();
        let merkle_root = Some(any_shred.merkle_root);
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
}

/// Struct to hold all the header payload of a [`Slice`].
///
/// This is included in each [`Shred`] after shredding.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct SliceHeader {
    /// Same as [`Slice::slot`].
    pub(crate) slot: Slot,
    /// Same as [`Slice::slice_index`].
    pub(crate) slice_index: usize,
    /// Same as [`Slice::is_last`].
    pub(crate) is_last: bool,
}

/// Struct to hold all the actual payload of a [`Slice`].
///
/// This is what actually gets "shredded" into different [`Shred`]s.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SlicePayload {
    parent: Option<(Slot, Hash)>,
    data: Vec<u8>,
}

impl SlicePayload {
    pub(crate) fn new(parent: Option<(Slot, Hash)>, data: Vec<u8>) -> Self {
        Self { parent, data }
    }
}

impl From<SlicePayload> for Vec<u8> {
    fn from(payload: SlicePayload) -> Self {
        bincode::serde::encode_to_vec(payload, bincode::config::standard()).unwrap()
    }
}

impl From<Vec<u8>> for SlicePayload {
    fn from(payload: Vec<u8>) -> Self {
        assert!(payload.len() <= MAX_DATA_PER_SLICE);
        let (ret, bytes): (SlicePayload, usize) =
            bincode::serde::decode_from_slice(&payload, bincode::config::standard()).unwrap();
        assert_eq!(payload.len(), bytes);
        ret
    }
}

/// Creates a [`SlicePayload`] with a random payload of desired size.
///
/// This function should only be used for testing and benchmarking.
//
// XXX: This is only used in test and benchmarking code.  Ensure it is only compiled when we are testing or benchmarking.
pub fn create_random_slice_payload(
    parent: Option<(Slot, Hash)>,
    desired_size: usize,
) -> SlicePayload {
    let mut payload = vec![0; desired_size];

    let used = bincode::serde::encode_into_slice(parent, &mut payload, bincode::config::standard())
        .unwrap();
    let left = desired_size.checked_sub(used).unwrap();

    // Super hacky.  Figure out how big the data should be so that its bincode encoded size is `left`.  If the size of the vec fits in a single byte, then it takes one byte to bincode encode it.  Otherwise, it takes number of non-zero bytes minus 1.
    let highest_byte = highest_non_zero_byte(desired_size);
    let size = if highest_byte == 1 {
        left.checked_sub(highest_byte).unwrap()
    } else {
        left.checked_sub(highest_byte)
            .unwrap()
            .checked_sub(1)
            .unwrap()
    };
    let mut data = vec![0; size];
    let mut rng = rng();
    rng.fill_bytes(&mut data);
    bincode::serde::encode_into_slice(data, &mut payload[used..], bincode::config::standard())
        .unwrap();

    payload.into()
}

/// Create a [`Slice`] with a random payload of desired size.
///
/// This function should only be used for testing and benchmarking.
//
// XXX: This is only used in test and benchmarking code.  Ensure it is only compiled when we are testing or benchmarking.
pub fn create_random_slice(desired_size: usize) -> Slice {
    let payload = create_random_slice_payload(None, desired_size);
    let header = SliceHeader {
        slot: Slot::new(0),
        slice_index: 0,
        is_last: true,
    };
    Slice::from_parts(header, payload, None)
}
