// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Slice`] and related data structures.

use rand::{RngCore, rng};
use serde::{Deserialize, Serialize};

use crate::Slot;
use crate::crypto::Hash;
use crate::shredder::{MAX_DATA_PER_SLICE, Shred};

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
    pub parent: Option<(Slot, Hash)>,
    /// Payload bytes.
    pub data: Vec<u8>,
}

impl Slice {
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
        println!("from: ret.data.len={} bytes={}", ret.data.len(), bytes);
        // XXX: add an assertion that return bytes is equal to teh size of payload.
        ret
    }
}

// Returns the number of bytes that are actually set in the `val`
fn num_bytes_set(mut val: usize) -> usize {
    let mut cnt = 0;
    while val != 0 {
        val /= 256;
        cnt += 1;
    }
    cnt
}

// XXX: This is only used in test and benchmarking code.  Ensure it is only compiled when we are testing or benchmarking.
pub fn create_random_slice_payload(desired_size: usize) -> SlicePayload {
    let mut payload = vec![0; desired_size];

    let parent: Option<(Slot, Hash)> = None;
    let used = bincode::serde::encode_into_slice(parent, &mut payload, bincode::config::standard())
        .unwrap();
    let left = desired_size.checked_sub(used).unwrap();

    // Super hacky.  Figure out how big the data should be so that its bincode encoded size is `left`
    let size = left
        .checked_sub(num_bytes_set(desired_size))
        .unwrap()
        .checked_sub(1)
        .unwrap();
    let mut data = vec![0; size];
    let mut rng = rng();
    rng.fill_bytes(&mut data);
    bincode::serde::encode_into_slice(data, &mut payload[used..], bincode::config::standard())
        .unwrap();

    payload.into()
}

// XXX: This is only used in test and benchmarking code.  Ensure it is only compiled when we are testing or benchmarking.
pub fn create_random_slice(desired_size: usize) -> Slice {
    let payload = create_random_slice_payload(desired_size);
    let header = SliceHeader {
        slot: Slot::new(0),
        slice_index: 0,
        is_last: true,
    };
    Slice::from_parts(header, payload, None)
}
