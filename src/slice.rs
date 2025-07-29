// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the Slice and related data structures.

use bincode::error::DecodeError;
use serde::{Deserialize, Serialize};

use crate::Slot;
use crate::crypto::Hash;
use crate::shredder::Shred;

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
    /// Creates a slice from raw payload bytes and the metadata extracted from a shred.
    #[must_use]
    pub(crate) fn from_parts(data: Vec<u8>, any_shred: &Shred) -> Self {
        let SliceHeader {
            slot,
            slice_index,
            is_last,
        } = any_shred.payload().header;
        let merkle_root = Some(any_shred.merkle_root);
        let payload = SlicePayload::new(&data).unwrap();
        Self {
            slot,
            slice_index,
            is_last,
            merkle_root,
            parent: payload.parent,
            data: payload.data,
        }
    }

    /// Deconstructs a slice into its components: `SliceHeader` and `SlicePayload`.
    pub(crate) fn deconstruct_slice(self) -> (SliceHeader, SlicePayload) {
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

/// Struct to hold all the header payload of a Slice.
/// This is included in each Shred.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct SliceHeader {
    /// Same as `Slice::slot`.
    pub(crate) slot: Slot,
    /// Same as `Slice::slice_index`.
    pub(crate) slice_index: usize,
    /// Same as `Slice::is_last`.
    pub(crate) is_last: bool,
}

/// Struct to hold all the actual payload of a Slice.
/// This is what actually gets "shredded" in the `Shred`s.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct SlicePayload {
    parent: Option<(Slot, Hash)>,
    data: Vec<u8>,
}

impl SlicePayload {
    pub(crate) fn new(data: &[u8]) -> Result<Self, DecodeError> {
        bincode::serde::decode_from_slice(data, bincode::config::standard()).map(|(p, _)| p)
    }
}
