// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`Slice`] and related data structures.

use std::ops::Deref;

use rand::prelude::*;
use thiserror::Error;
use wincode::config::DefaultConfig;
use wincode::{SchemaRead, SchemaWrite};

use crate::crypto::merkle::SliceRoot;
use crate::shredder::{MAX_DATA_PER_SLICE, ValidatedShred};
use crate::types::SliceIndex;
use crate::{BlockId, Slot};

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
    pub parent: Option<BlockId>,
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
    pub(crate) parent: Option<BlockId>,
    /// Same as [`Slice::data`].
    pub(crate) data: Vec<u8>,
}

impl SlicePayload {
    /// Constructs a new [`SlicePayload`] from its component parts.
    pub(crate) fn new(parent: Option<BlockId>, data: Vec<u8>) -> Self {
        Self { parent, data }
    }

    /// Serializes the payload into bytes.
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        wincode::serialize(self).expect("serializing a slice payload should not fail")
    }
}

impl From<SlicePayload> for Vec<u8> {
    fn from(payload: SlicePayload) -> Self {
        wincode::serialize(&payload).expect("serializing a slice payload should not fail")
    }
}

/// Errors that may occur while deserializing a [`SlicePayload`] from bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(crate) enum SlicePayloadError {
    /// The serialized payload is larger than a slice is allowed to hold.
    #[error("payload of {len} bytes exceeds the {MAX_DATA_PER_SLICE} byte slice limit")]
    TooLarge { len: usize },
    /// The bytes did not decode into a valid [`SlicePayload`].
    #[error("malformed slice payload")]
    BadEncoding,
}

impl TryFrom<&[u8]> for SlicePayload {
    type Error = SlicePayloadError;

    /// Deserializes a [`SlicePayload`] from bytes received over the network.
    ///
    /// Unlike a plain [`wincode::deserialize`], this:
    /// - caps preallocation at [`MAX_DATA_PER_SLICE`] (wincode has a 4 MiB default),
    /// - requires the bytes to be fully consumed (no trailing bytes), and
    /// - returns an error instead of panicking on malformed input.
    fn try_from(payload: &[u8]) -> Result<Self, Self::Error> {
        if payload.len() > MAX_DATA_PER_SLICE {
            return Err(SlicePayloadError::TooLarge { len: payload.len() });
        }
        let config = DefaultConfig::default().with_preallocation_size_limit::<MAX_DATA_PER_SLICE>();
        wincode::config::deserialize_exact(payload, config)
            .map_err(|_| SlicePayloadError::BadEncoding)
    }
}

/// Creates a [`SlicePayload`] with a random payload of desired size (in bytes).
///
/// The payload does not contain valid transactions.
/// This function should only be used for testing and benchmarking.
//
// TODO: This is only used in test and benchmarking code.
// Ensure it is only compiled when we are testing or benchmarking.
pub(crate) fn create_slice_payload_with_invalid_txs(
    parent: Option<BlockId>,
    desired_size: usize,
) -> SlicePayload {
    let parent_bytes = <Option<BlockId> as wincode::SchemaWrite<DefaultConfig>>::size_of(&parent)
        .expect("computing the serialized size of the payload header should not fail");
    // 8 bytes for data length (usize), since wincode uses fixed-length integer encoding
    let data_len_bytes = 8;

    let size = desired_size
        .checked_sub(parent_bytes + data_len_bytes)
        .expect("desired size should be large enough to hold the payload header");
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
// TODO: This is only used in test and benchmarking code.
// Ensure it is only compiled when we are testing or benchmarking.
pub fn create_slice_with_invalid_txs(desired_size: usize) -> Slice {
    let payload = create_slice_payload_with_invalid_txs(None, desired_size);
    let header = SliceHeader {
        slot: Slot::new(0),
        slice_index: SliceIndex::first(),
        is_last: true,
    };
    Slice::from_parts(header, payload)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn payload_roundtrip() {
        let payload = SlicePayload::new(None, vec![1, 2, 3, 4]);
        let bytes = payload.to_bytes();
        assert_eq!(SlicePayload::try_from(bytes.as_slice()).unwrap(), payload);
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        let mut bytes = SlicePayload::new(None, vec![1, 2, 3, 4]).to_bytes();
        // extra trailing byte
        bytes.push(0xAA);
        assert_eq!(
            SlicePayload::try_from(bytes.as_slice()),
            Err(SlicePayloadError::BadEncoding)
        );
    }

    #[test]
    fn malformed_payload_returns_error() {
        // garbage bytes must return an error rather than panicking
        assert_eq!(
            SlicePayload::try_from([0xFFu8; 4].as_slice()),
            Err(SlicePayloadError::BadEncoding)
        );
    }

    #[test]
    fn oversized_payload_returns_error() {
        let bytes = vec![0u8; MAX_DATA_PER_SLICE + 1];
        assert_eq!(
            SlicePayload::try_from(bytes.as_slice()),
            Err(SlicePayloadError::TooLarge {
                len: MAX_DATA_PER_SLICE + 1
            })
        );
    }

    #[test]
    fn inflated_length_prefix_is_rejected_without_panic() {
        // overwriting the fixint length field must error
        let mut bytes = SlicePayload::new(None, vec![]).to_bytes();
        let len = bytes.len();
        bytes[len - 8..].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(bytes.len() <= MAX_DATA_PER_SLICE);
        assert_eq!(
            SlicePayload::try_from(bytes.as_slice()),
            Err(SlicePayloadError::BadEncoding)
        );
    }
}
