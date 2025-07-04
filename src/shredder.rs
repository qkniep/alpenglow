// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Shredding and deshredding of blocks.
//!
//! This module defines the [`Shredder`] trait for shredding blocks into shreds.
//!
//! It also provides several shredders implementing this trait:
//! - [`RegularShredder`] augments data shreds with coding shreds.
//! - [`CodingOnlyShredder`] only outputs coding shreds.
//! - [`AontShredder`] uses the RAONT-RS all-or-nothing construction.
//! - [`PetsShredder`] uses the PETS all-or-nothing construction.
//!
//! Finally, it defines some of the low-level data types representing a block:
//! - [`Shred`] is a single part of the block that fits into a UDP datagram.
//! - [`Slice`] corresponds to a fixed number of shreds we perform erasure coding on.
// TODO: split this file up

use aes::Aes128;
use aes::cipher::{Array, KeyIvInit, StreamCipher};
use ctr::Ctr64LE;
use rand::{RngCore, rng};
use reed_solomon_simd as rs;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::Slot;
use crate::crypto::signature::{PublicKey, SecretKey, Signature};
use crate::crypto::{Hash, MerkleTree, hash};

/// Number of data shreds the payload of a slice is split into.
pub const DATA_SHREDS: usize = 32;
/// Total number of shreds the shredder outputs for a slice.
///
/// Generally, includes both data and coding shreds.
/// How many are data and coding depends on the specific shredder.
pub const TOTAL_SHREDS: usize = 64;
/// Maximum number of payload bytes a single shred can hold.
pub const MAX_DATA_PER_SHRED: usize = 1024;
/// Maximum number of payload bytes an entire slice can hold.
pub const MAX_DATA_PER_SLICE: usize = DATA_SHREDS * MAX_DATA_PER_SHRED;

/// Errors that may occur during shredding and deshredding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum ShredderError {
    #[error("could not deshred malformed input")]
    BadEncoding,
    #[error("too much data to fit into slice")]
    TooMuchData,
    #[error("not enough shreds to deshred")]
    NotEnoughShreds,
    #[error("more shreds than expected")]
    TooManyShreds,
    #[error("shreds are part of invalid Merkle tree")]
    InvalidMerkleTree,
}

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
    /// Payload bytes.
    pub data: Vec<u8>,
}

impl Slice {
    /// Creates a slice from raw payload bytes and the metadata extracted from a shred.
    #[must_use]
    pub const fn from_parts(data: Vec<u8>, any_shred: &Shred) -> Self {
        let slot = any_shred.payload().slot;
        let slice_index = any_shred.payload().slice_index;
        let is_last = any_shred.payload().is_last_slice;
        let merkle_root = Some(any_shred.merkle_root);
        Self {
            slot,
            slice_index,
            is_last,
            merkle_root,
            data,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ShredPayloadType {
    Data(ShredPayload),
    Coding(ShredPayload),
}

impl ShredPayloadType {
    /// Returns `true` if the payload is of data type.
    pub const fn is_data(&self) -> bool {
        matches!(self, ShredPayloadType::Data(_))
    }

    /// Returns `true` if the payload is of coding type.
    pub const fn is_coding(&self) -> bool {
        matches!(self, ShredPayloadType::Coding(_))
    }
}

/// A shred is the smallest unit of data that is used when disseminating blocks.
/// Shreds are crafted to fit into an MTU size packet.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Shred {
    pub(crate) payload_type: ShredPayloadType,
    pub(crate) merkle_root: Hash,
    merkle_root_sig: Signature,
    merkle_path: Vec<Hash>,
}

impl Shred {
    /// Verifies the proof and signature of this shred.
    #[must_use]
    pub fn verify(&self, pk: &PublicKey, existing_merkle_root: Option<&Hash>) -> bool {
        // FIX: make this work for all shredders
        let index = match self.payload_type {
            ShredPayloadType::Coding(_) => DATA_SHREDS + self.payload().index_in_slice,
            ShredPayloadType::Data(_) => self.payload().index_in_slice,
        };
        if !MerkleTree::check_proof(
            &self.payload().data,
            index,
            self.merkle_root,
            &self.merkle_path,
        ) {
            return false;
        }
        if let Some(prev_root) = existing_merkle_root {
            return &self.merkle_root == prev_root;
        }
        self.merkle_root_sig.verify(&self.merkle_root, pk)
    }

    pub const fn payload(&self) -> &ShredPayload {
        match &self.payload_type {
            ShredPayloadType::Coding(p) | ShredPayloadType::Data(p) => &p,
        }
    }
}

/// A data shred without the Merkle proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DataShred(ShredPayload);
/// A coding shred without the Merkle proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodingShred(ShredPayload);

/// Base payload of a shred, regardless of its type.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShredPayload {
    pub(crate) slot: Slot,
    pub(crate) slice_index: usize,
    pub(crate) index_in_slice: usize,
    pub(crate) is_last_slice: bool,
    pub(crate) data: bytes::Bytes,
}

impl ShredPayload {
    /// Returns the index of this shred within the entire slot.
    #[must_use]
    pub const fn index_in_slot(&self) -> usize {
        self.slice_index * DATA_SHREDS + self.index_in_slice
    }
}

/// A trait for shredding and deshredding.
///
/// Abstracts the process of turning a raw payload of bytes for an entire slice
/// into shreds and turning shreds back into the raw payload of a slice.
pub trait Shredder {
    /// Maximum number of payload bytes that fit into a slice.
    ///
    /// For the regular shredder, this is [`MAX_DATA_PER_SLICE`].
    /// However, this can be less if the specfic shredder adds some overhead.
    const MAX_DATA_SIZE: usize;

    /// Splits the given slice into [`TOTAL_SHREDS`] shreds, which depending on
    /// the specific implementation can be any combination of data and coding.
    ///
    /// # Errors
    ///
    /// - Implementations may return an error if the input is invalid or if the
    ///   shredding process fails for any implementation-specific reason.
    /// - Should always return [`ShredderError::TooMuchData`] if the `slice` is
    ///   too big, i.e., more than [`Shredder::MAX_DATA_SIZE`] bytes.
    fn shred(slice: &Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredderError>;

    /// Puts the given shreds back together into a complete slice.
    ///
    /// # Errors
    ///
    /// - Implementations may return an error if the input is invalid or if the
    ///   deshredding process fails for any implementation-specific reason.
    /// - Should always return [`ShredderError::TooMuchData`] if the reconstructed
    ///   slice is too big, i.e., more than [`Shredder::MAX_DATA_SIZE`] bytes.
    /// - Any implementation of this needs to make sure to:
    ///     1. Reconstruct all shreds (data and coding) under the Merkle tree.
    ///     2. Verify the entire Merkle tree.
    ///     3. Return [`ShredderError::InvalidMerkleTree`] if this fails.
    fn deshred(shreds: &[Shred]) -> Result<Slice, ShredderError>;
}

/// A shredder that augments the [`DATA_SHREDS`] data shreds with
/// `TOTAL_SHREDS - DATA_SHREDS` coding shreds and outputs both.
pub struct RegularShredder;

/// A shredder that only produces [`TOTAL_SHREDS`] coding shreds.
pub struct CodingOnlyShredder;

/// A shredder that uses the RAONT-RS all-or-nothing construction.
///
/// It outputs [`DATA_SHREDS`] encrypted data shreds and
/// `TOTAL_SHREDS - DATA_SHREDS` coding shreds.
///
/// See also: <https://eprint.iacr.org/2016/1014>
pub struct AontShredder;

/// A shredder that uses the PETS all-or-nothing construction.
///
/// It outputs `DATA_SHREDS-1` encrypted data shreds and
/// `TOTAL_SHREDS - DATA_SHREDS + 1` coding shreds.
///
/// See also: <https://arxiv.org/abs/2502.02774>
pub struct PetsShredder;

impl Shredder for RegularShredder {
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE;

    fn shred(slice: &Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredderError> {
        let (data, coding) = shred_reed_solomon(slice, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS)?;
        Ok(data_and_coding_to_output_shreds(data, coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<Slice, ShredderError> {
        let data = deshred_reed_solomon(shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS)?;
        let slice = Slice::from_parts(data, &shreds[0]);

        // additional Merkle tree validity check
        let merkle_root = shreds[0].merkle_root;
        let (data, coding) = shred_reed_solomon(&slice, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS)?;
        let tree = build_merkle_tree(&data, &coding);
        if tree.get_root() != merkle_root {
            return Err(ShredderError::InvalidMerkleTree);
        }

        Ok(slice)
    }
}

impl Shredder for CodingOnlyShredder {
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE;

    fn shred(slice: &Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredderError> {
        let (_data, coding) = shred_reed_solomon(slice, DATA_SHREDS, TOTAL_SHREDS)?;
        Ok(data_and_coding_to_output_shreds(vec![], coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<Slice, ShredderError> {
        let data = deshred_reed_solomon(shreds, DATA_SHREDS, TOTAL_SHREDS)?;
        let slice = Slice::from_parts(data, &shreds[0]);

        // additional Merkle tree validity check
        let merkle_root = shreds[0].merkle_root;
        let (_, coding) = shred_reed_solomon(&slice, DATA_SHREDS, TOTAL_SHREDS)?;
        let tree = build_merkle_tree(&[], &coding);
        if tree.get_root() != merkle_root {
            return Err(ShredderError::InvalidMerkleTree);
        }

        Ok(slice)
    }
}

impl Shredder for PetsShredder {
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE - 16;

    fn shred(slice: &Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredderError> {
        assert!(slice.data.len() <= Self::MAX_DATA_SIZE);
        let mut buffer = vec![0; slice.data.len()];
        buffer.copy_from_slice(&slice.data);

        let mut rng = rng();
        let mut key = Array::from([0; 16]);
        rng.fill_bytes(&mut key);
        let iv = Array::from([0; 16]);

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut buffer);

        for i in 0..16 {
            buffer.push(key[i]);
        }

        let (mut data, coding) = shred_reed_solomon_raw(
            slice.slot,
            slice.slice_index,
            slice.is_last,
            &buffer,
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS + 1,
        )?;
        // delete data shred containing key
        data.pop();

        Ok(data_and_coding_to_output_shreds(data, coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<Slice, ShredderError> {
        let mut buffer = deshred_reed_solomon(shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS + 1)?;
        if buffer.len() < 16 {
            return Err(ShredderError::BadEncoding);
        }

        // additional Merkle tree validity check
        let merkle_root = shreds[0].merkle_root;
        let (mut data, coding) = shred_reed_solomon_raw(
            shreds[0].payload().slot,
            shreds[0].payload().slice_index,
            shreds[0].payload().is_last_slice,
            &buffer,
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS + 1,
        )?;
        data.pop();
        let tree = build_merkle_tree(&data, &coding);
        if tree.get_root() != merkle_root {
            return Err(ShredderError::InvalidMerkleTree);
        }

        // decrypt slice
        let tail = buffer.split_off(buffer.len() - 16);
        let iv = Array::from([0u8; 16]);
        let key = Array::try_from(tail.as_slice()).expect("tail should have correct length");

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut buffer);

        Ok(Slice::from_parts(buffer, &shreds[0]))
    }
}

impl Shredder for AontShredder {
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE - 16;

    fn shred(slice: &Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredderError> {
        assert!(slice.data.len() <= Self::MAX_DATA_SIZE);
        let mut buffer = vec![0; slice.data.len()];
        buffer.copy_from_slice(&slice.data);

        let mut rng = rng();
        let mut key = Array::from([0; 16]);
        rng.fill_bytes(&mut key);
        let iv = Array::from([0u8; 16]);

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut buffer);

        let hash = hash(&buffer);
        for i in 0..16 {
            buffer.push(hash[i] ^ key[i]);
        }

        let (data, coding) = shred_reed_solomon_raw(
            slice.slot,
            slice.slice_index,
            slice.is_last,
            &buffer,
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS,
        )?;
        Ok(data_and_coding_to_output_shreds(data, coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<Slice, ShredderError> {
        let mut buffer = deshred_reed_solomon(shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS)?;
        if buffer.len() < 16 {
            return Err(ShredderError::BadEncoding);
        }

        // additional Merkle tree validity check
        let merkle_root = shreds[0].merkle_root;
        let (data, coding) = shred_reed_solomon_raw(
            shreds[0].payload().slot,
            shreds[0].payload().slice_index,
            shreds[0].payload().is_last_slice,
            &buffer,
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS,
        )?;
        let tree = build_merkle_tree(&data, &coding);
        if tree.get_root() != merkle_root {
            return Err(ShredderError::InvalidMerkleTree);
        }

        // decrypt slice
        let tail = buffer.split_off(buffer.len() - 16);
        let hash = hash(&buffer);

        let iv = Array::from([0u8; 16]);
        let mut key = Array::try_from(tail.as_slice()).unwrap();
        for i in 0..16 {
            key[i] ^= hash[i];
        }

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut buffer);

        Ok(Slice::from_parts(buffer, &shreds[0]))
    }
}

/// Splits the given slice into `num_data` data shreds, then generates
/// `num_coding_shreds` additional Reed-Solomon coding shreds.
///
/// # Errors
///
/// Returns [`ShredderError::TooMuchData`] if the slice contains too much data.
fn shred_reed_solomon(
    slice: &Slice,
    num_data: usize,
    num_coding: usize,
) -> Result<(Vec<DataShred>, Vec<CodingShred>), ShredderError> {
    let Slice {
        slot,
        slice_index,
        is_last,
        merkle_root: _,
        data,
    } = slice;
    shred_reed_solomon_raw(*slot, *slice_index, *is_last, data, num_data, num_coding)
}

/// Splits the given data into `num_data` data shreds, then generates
/// `num_coding_shreds` additional Reed-Solomon coding shreds.
/// The slice-specific fields `slot`, `slice_index`, and `is_last` are included
/// in every `DataShred` or `CodingShred`.
///
/// # Errors
///
/// Returns [`ShredderError::TooMuchData`] if `data` is too large.
fn shred_reed_solomon_raw(
    slot: Slot,
    slice_index: usize,
    is_last_slice: bool,
    data: &[u8],
    num_data: usize,
    num_coding: usize,
) -> Result<(Vec<DataShred>, Vec<CodingShred>), ShredderError> {
    if data.len() > MAX_DATA_PER_SLICE {
        return Err(ShredderError::TooMuchData);
    }

    let shred_bytes = data.len() / DATA_SHREDS;
    let data_parts = data.chunks(shred_bytes);
    let coding_parts = rs::encode(num_data, num_coding, data_parts.clone()).unwrap();

    // map raw data/coding parts to `DataShred` and `CodingShred`
    let payload_from_index_and_data = |index: usize, data: Vec<u8>| ShredPayload {
        slot,
        slice_index,
        index_in_slice: index,
        is_last_slice,
        data: data.into(),
    };
    let data_shreds: Vec<_> = data_parts
        .into_iter()
        .enumerate()
        .map(|(i, p)| DataShred(payload_from_index_and_data(i, p.to_vec())))
        .collect();
    let coding_shreds: Vec<_> = coding_parts
        .into_iter()
        .enumerate()
        .map(|(i, p)| CodingShred(payload_from_index_and_data(i, p)))
        .collect();

    Ok((data_shreds, coding_shreds))
}

/// Reconstructs the raw data from the given shreds.
///
/// # Errors
///
/// - Returns [`ShredderError::NotEnoughShreds`] if less than `DATA_SHREDS` are provided.
/// - Returns [`ShredderError::TooManyShreds`] if more than `TOTAL_SHREDS` are provided.
/// - Returns [`ShredderError::TooMuchData`] if reconstructed data is larger than supported.
fn deshred_reed_solomon(
    shreds: &[Shred],
    num_data: usize,
    num_coding: usize,
) -> Result<Vec<u8>, ShredderError> {
    if shreds.len() < DATA_SHREDS {
        return Err(ShredderError::NotEnoughShreds);
    } else if shreds.len() > TOTAL_SHREDS {
        return Err(ShredderError::TooManyShreds);
    }

    // filter to split data and coding shreds
    let data = shreds.iter().filter_map(|s| match &s.payload_type {
        ShredPayloadType::Data(d) => Some((d.index_in_slice, &d.data)),
        ShredPayloadType::Coding(_) => None,
    });
    let coding = shreds.iter().filter_map(|s| match &s.payload_type {
        ShredPayloadType::Coding(c) => Some((c.index_in_slice, &c.data)),
        ShredPayloadType::Data(_) => None,
    });

    let restored = rs::decode(num_data, num_coding, data.clone(), coding).unwrap();

    let mut data_shreds = vec![None; DATA_SHREDS];
    for (i, d) in data {
        data_shreds[i] = Some(d);
    }

    // restore data from data shreds (from input and restored)
    let mut restored_payload = Vec::with_capacity(MAX_DATA_PER_SLICE);
    for (i, d) in data_shreds.into_iter().enumerate() {
        let shred_data = match d {
            Some(data_ref) => data_ref.as_ref(),
            None => restored.get(&i).unwrap(),
        };
        if restored_payload.len() + shred_data.len() > MAX_DATA_PER_SLICE {
            return Err(ShredderError::TooMuchData);
        }
        restored_payload.extend_from_slice(shred_data);
    }

    Ok(restored_payload)
}

/// Generates the Merkle tree, signs the root, and outputs shreds.
/// Each shred contains the Merkle root, its own path and the signature.
fn data_and_coding_to_output_shreds(
    data: Vec<DataShred>,
    coding: Vec<CodingShred>,
    sk: &SecretKey,
) -> Vec<Shred> {
    let mut shreds = Vec::with_capacity(data.len() + coding.len());
    let num_data_shreds = data.len();

    let tree = build_merkle_tree(&data, &coding);
    let merkle_root = tree.get_root();
    let sig = sk.sign(&merkle_root);

    for (i, d) in data.into_iter().enumerate() {
        shreds.push(Shred {
            payload_type: ShredPayloadType::Data(d.0),
            merkle_root,
            merkle_root_sig: sig,
            merkle_path: tree.create_proof(i),
        });
    }
    for (i, c) in coding.into_iter().enumerate() {
        shreds.push(Shred {
            payload_type: ShredPayloadType::Coding(c.0),
            merkle_root,
            merkle_root_sig: sig,
            merkle_path: tree.create_proof(num_data_shreds + i),
        });
    }

    shreds
}

/// Builds the Merkle tree for a slice, where the leaves are the given shreds.
fn build_merkle_tree(data_shreds: &[DataShred], coding_shreds: &[CodingShred]) -> MerkleTree {
    let leaves = data_shreds
        .iter()
        .map(|d| d.0.data.as_ref())
        .chain(coding_shreds.iter().map(|c| c.0.data.as_ref()));
    MerkleTree::new_from_iter(leaves)
}

#[cfg(test)]
mod tests {
    use super::*;

    use color_eyre::Result;

    fn create_random_slice(padding: usize) -> Slice {
        let mut rng = rng();
        let mut buf = vec![0u8; MAX_DATA_PER_SLICE - padding];
        rng.fill_bytes(&mut buf);
        Slice {
            slot: 0,
            slice_index: 0,
            is_last: true,
            merkle_root: None,
            data: buf,
        }
    }

    #[test]
    fn regular_shredding() -> Result<()> {
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_random_slice(0);
        let shreds = RegularShredder::shred(&slice, &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let slice_restored = RegularShredder::deshred(&shreds)?;
        slice.merkle_root = slice_restored.merkle_root;
        assert_eq!(slice_restored, slice);

        // restore only from coding shreds
        let slice_restored = RegularShredder::deshred(&shreds[..DATA_SHREDS])?;
        assert_eq!(slice_restored, slice);

        // restore only from data shreds
        let slice_restored = RegularShredder::deshred(&shreds[DATA_SHREDS..])?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let slice_restored = RegularShredder::deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let slice_restored = RegularShredder::deshred(&shreds[start..end])?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let slice_restored = RegularShredder::deshred(&shreds[1..])?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let result = RegularShredder::deshred(&shreds[..1]);
        assert_eq!(result, Err(ShredderError::NotEnoughShreds));

        // cannot restore from too few shreds
        let result = RegularShredder::deshred(&shreds[..DATA_SHREDS - 1]);
        assert_eq!(result, Err(ShredderError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn coding_only_shredding() -> Result<()> {
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_random_slice(0);
        let shreds = CodingOnlyShredder::shred(&slice, &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let slice_restored = CodingOnlyShredder::deshred(&shreds)?;
        slice.merkle_root = slice_restored.merkle_root;
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let slice_restored = CodingOnlyShredder::deshred(&shreds[..DATA_SHREDS])?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let slice_restored = CodingOnlyShredder::deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let slice_restored = CodingOnlyShredder::deshred(&shreds[1..])?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let result = CodingOnlyShredder::deshred(&shreds[..1]);
        assert_eq!(result, Err(ShredderError::NotEnoughShreds));

        // cannot restore from too few shreds
        let result = CodingOnlyShredder::deshred(&shreds[..DATA_SHREDS - 1]);
        assert_eq!(result, Err(ShredderError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn aont_shredding() -> Result<()> {
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_random_slice(16);
        let shreds = AontShredder::shred(&slice, &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let slice_restored = AontShredder::deshred(&shreds)?;
        slice.merkle_root = slice_restored.merkle_root;
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let slice_restored = AontShredder::deshred(&shreds[..DATA_SHREDS])?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let slice_restored = AontShredder::deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let slice_restored = AontShredder::deshred(&shreds[start..end])?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let slice_restored = AontShredder::deshred(&shreds[1..])?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let result = AontShredder::deshred(&shreds[..1]);
        assert_eq!(result, Err(ShredderError::NotEnoughShreds));

        // cannot restore from too few shreds
        let result = AontShredder::deshred(&shreds[..DATA_SHREDS - 1]);
        assert_eq!(result, Err(ShredderError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn pets_shredding() -> Result<()> {
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_random_slice(16);
        let shreds = PetsShredder::shred(&slice, &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let slice_restored = PetsShredder::deshred(&shreds)?;
        slice.merkle_root = slice_restored.merkle_root;
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let slice_restored = PetsShredder::deshred(&shreds[..DATA_SHREDS])?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let slice_restored = PetsShredder::deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let slice_restored = PetsShredder::deshred(&shreds[start..end])?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let slice_restored = PetsShredder::deshred(&shreds[1..])?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let result = PetsShredder::deshred(&shreds[..1]);
        assert_eq!(result, Err(ShredderError::NotEnoughShreds));

        // cannot restore from too few shreds
        let result = PetsShredder::deshred(&shreds[..DATA_SHREDS - 1]);
        assert_eq!(result, Err(ShredderError::NotEnoughShreds));

        Ok(())
    }
}
