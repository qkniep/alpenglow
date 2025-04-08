// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Shredding and deshredding of blocks.
//!
//!
// TODO: split this file up

use aes::Aes128;
use aes::cipher::{Array, KeyIvInit, StreamCipher};
use ctr::Ctr64LE;
use rand::{RngCore, rng};
use reed_solomon_simd as rs;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::Slot;
use crate::crypto::aggsig::{PublicKey, SecretKey};
use crate::crypto::{Hash, MerkleTree, Signature, hash};

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

/// A shred is the smallest unit of data that is used when disseminating blocks.
/// Shreds are crafted to fit into an MTU size packet.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Shred {
    Data(DataShredWithPath),
    Coding(CodingShredWithPath),
}

impl Slice {
    /// Creates a slice from raw payload bytes and the metadata extracted from a shred.
    #[must_use]
    pub const fn from_parts(data: Vec<u8>, any_shred: &Shred) -> Self {
        let slot = any_shred.slot();
        let slice_index = any_shred.slice();
        let is_last = any_shred.is_last_slice();
        let merkle_root = Some(any_shred.merkle_root());
        Self {
            slot,
            slice_index,
            is_last,
            merkle_root,
            data,
        }
    }
}

impl Shred {
    /// Verifies the proof and signature of this shred.
    #[must_use]
    pub fn verify(&self, pk: &PublicKey, existing_merkle_root: Option<&Hash>) -> bool {
        let root = self.merkle_root();
        let proof = self.merkle_path();
        // FIX: make this work for all shredders
        let index = match self {
            Self::Data(_) => self.index_in_slice(),
            Self::Coding(_) => DATA_SHREDS + self.index_in_slice(),
        };
        if !MerkleTree::check_proof(self.data(), index, root, proof) {
            return false;
        }
        if let Some(prev_root) = existing_merkle_root {
            return &root == prev_root;
        }
        self.merkle_root_sig().verify(&root, pk)
    }

    /// Gives the slot number this shred is for.
    #[must_use]
    pub fn data(&self) -> &[u8] {
        match self {
            Self::Data(s) => &s.payload.0.data,
            Self::Coding(s) => &s.payload.0.data,
        }
    }

    /// Gives the slot number this shred is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        match self {
            Self::Data(s) => s.payload.0.slot,
            Self::Coding(s) => s.payload.0.slot,
        }
    }

    /// Gives the slice number (within the slot) this shred is for.
    #[must_use]
    pub const fn slice(&self) -> usize {
        match self {
            Self::Data(s) => s.payload.0.slice_index,
            Self::Coding(s) => s.payload.0.slice_index,
        }
    }

    /// Returns `true` if the shred is a data shred.
    #[must_use]
    pub const fn is_data(&self) -> bool {
        matches!(self, Self::Data(_))
    }

    /// Returns `true` if the shred is a coding shred.
    #[must_use]
    pub const fn is_coding(&self) -> bool {
        matches!(self, Self::Coding(_))
    }

    /// Returns `true` if the shreds has the last-slice bit set.
    #[must_use]
    pub const fn is_last_slice(&self) -> bool {
        match self {
            Self::Data(s) => s.payload.0.is_last_slice,
            Self::Coding(s) => s.payload.0.is_last_slice,
        }
    }

    ///
    #[must_use]
    pub const fn index_in_slice(&self) -> usize {
        match self {
            Self::Data(s) => s.payload.0.index_in_slice,
            Self::Coding(s) => s.payload.0.index_in_slice,
        }
    }

    ///
    #[must_use]
    pub const fn index_in_slot(&self) -> usize {
        let (slice_index, index_in_slice) = match self {
            Self::Data(s) => (s.payload.0.slice_index, s.payload.0.index_in_slice),
            Self::Coding(s) => (s.payload.0.slice_index, s.payload.0.index_in_slice),
        };
        slice_index * DATA_SHREDS + index_in_slice
    }

    /// Gives the merkle root of the shred.
    #[must_use]
    pub const fn merkle_root(&self) -> Hash {
        match self {
            Self::Data(s) => s.merkle_root,
            Self::Coding(s) => s.merkle_root,
        }
    }

    /// Gives the merkle root signature of the shred.
    #[must_use]
    pub const fn merkle_root_sig(&self) -> &Signature {
        match self {
            Self::Data(s) => &s.merkle_root_sig,
            Self::Coding(s) => &s.merkle_root_sig,
        }
    }

    /// Gives the merkle path of the shred.
    #[must_use]
    pub fn merkle_path(&self) -> &[Hash] {
        match self {
            Self::Data(s) => &s.merkle_path,
            Self::Coding(s) => &s.merkle_path,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DataShredWithPath {
    pub(crate) payload: DataShred,
    pub(crate) merkle_root: Hash,
    pub(crate) merkle_root_sig: Signature,
    merkle_path: Vec<Hash>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodingShredWithPath {
    pub(crate) payload: CodingShred,
    pub(crate) merkle_root: Hash,
    pub(crate) merkle_root_sig: Signature,
    merkle_path: Vec<Hash>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DataShred(ShredPayload);
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodingShred(ShredPayload);

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShredPayload {
    pub(crate) slot: Slot,
    pub(crate) slice_index: usize,
    pub(crate) index_in_slice: usize,
    pub(crate) is_last_slice: bool,
    pub(crate) data: Vec<u8>,
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
        Ok(Slice::from_parts(data, &shreds[0]))
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
        Ok(Slice::from_parts(data, &shreds[0]))
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
            DATA_SHREDS,
        )?;
        Ok(data_and_coding_to_output_shreds(data, coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<Slice, ShredderError> {
        let mut buffer = deshred_reed_solomon(shreds, DATA_SHREDS, DATA_SHREDS)?;
        if buffer.len() < 16 {
            return Err(ShredderError::BadEncoding);
        }

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
    let data_parts: Vec<_> = data.chunks(shred_bytes).map(<[u8]>::to_vec).collect();
    let coding_parts = rs::encode(num_data, num_coding, &data_parts).unwrap();

    // map raw data/coding parts to `DataShred` and `CodingShred`
    let payload_from_index_and_data = |index: usize, data: Vec<u8>| ShredPayload {
        slot,
        slice_index,
        index_in_slice: index,
        is_last_slice,
        data,
    };
    let data_shreds: Vec<_> = data_parts
        .into_iter()
        .enumerate()
        .map(|(i, p)| DataShred(payload_from_index_and_data(i, p)))
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
    let data = shreds.iter().filter_map(|s| match s {
        Shred::Data(d) => Some((d.payload.0.index_in_slice, &d.payload.0.data)),
        Shred::Coding(_) => None,
    });
    let coding = shreds.iter().filter_map(|s| match s {
        Shred::Coding(c) => Some((c.payload.0.index_in_slice, &c.payload.0.data)),
        Shred::Data(_) => None,
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
            Some(data_ref) => data_ref,
            None => restored.get(&i).unwrap(),
        };
        restored_payload.extend_from_slice(shred_data);
    }

    if restored_payload.len() > MAX_DATA_PER_SLICE {
        Err(ShredderError::TooMuchData)
    } else {
        Ok(restored_payload)
    }
}

/// Generates the Merkle tree, signs the root, and outputs shreds.
/// Each shred contains the Merkle root, its own path and the signature.
fn data_and_coding_to_output_shreds(
    data: Vec<DataShred>,
    coding: Vec<CodingShred>,
    sk: &SecretKey,
) -> Vec<Shred> {
    let mut shreds = Vec::new();
    let num_data_shreds = data.len();

    let tree = build_merkle_tree(&data, &coding);
    let merkle_root = tree.get_root();
    let sig = sk.sign(&merkle_root);

    for (i, d) in data.into_iter().enumerate() {
        shreds.push(Shred::Data(DataShredWithPath {
            payload: d,
            merkle_root,
            merkle_root_sig: sig,
            merkle_path: tree.create_proof(i),
        }));
    }
    for (i, c) in coding.into_iter().enumerate() {
        shreds.push(Shred::Coding(CodingShredWithPath {
            payload: c,
            merkle_root,
            merkle_root_sig: sig,
            merkle_path: tree.create_proof(num_data_shreds + i),
        }));
    }

    shreds
}

/// Builds the Merkle tree for a slice, where the leaves are the given shreds.
fn build_merkle_tree(data_shreds: &[DataShred], coding_shreds: &[CodingShred]) -> MerkleTree {
    let leaves: Vec<_> = data_shreds
        .iter()
        .map(|d| &d.0.data)
        .chain(coding_shreds.iter().map(|c| &c.0.data))
        .collect();
    MerkleTree::new(&leaves)
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
