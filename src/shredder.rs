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
//! Finally, it defines the relevant low-level data type:
//! - [`Shred`] is a single part of the block that fits into a UDP datagram,
//!   that also contains the slice header, Merkle path and leader signature.
//!
//! It also uses the [`Slice`] struct defined in the [`crate::types::slice`] module.

mod pool;
mod reed_solomon;
mod shred_index;
mod validated_shred;
mod validated_shreds;

use aes::Aes128;
use aes::cipher::{Array, KeyIvInit, StreamCipher};
use ctr::Ctr64LE;
use rand::{RngCore, rng};
use thiserror::Error;
use wincode::{SchemaRead, SchemaWrite};

pub use self::pool::{ShredderGuard, ShredderPool};
use self::reed_solomon::{
    RawShreds, ReedSolomonCoder, ReedSolomonDeshredError, ReedSolomonShredError,
};
pub use self::shred_index::ShredIndex;
pub use self::validated_shred::{ShredVerifyError, ValidatedShred};
use crate::crypto::merkle::{SliceMerkleTree, SliceProof, SliceRoot};
use crate::crypto::signature::{SecretKey, Signature};
use crate::crypto::{MerkleTree, hash};
use crate::shredder::validated_shreds::ValidatedShreds;
use crate::types::{Slice, SliceHeader, SlicePayload};

/// Number of data shreds the payload of a slice is split into.
pub const DATA_SHREDS: usize = 32;
/// Total number of shreds the shredder outputs for a slice.
///
/// Generally, includes both data and coding shreds.
/// How many are data and coding depends on the specific shredder.
pub const TOTAL_SHREDS: usize = 64;
/// Maximum number of payload bytes a single shred can hold.
pub const MAX_DATA_PER_SHRED: usize = 1024;
/// Maximum number of bytes an entire slice can hold, incl. padding.
pub const MAX_DATA_PER_SLICE_AFTER_PADDING: usize = DATA_SHREDS * MAX_DATA_PER_SHRED;
/// Maximum number of payload bytes a slice can hold.
/// Our padding scheme requires that you leave at least one byte of padding.
pub const MAX_DATA_PER_SLICE: usize = MAX_DATA_PER_SLICE_AFTER_PADDING - 1;

/// Errors that may occur during shredding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum ShredError {
    #[error("too much data to fit into slice")]
    TooMuchData,
}

impl From<ReedSolomonShredError> for ShredError {
    fn from(err: ReedSolomonShredError) -> Self {
        match err {
            ReedSolomonShredError::TooMuchData => Self::TooMuchData,
        }
    }
}

/// Errors that may occur during deshredding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum DeshredError {
    #[error("could not deshred malformed input")]
    BadEncoding,
    #[error("too much data to fit into slice")]
    TooMuchData,
    #[error("not enough shreds to deshred")]
    NotEnoughShreds,
    #[error("shreds are part of invalid Merkle tree")]
    InvalidMerkleTree,
    #[error("shreds array contains invalid sequence")]
    InvalidLayout,
}

impl From<ReedSolomonDeshredError> for DeshredError {
    fn from(err: ReedSolomonDeshredError) -> Self {
        match err {
            ReedSolomonDeshredError::TooMuchData => Self::TooMuchData,
            ReedSolomonDeshredError::NotEnoughShreds => Self::NotEnoughShreds,
            ReedSolomonDeshredError::InvalidPadding => Self::BadEncoding,
        }
    }
}

impl From<ReedSolomonShredError> for DeshredError {
    fn from(err: ReedSolomonShredError) -> Self {
        match err {
            ReedSolomonShredError::TooMuchData => Self::TooMuchData,
        }
    }
}

#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub enum ShredPayloadType {
    Data(ShredPayload),
    Coding(ShredPayload),
}

/// A shred is the smallest unit of data that is used when disseminating blocks.
/// Shreds are crafted to fit into an MTU size packet.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub struct Shred {
    pub(crate) payload_type: ShredPayloadType,
    merkle_root_sig: Signature,
    merkle_path: SliceProof,
}

impl Shred {
    /// Verifies only the Merkle proof of this shred.
    ///
    /// For full verification, see [`ValidatedShred::try_new`].
    ///
    /// Returns `true` iff the Merkle root matches the given root and the proof is valid.
    #[must_use]
    pub fn verify_path_only(&self, root: &SliceRoot) -> bool {
        if &self.merkle_root != root {
            return false;
        }
        SliceMerkleTree::check_proof(
            &self.payload().data,
            *self.payload().shred_index,
            &self.merkle_root,
            &self.merkle_path,
        )
    }

    /// References the payload contained in this shred.
    pub const fn payload(&self) -> &ShredPayload {
        match &self.payload_type {
            ShredPayloadType::Coding(p) | ShredPayloadType::Data(p) => p,
        }
    }

    /// Mutably references the payload contained in this shred.
    pub const fn payload_mut(&mut self) -> &mut ShredPayload {
        match &mut self.payload_type {
            ShredPayloadType::Coding(p) | ShredPayloadType::Data(p) => p,
        }
    }

    /// Returns `true` iff this is a data shred.
    pub const fn is_data(&self) -> bool {
        matches!(self.payload_type, ShredPayloadType::Data(_))
    }

    /// Returns `true` iff this is a coding shred.
    pub const fn is_coding(&self) -> bool {
        matches!(self.payload_type, ShredPayloadType::Coding(_))
    }
}

/// Base payload of a shred, regardless of its type.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub struct ShredPayload {
    /// Slice header replicated in each shred.
    pub(crate) header: SliceHeader,
    /// Index of this shred within the slice.
    pub(crate) shred_index: ShredIndex,
    /// Raw payload bytes of this shred, part of the erasure-coded slice payload.
    pub(crate) data: Vec<u8>,
}

impl ShredPayload {
    /// Returns the index of this shred within the entire slot.
    #[must_use]
    pub fn index_in_slot(&self) -> usize {
        self.header.slice_index.inner() * TOTAL_SHREDS + *self.shred_index
    }
}

/// A trait for shredding and deshredding.
///
/// Abstracts the process of turning a raw payload of bytes for an entire slice
/// into shreds and turning shreds back into the raw payload of a slice.
pub trait Shredder: Default {
    /// Maximum number of payload bytes that fit into a slice.
    ///
    /// For the regular shredder, this is [`MAX_DATA_PER_SLICE`].
    /// However, this can be less if the specfic shredder adds some overhead.
    const MAX_DATA_SIZE: usize;

    /// When [`Shredder::shred`] is called, how many data shreds will be produced.
    const DATA_OUTPUT_SHREDS: usize;

    /// When [`Shredder::shred`] is called, how many coding shreds will be produced.
    const CODING_OUTPUT_SHREDS: usize;

    /// Splits the given slice into [`TOTAL_SHREDS`] shreds, which depending on
    /// the specific implementation can be any combination of data and coding.
    ///
    /// # Errors
    ///
    /// - Implementations may return an error if the input is invalid or if the
    ///   shredding process fails for any implementation-specific reason.
    /// - Should always return [`ShredError::TooMuchData`] if the `slice` is
    ///   too big, i.e., more than [`Shredder::MAX_DATA_SIZE`] bytes.
    fn shred(
        &mut self,
        slice: Slice,
        sk: &SecretKey,
    ) -> Result<[ValidatedShred; TOTAL_SHREDS], ShredError>;

    /// Puts the given shreds back together into a complete slice.
    ///
    /// Additionally, outputs all [`TOTAL_SHREDS`] reconstructed shreds.
    /// This includes all (potentially data and coding) shreds sent originally.
    ///
    /// # Errors
    ///
    /// - Implementations may return an error if the input is invalid or if the
    ///   deshredding process fails for any implementation-specific reason.
    /// - Should always return [`DeshredError::TooMuchData`] if the reconstructed
    ///   slice is too big, i.e., more than [`Shredder::MAX_DATA_SIZE`] bytes.
    ///
    /// - Any implementation of this needs to make sure to:
    ///     1. Reconstruct all shreds (data and coding) under the Merkle tree.
    ///     2. Verify the entire Merkle tree.
    ///     3. Return [`DeshredError::InvalidMerkleTree`] if this fails.
    fn deshred(
        &mut self,
        shreds: &[Option<ValidatedShred>; TOTAL_SHREDS],
    ) -> Result<(Slice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let shreds =
            ValidatedShreds::try_new(shreds, Self::DATA_OUTPUT_SHREDS, Self::CODING_OUTPUT_SHREDS)
                .ok_or(DeshredError::InvalidLayout)?;
        self.deshred_validated_shreds(shreds)
    }

    /// The core deshreding implementation that the actual shredders provide.
    ///
    /// NOTE: this is not part of the public API, normally, [`Shredder::deshred()`] should be used.
    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(Slice, [ValidatedShred; TOTAL_SHREDS]), DeshredError>;
}

/// A shredder that augments the [`DATA_SHREDS`] data shreds with
/// `TOTAL_SHREDS - DATA_SHREDS` coding shreds and outputs both.
pub struct RegularShredder(ReedSolomonCoder);

impl Shredder for RegularShredder {
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE;
    const DATA_OUTPUT_SHREDS: usize = DATA_SHREDS;
    const CODING_OUTPUT_SHREDS: usize = TOTAL_SHREDS - DATA_SHREDS;

    fn shred(
        &mut self,
        slice: Slice,
        sk: &SecretKey,
    ) -> Result<[ValidatedShred; TOTAL_SHREDS], ShredError> {
        let (header, payload) = slice.deconstruct();
        let raw_shreds = self.0.shred(&payload.to_bytes())?;
        Ok(data_and_coding_to_output_shreds(header, raw_shreds, sk))
    }

    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(Slice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let payload_bytes = self.0.deshred(shreds)?;
        let payload = SlicePayload::from(payload_bytes.as_slice());

        // deshreding succeeded above, there should be at least one shred in the array so the unwrap() below should be safe
        let any_shred = shreds.to_shreds().iter().find_map(|s| s.as_ref()).unwrap();
        let slice = Slice::from_shreds(payload, any_shred);
        let header = slice.to_header();

        // additional Merkle tree validity check
        let merkle_root = any_shred.merkle_root.clone();
        let raw_shreds = self.0.shred(&payload_bytes)?;
        let tree = build_merkle_tree(&raw_shreds);
        if tree.get_root() != merkle_root {
            return Err(DeshredError::InvalidMerkleTree);
        }

        // turn reconstructed shreds into output shreds (with root, path, sig)
        let leader_sig = any_shred.merkle_root_sig;
        let reconstructed_shreds =
            create_output_shreds_for_other_leader(header, raw_shreds, tree, leader_sig);

        assert_eq!(reconstructed_shreds.len(), TOTAL_SHREDS);
        Ok((slice, reconstructed_shreds))
    }
}

impl Default for RegularShredder {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_OUTPUT_SHREDS))
    }
}

/// A shredder that only produces [`TOTAL_SHREDS`] coding shreds.
pub struct CodingOnlyShredder(ReedSolomonCoder);

impl Shredder for CodingOnlyShredder {
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE;
    const DATA_OUTPUT_SHREDS: usize = 0;
    const CODING_OUTPUT_SHREDS: usize = TOTAL_SHREDS;

    fn shred(
        &mut self,
        slice: Slice,
        sk: &SecretKey,
    ) -> Result<[ValidatedShred; TOTAL_SHREDS], ShredError> {
        let (header, payload) = slice.deconstruct();
        let mut raw_shreds = self.0.shred(&payload.to_bytes())?;
        raw_shreds.data = vec![];
        Ok(data_and_coding_to_output_shreds(header, raw_shreds, sk))
    }

    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(Slice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let payload_bytes = self.0.deshred(shreds)?;
        let payload = SlicePayload::from(payload_bytes.as_slice());

        // deshreding succeeded above, there should be at least one shred in the array so the unwrap() below should be safe
        let any_shred = shreds.to_shreds().iter().find_map(|s| s.as_ref()).unwrap();
        let slice = Slice::from_shreds(payload, any_shred);

        // additional Merkle tree validity check
        let merkle_root = any_shred.merkle_root.clone();
        let mut raw_shreds = self.0.shred(&payload_bytes)?;
        raw_shreds.data = vec![];
        let tree = build_merkle_tree(&raw_shreds);
        if tree.get_root() != merkle_root {
            return Err(DeshredError::InvalidMerkleTree);
        }

        // turn reconstructed shreds into output shreds (with root, path, sig)
        let (header, _payload) = slice.clone().deconstruct();
        let leader_sig = any_shred.merkle_root_sig;
        let reconstructed_shreds =
            create_output_shreds_for_other_leader(header, raw_shreds, tree, leader_sig);

        assert_eq!(reconstructed_shreds.len(), TOTAL_SHREDS);
        Ok((slice, reconstructed_shreds))
    }
}

impl Default for CodingOnlyShredder {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_OUTPUT_SHREDS))
    }
}

/// A shredder that uses the PETS all-or-nothing construction.
///
/// It outputs `DATA_SHREDS - 1` encrypted data shreds and
/// `TOTAL_SHREDS - DATA_SHREDS + 1` coding shreds.
///
/// See also: <https://arxiv.org/abs/2502.02774>
pub struct PetsShredder(ReedSolomonCoder);

impl Shredder for PetsShredder {
    // needs 16 bytes for symmmetric encryption key
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE - 16;
    const DATA_OUTPUT_SHREDS: usize = DATA_SHREDS - 1;
    const CODING_OUTPUT_SHREDS: usize = TOTAL_SHREDS - DATA_SHREDS + 1;

    fn shred(
        &mut self,
        slice: Slice,
        sk: &SecretKey,
    ) -> Result<[ValidatedShred; TOTAL_SHREDS], ShredError> {
        let (header, payload) = slice.deconstruct();
        let mut payload: Vec<u8> = payload.into();
        assert!(payload.len() <= Self::MAX_DATA_SIZE);

        let mut rng = rng();
        let mut key = Array::from([0; 16]);
        rng.fill_bytes(&mut key);
        let iv = Array::from([0; 16]);

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut payload);

        payload.extend_from_slice(&key);
        let mut raw_shreds = self.0.shred(&payload)?;
        // delete data shred containing key
        raw_shreds.data.pop();

        Ok(data_and_coding_to_output_shreds(header, raw_shreds, sk))
    }

    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(Slice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let mut buffer = self.0.deshred(shreds)?;
        if buffer.len() < 16 {
            return Err(DeshredError::BadEncoding);
        }

        // deshreding succeeded above, there should be at least one shred in the array so the unwrap() below should be safe
        let any_shred = shreds.to_shreds().iter().find_map(|s| s.as_ref()).unwrap();

        // additional Merkle tree validity check
        let merkle_root = any_shred.merkle_root.clone();
        let header = any_shred.payload().header.clone();
        let mut raw_shreds = self.0.shred(&buffer)?;
        raw_shreds.data.pop();
        let tree = build_merkle_tree(&raw_shreds);
        if tree.get_root() != merkle_root {
            return Err(DeshredError::InvalidMerkleTree);
        }

        // decrypt slice
        let tail = buffer.split_off(buffer.len() - 16);
        let iv = Array::from([0; 16]);
        let key = Array::try_from(tail.as_slice()).expect("tail should have correct length");

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut buffer);
        let payload = SlicePayload::from(buffer.as_slice());
        let slice = Slice::from_shreds(payload, any_shred);

        // turn reconstructed shreds into output shreds (with root, path, sig)
        let leader_sig = any_shred.merkle_root_sig;
        let reconstructed_shreds =
            create_output_shreds_for_other_leader(header, raw_shreds, tree, leader_sig);

        assert_eq!(reconstructed_shreds.len(), TOTAL_SHREDS);
        Ok((slice, reconstructed_shreds))
    }
}

impl Default for PetsShredder {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_OUTPUT_SHREDS))
    }
}

/// A shredder that uses the RAONT-RS all-or-nothing construction.
///
/// It outputs [`DATA_SHREDS`] encrypted data shreds and
/// `TOTAL_SHREDS - DATA_SHREDS` coding shreds.
///
/// See also: <https://eprint.iacr.org/2016/1014>
pub struct AontShredder(ReedSolomonCoder);

impl Shredder for AontShredder {
    // needs 16 bytes for symmmetric encryption key
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE - 16;
    const DATA_OUTPUT_SHREDS: usize = DATA_SHREDS;
    const CODING_OUTPUT_SHREDS: usize = TOTAL_SHREDS - DATA_SHREDS;

    fn shred(
        &mut self,
        slice: Slice,
        sk: &SecretKey,
    ) -> Result<[ValidatedShred; TOTAL_SHREDS], ShredError> {
        let (header, payload) = slice.deconstruct();
        let mut payload: Vec<u8> = payload.into();
        assert!(payload.len() <= Self::MAX_DATA_SIZE);

        let mut rng = rng();
        let mut key = Array::from([0; 16]);
        rng.fill_bytes(&mut key);
        let iv = Array::from([0; 16]);

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut payload);

        let hash = hash(&payload);
        for i in 0..16 {
            payload.push(hash.as_ref()[i] ^ key[i]);
        }

        let raw_shreds = self.0.shred(&payload)?;
        Ok(data_and_coding_to_output_shreds(header, raw_shreds, sk))
    }

    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(Slice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let mut buffer = self.0.deshred(shreds)?;
        if buffer.len() < 16 {
            return Err(DeshredError::BadEncoding);
        }

        // deshreding succeeded above, there should be at least one shred in the array so the unwrap() below should be safe
        let any_shred = shreds.to_shreds().iter().find_map(|s| s.as_ref()).unwrap();

        // additional Merkle tree validity check
        let merkle_root = any_shred.merkle_root.clone();
        let header = any_shred.payload().header.clone();
        let raw_shreds = self.0.shred(&buffer)?;
        let tree = build_merkle_tree(&raw_shreds);
        if tree.get_root() != merkle_root {
            return Err(DeshredError::InvalidMerkleTree);
        }

        // decrypt slice
        let tail = buffer.split_off(buffer.len() - 16);
        let hash = hash(&buffer);

        let iv = Array::from([0; 16]);
        let mut key = Array::try_from(tail.as_slice()).unwrap();
        for i in 0..16 {
            key[i] ^= hash.as_ref()[i];
        }

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut buffer);
        let payload = SlicePayload::from(buffer.as_slice());
        let slice = Slice::from_shreds(payload, any_shred);

        // turn reconstructed shreds into output shreds (with root, path, sig)
        let leader_sig = any_shred.merkle_root_sig;
        let reconstructed_shreds =
            create_output_shreds_for_other_leader(header, raw_shreds, tree, leader_sig);

        assert_eq!(reconstructed_shreds.len(), TOTAL_SHREDS);
        Ok((slice, reconstructed_shreds))
    }
}

impl Default for AontShredder {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_OUTPUT_SHREDS))
    }
}

/// Generates the Merkle tree, signs the root, and outputs shreds.
///
/// Each returned shred contains the Merkle root, its own path and the signature.
fn data_and_coding_to_output_shreds(
    header: SliceHeader,
    raw_shreds: RawShreds,
    sk: &SecretKey,
) -> [ValidatedShred; TOTAL_SHREDS] {
    let tree = build_merkle_tree(&raw_shreds);
    let merkle_root = tree.get_root();
    let merkle_root_sig = sk.sign(merkle_root.as_ref());

    let convert = |shred_index: ShredIndex, data: Vec<u8>| -> (SliceProof, ShredPayload) {
        let merkle_path = tree.create_proof(*shred_index);
        let payload = ShredPayload {
            header: header.clone(),
            shred_index,
            data,
        };
        (merkle_path, payload)
    };
    let num_data = raw_shreds.data.len();
    let data = raw_shreds
        .data
        .into_iter()
        .enumerate()
        .map(|(shred_index, d)| {
            let shred_index = ShredIndex::new(shred_index).unwrap();
            let (merkle_path, payload) = convert(shred_index, d);
            (merkle_path, ShredPayloadType::Data(payload))
        });
    let coding = raw_shreds
        .coding
        .into_iter()
        .enumerate()
        .map(|(offset, c)| {
            let shred_index = num_data + offset;
            let shred_index = ShredIndex::new(shred_index).unwrap();
            let (merkle_path, payload) = convert(shred_index, c);
            (merkle_path, ShredPayloadType::Coding(payload))
        });
    data.chain(coding)
        .map(|(merkle_path, payload)| {
            ValidatedShred::new_validated(Shred {
                payload_type: payload,
                merkle_root_sig,
                merkle_path,
            })
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

/// Puts the root, path, and signature of the leader into shreds.
///
/// This is analogous to [`data_and_coding_to_output_shreds`], but for another leader.
/// Instead of signing the root, copies the existing signature from another shred.
/// Also, requires the Merkle tree to already be calculated from reconstructed shreds.
///
/// Each returned shred contains the Merkle root, its own path and the signature.
fn create_output_shreds_for_other_leader(
    header: SliceHeader,
    raw_shreds: RawShreds,
    tree: SliceMerkleTree,
    leader_signature: Signature,
) -> [ValidatedShred; TOTAL_SHREDS] {
    let convert = |shred_index: ShredIndex, data: Vec<u8>| -> (SliceProof, ShredPayload) {
        let merkle_path = tree.create_proof(*shred_index);
        let payload = ShredPayload {
            header: header.clone(),
            shred_index,
            data,
        };
        (merkle_path, payload)
    };
    let num_data = raw_shreds.data.len();
    let data = raw_shreds
        .data
        .into_iter()
        .enumerate()
        .map(|(shred_index, d)| {
            let shred_index = ShredIndex::new(shred_index).unwrap();
            let (merkle_path, payload) = convert(shred_index, d);
            (merkle_path, ShredPayloadType::Data(payload))
        });
    let coding = raw_shreds
        .coding
        .into_iter()
        .enumerate()
        .map(|(offset, c)| {
            let shred_index = num_data + offset;
            let shred_index = ShredIndex::new(shred_index).unwrap();
            let (merkle_path, payload) = convert(shred_index, c);
            (merkle_path, ShredPayloadType::Coding(payload))
        });
    data.chain(coding)
        .map(|(merkle_path, payload)| {
            ValidatedShred::new_validated(Shred {
                payload_type: payload,
                merkle_root_sig: leader_signature,
                merkle_path,
            })
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

/// Builds the Merkle tree for a slice, where the leaves are the given shreds.
fn build_merkle_tree(raw_shreds: &RawShreds) -> SliceMerkleTree {
    // zero-allocation chaining of slices
    let leaves = raw_shreds.data.iter().chain(&raw_shreds.coding);
    MerkleTree::new(leaves)
}

#[cfg(test)]
mod tests {
    use color_eyre::Result;

    use super::*;
    use crate::types::slice::create_slice_with_invalid_txs;

    /// Constructs a valid layout of `Shred`s from the input.
    fn into_array(shreds: &[ValidatedShred]) -> [Option<ValidatedShred>; TOTAL_SHREDS] {
        assert!(shreds.len() <= TOTAL_SHREDS);
        let mut ret = [const { None }; TOTAL_SHREDS];
        for shred in shreds {
            ret[*shred.payload().shred_index] = Some(shred.clone());
        }
        ret
    }

    #[test]
    fn regular_shredding() -> Result<()> {
        let mut shredder = RegularShredder::default();
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let shreds = shredder.shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let all = into_array(&shreds);
        let (slice_restored, _) = shredder.deshred(&all)?;
        slice.merkle_root = slice_restored.merkle_root.clone();
        assert_eq!(slice_restored, slice);

        // restore only from data shreds
        let coding = into_array(&shreds[..DATA_SHREDS]);
        let (slice_restored, _) = shredder.deshred(&coding)?;
        assert_eq!(slice_restored, slice);

        // restore using as many coding shreds as possible
        let data = into_array(&shreds[TOTAL_SHREDS - DATA_SHREDS..]);
        let (slice_restored, _) = shredder.deshred(&data)?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let nc_shreds = into_array(&nc_shreds);
        let (slice_restored, _) = shredder.deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let input = into_array(&shreds[start..end]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let input = into_array(&shreds[1..]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let input = into_array(&shreds[..1]);
        let result = shredder.deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        // cannot restore from too few shreds
        let input = into_array(&shreds[..DATA_SHREDS - 1]);
        let result = shredder.deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn coding_only_shredding() -> Result<()> {
        let mut shredder = CodingOnlyShredder::default();
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let shreds = shredder.shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let input = into_array(&shreds);
        let (slice_restored, _) = shredder.deshred(&input)?;
        slice.merkle_root = slice_restored.merkle_root.clone();
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let input = into_array(&shreds[..DATA_SHREDS]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let input = into_array(&nc_shreds);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let input = into_array(&shreds[1..]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let input = into_array(&shreds[..1]);
        let result = shredder.deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        // cannot restore from too few shreds
        let input = into_array(&shreds[..DATA_SHREDS - 1]);
        let result = shredder.deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn aont_shredding() -> Result<()> {
        let mut shredder = AontShredder::default();
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let shreds = shredder.shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let input = into_array(&shreds);
        let (slice_restored, _) = shredder.deshred(&input)?;
        slice.merkle_root = slice_restored.merkle_root.clone();
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let input = into_array(&shreds[..DATA_SHREDS]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let input = into_array(&nc_shreds);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let input = into_array(&shreds[start..end]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let input = into_array(&shreds[1..]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let input = into_array(&shreds[..1]);
        let result = shredder.deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        // cannot restore from too few shreds
        let input = into_array(&shreds[..DATA_SHREDS - 1]);
        let result = shredder.deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn pets_shredding() -> Result<()> {
        let mut shredder = PetsShredder::default();
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let shreds = shredder.shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let input = into_array(&shreds);
        let (slice_restored, _) = shredder.deshred(&input)?;
        slice.merkle_root = slice_restored.merkle_root.clone();
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let input = into_array(&shreds[..DATA_SHREDS]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let input = into_array(&nc_shreds);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let input = into_array(&shreds[start..end]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let input = into_array(&shreds[1..]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let input = into_array(&shreds[..1]);
        let result = shredder.deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        // cannot restore from too few shreds
        let input = into_array(&shreds[..DATA_SHREDS - 1]);
        let result = shredder.deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        Ok(())
    }
}
