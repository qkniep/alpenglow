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
use crate::crypto::{MerkleTree, cipher, hash};
use crate::shredder::validated_shreds::ValidatedShreds;
use crate::types::{ReconstructedSlice, Slice, SliceHeader, SlicePayload, SlicePayloadError};

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
    #[error("shreds array contains invalid sequence")]
    InvalidLayout,
    #[error("not enough shreds to deshred")]
    NotEnoughShreds,
    #[error("too much data to fit into slice")]
    TooMuchData,
    #[error("could not deshred malformed input")]
    BadEncoding,
    #[error("shreds are part of invalid Merkle tree")]
    InvalidMerkleTree,
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

impl From<SlicePayloadError> for DeshredError {
    fn from(err: SlicePayloadError) -> Self {
        match err {
            SlicePayloadError::TooLarge { .. } => Self::TooMuchData,
            SlicePayloadError::BadEncoding => Self::BadEncoding,
        }
    }
}

#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub enum ShredPayloadType {
    Data(ShredPayload),
    Coding(ShredPayload),
}

/// A shred is the smallest unit of data that is used when disseminating blocks.
///
/// Shreds are crafted to always fit into an MTU-size packet.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub struct Shred {
    payload_type: ShredPayloadType,
    merkle_root_sig: Signature,
    merkle_path: SliceProof,
}

impl Shred {
    /// Verifies only the Merkle proof of this shred against the given root.
    ///
    /// For full verification, see [`ValidatedShred::try_new`].
    #[must_use]
    pub fn verify_path_only(&self, root: &SliceRoot) -> bool {
        SliceMerkleTree::check_proof(
            &self.payload().data,
            *self.payload().shred_index,
            root,
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

    /// Derives the Merkle root of the slice from this shred's proof.
    #[must_use]
    pub fn merkle_root(&self) -> SliceRoot {
        SliceMerkleTree::derive_root(
            &self.payload().data,
            *self.payload().shred_index,
            &self.merkle_path,
        )
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
    /// However, this can be less if the specific shredder adds some overhead.
    const MAX_DATA_SIZE: usize;

    /// When [`Shredder::shred`] is called, how many data shreds will be produced.
    const DATA_OUTPUT_SHREDS: usize;

    /// When [`Shredder::shred`] is called, how many coding shreds will be produced.
    const CODING_OUTPUT_SHREDS: usize;

    /// Splits the given slice into [`TOTAL_SHREDS`] shreds.
    ///
    /// Produces [`Self::DATA_OUTPUT_SHREDS`] data shreds and
    /// [`Self::CODING_OUTPUT_SHREDS`] coding shreds (both depend on the implementer).
    /// All data shreds appear before all coding shreds in the output.
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
    /// This is a convenience wrapper around [`Shredder::deshred_into`] that
    /// leaves the input untouched, at the cost of cloning the present shreds.
    ///
    /// # Errors
    ///
    /// Same as [`Shredder::deshred_into`].
    fn deshred(
        &mut self,
        shreds: &[Option<ValidatedShred>; TOTAL_SHREDS],
    ) -> Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let mut shreds = shreds.clone();
        let slice = self.deshred_into(&mut shreds)?;
        let shreds = shreds.map(|s| s.expect("deshred_into reconstructs all missing shreds"));
        Ok((slice, shreds))
    }

    /// Puts the given shreds back together into a complete slice, in place.
    ///
    /// Reconstructs all missing shreds, storing them in the corresponding
    /// `None` entries of `shreds`. Already present shreds are left untouched.
    /// After a successful call, all [`TOTAL_SHREDS`] entries are `Some`.
    ///
    /// # Errors
    ///
    /// - Implementations may return an error if the input is invalid or if the
    ///   deshredding process fails for any implementation-specific reason.
    /// - Should always return [`DeshredError::TooMuchData`] if the reconstructed
    ///   slice is too big, i.e., more than [`Shredder::MAX_DATA_SIZE`] bytes.
    /// - Returns [`DeshredError::InvalidMerkleTree`] if the reconstructed shreds
    ///   do not form a Merkle tree matching the root of the received shreds.
    fn deshred_into(
        &mut self,
        shreds: &mut [Option<ValidatedShred>; TOTAL_SHREDS],
    ) -> Result<ReconstructedSlice, DeshredError> {
        let validated =
            ValidatedShreds::try_new(shreds, Self::DATA_OUTPUT_SHREDS, Self::CODING_OUTPUT_SHREDS)
                .ok_or(DeshredError::InvalidLayout)?;
        let (payload_bytes, raw_shreds) = self.deshred_validated_shreds(validated)?;

        // gather everything needed from any one of the received shreds
        let any_shred = validated.any_shred();
        let merkle_root = any_shred.merkle_root().clone();
        let header = any_shred.payload().header;
        let leader_sig = any_shred.as_shred().merkle_root_sig;

        // additional Merkle tree validity check
        // NOTE: This is necessary to catch maliciously constructed slices.
        let tree = check_merkle_tree(&raw_shreds, &merkle_root)?;

        let payload = SlicePayload::try_from(payload_bytes.as_slice())?;
        let slice = ReconstructedSlice::from_shreds(payload, any_shred, merkle_root);

        // reconstruct missing output shreds (with root, path, sig) in place
        fill_missing_shreds(shreds, header, raw_shreds, &tree, leader_sig);
        Ok(slice)
    }

    /// The core deshreding implementation that the actual shredders provide.
    ///
    /// Decodes the erasure coding and reverses any shredder-specific payload
    /// transformation. Returns the raw payload bytes of the slice together
    /// with all [`TOTAL_SHREDS`] reconstructed raw shreds.
    ///
    /// NOTE: this is not part of the public API, normally, [`Shredder::deshred()`]
    /// or [`Shredder::deshred_into()`] should be used.
    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(Vec<u8>, RawShreds), DeshredError>;
}

/// A plain Reed-Solomon shredder.
///
/// It augments the the [`DATA_SHREDS`] data shreds with
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
    ) -> Result<(Vec<u8>, RawShreds), DeshredError> {
        Ok(self.0.deshred(shreds)?)
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
    ) -> Result<(Vec<u8>, RawShreds), DeshredError> {
        let (payload_bytes, mut raw_shreds) = self.0.deshred(shreds)?;
        // this shredder outputs no data shreds
        raw_shreds.data = vec![];
        Ok((payload_bytes, raw_shreds))
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
    // needs space for the symmetric encryption key
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE - cipher::KEY_BYTES;
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

        let key = cipher::encrypt_with_random_key(&mut payload);
        payload.extend_from_slice(&key);

        let mut raw_shreds = self.0.shred(&payload)?;
        // delete data shred containing key
        raw_shreds.data.pop();

        Ok(data_and_coding_to_output_shreds(header, raw_shreds, sk))
    }

    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(Vec<u8>, RawShreds), DeshredError> {
        let (buffer, mut raw_shreds) = self.0.deshred(shreds)?;
        // delete data shred that contained the key
        raw_shreds.data.pop();
        // the PETS key is the plaintext tail of the buffer
        let payload_bytes = decrypt_payload(buffer, |key, _buffer| key)?;
        Ok((payload_bytes, raw_shreds))
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
    // needs space for the symmetric encryption key
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE - cipher::KEY_BYTES;
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

        let key = cipher::encrypt_with_random_key(&mut payload);
        // append the key XORed with the hash of the ciphertext
        let hash = hash(&payload);
        payload.extend(key.iter().zip(hash.as_ref()).map(|(k, h)| k ^ h));

        let raw_shreds = self.0.shred(&payload)?;
        Ok(data_and_coding_to_output_shreds(header, raw_shreds, sk))
    }

    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(Vec<u8>, RawShreds), DeshredError> {
        let (buffer, raw_shreds) = self.0.deshred(shreds)?;
        // the RAONT-RS key is the tail XORed with the hash of the payload
        let payload_bytes = decrypt_payload(buffer, |mut key, buffer| {
            let hash = hash(buffer);
            for (k, h) in key.iter_mut().zip(hash.as_ref()) {
                *k ^= h;
            }
            key
        })?;
        Ok((payload_bytes, raw_shreds))
    }
}

impl Default for AontShredder {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_OUTPUT_SHREDS))
    }
}

/// Decrypts a payload with an embedded key (at the end).
///
/// Strips the trailing key material off `buffer`, decrypts the remaining
/// ciphertext in place, and returns the plaintext bytes.
/// `derive_key` needs to turn the raw [`cipher::KEY_BYTES`]-byte tail
/// and the remaining ciphertext `buffer` into the actual decryption key.
///
/// # Errors
///
/// Returns [`DeshredError::BadEncoding`] if `buffer` is too short to contain a key.
fn decrypt_payload(
    mut buffer: Vec<u8>,
    derive_key: impl FnOnce([u8; cipher::KEY_BYTES], &[u8]) -> [u8; cipher::KEY_BYTES],
) -> Result<Vec<u8>, DeshredError> {
    // split the key tail off the buffer, the remainder is the ciphertext
    let ciphertext_len = buffer
        .len()
        .checked_sub(cipher::KEY_BYTES)
        .ok_or(DeshredError::BadEncoding)?;
    let tail = buffer.split_off(ciphertext_len);
    let tail = tail.try_into().expect("tail is exactly KEY_BYTES long");

    let key = derive_key(tail, &buffer);
    cipher::apply_keystream(key, &mut buffer);

    Ok(buffer)
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
    let merkle_root_sig = sk.sign_bytes(merkle_root.as_ref());
    assemble_output_shreds(header, raw_shreds, &tree, merkle_root_sig)
}

/// Assembles the reconstructed `raw_shreds` into the final output shreds.
///
/// Puts the `raw_shreds` together with the `header`, `merkle_root_sig`,
/// and a Merkle proof generated from the given `tree`.
/// Used both when producing our own block and when reconstructing another leader's block.
///
/// The output contains all data shreds before all coding shreds.
fn assemble_output_shreds(
    header: SliceHeader,
    raw_shreds: RawShreds,
    tree: &SliceMerkleTree,
    merkle_root_sig: Signature,
) -> [ValidatedShred; TOTAL_SHREDS] {
    let mut shreds = [const { None }; TOTAL_SHREDS];
    fill_missing_shreds(&mut shreds, header, raw_shreds, tree, merkle_root_sig);
    shreds.map(|shred| shred.expect("fill_missing_shreds fills all empty entries"))
}

/// Reconstructs missing output shreds (data first, then coding) in place.
///
/// Fills each `None` entry of `shreds` with the corresponding shred built from
/// the reconstructed `raw_shreds`, the slice's Merkle `tree`, and
/// `merkle_root_sig`. Already present shreds are left untouched.
///
/// Used both when producing our own block (signature freshly created over the
/// root, see [`data_and_coding_to_output_shreds`]) and when reconstructing
/// another leader's block (signature copied from a received shred, see
/// [`Shredder::deshred_into`]). In the latter case `tree` must already match
/// the reconstructed shreds.
///
/// Each new shred contains the Merkle root, its own path and the signature.
fn fill_missing_shreds(
    shreds: &mut [Option<ValidatedShred>; TOTAL_SHREDS],
    header: SliceHeader,
    raw_shreds: RawShreds,
    tree: &SliceMerkleTree,
    merkle_root_sig: Signature,
) {
    let merkle_root = tree.get_root();
    let num_data = raw_shreds.data.len();
    assert_eq!(num_data + raw_shreds.coding.len(), TOTAL_SHREDS);
    let raw = raw_shreds.data.into_iter().chain(raw_shreds.coding);
    for ((index, data), shred) in raw.enumerate().zip(shreds.iter_mut()) {
        if shred.is_some() {
            continue;
        }
        let shred_index = ShredIndex::new(index).expect("raw shreds never exceed TOTAL_SHREDS");
        let payload = ShredPayload {
            header,
            shred_index,
            data,
        };
        let payload_type = if index < num_data {
            ShredPayloadType::Data(payload)
        } else {
            ShredPayloadType::Coding(payload)
        };
        *shred = Some(ValidatedShred::new_validated(
            Shred {
                payload_type,
                merkle_root_sig,
                merkle_path: tree.create_proof(index),
            },
            merkle_root.clone(),
        ));
    }
}

/// Builds the Merkle tree for a slice and verifies it matches the expected root.
///
/// Returns the tree if the root matches, otherwise returns [`DeshredError::InvalidMerkleTree`].
fn check_merkle_tree(
    raw_shreds: &RawShreds,
    expected_root: &SliceRoot,
) -> Result<SliceMerkleTree, DeshredError> {
    let tree = build_merkle_tree(raw_shreds);
    if tree.get_root() != *expected_root {
        return Err(DeshredError::InvalidMerkleTree);
    }
    Ok(tree)
}

/// Builds the Merkle tree for a slice, where the leaves are the given shreds.
fn build_merkle_tree(raw_shreds: &RawShreds) -> SliceMerkleTree {
    // zero-allocation chaining of slice iterators
    let leaves = raw_shreds.data.iter().chain(&raw_shreds.coding);
    MerkleTree::new(leaves)
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

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

    /// Runs the shred/deshred roundtrip test suite for the given shredder.
    ///
    /// Shreds a maximum-size slice, then checks that it can be restored from
    /// any sufficient subset of shreds and not from an insufficient one.
    fn shredding_roundtrip<S: Shredder>() -> Result<()> {
        let mut shredder = S::default();
        let sk = SecretKey::new(&mut rand::rng());
        let slice = create_slice_with_invalid_txs(S::MAX_DATA_SIZE);
        let shreds = shredder.shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let input = into_array(&shreds);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(*slice_restored, slice);

        // restore from just enough shreds (the first DATA_SHREDS)
        let input = into_array(&shreds[..DATA_SHREDS]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(*slice_restored, slice);

        // restore from just enough shreds (the last DATA_SHREDS)
        let input = into_array(&shreds[TOTAL_SHREDS - DATA_SHREDS..]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(*slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let input = into_array(&nc_shreds);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(*slice_restored, slice);

        // restore from just enough shreds (DATA_SHREDS from the middle)
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let input = into_array(&shreds[start..end]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(*slice_restored, slice);

        // restore from all but one shred
        let input = into_array(&shreds[1..]);
        let (slice_restored, _) = shredder.deshred(&input)?;
        assert_eq!(*slice_restored, slice);

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
    fn deshred_rejects_undecodable_payload() {
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let (header, _payload) = slice.deconstruct();
        // a single byte is too short to be a serialized `SlicePayload`
        // (which needs at least a parent tag plus an 8-byte length prefix)
        let sk = SecretKey::new(&mut rand::rng());
        let mut coder = ReedSolomonCoder::new(TOTAL_SHREDS - DATA_SHREDS);
        let raw_shreds = coder.shred(&[0u8]).unwrap();
        let shreds = data_and_coding_to_output_shreds(header, raw_shreds, &sk);
        // decoding it fails, but never panics
        let result = RegularShredder::default().deshred(&into_array(&shreds));
        assert_eq!(result.err(), Some(DeshredError::BadEncoding));
    }

    #[test]
    fn deshred_into_fills_missing_shreds() -> Result<()> {
        let mut shredder = RegularShredder::default();
        let sk = SecretKey::new(&mut rand::rng());
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let shreds = shredder.shred(slice.clone(), &sk)?;

        // restore in place from only the data shreds
        let mut input = into_array(&shreds[..DATA_SHREDS]);
        let restored = shredder.deshred_into(&mut input)?;
        assert_eq!(*restored, slice);

        // all missing shreds should have been reconstructed in place
        for (reconstructed, original) in input.iter().zip(&shreds) {
            let reconstructed = reconstructed.as_ref().unwrap();
            assert_eq!(reconstructed.is_data(), original.is_data());
            assert_eq!(reconstructed.payload().data, original.payload().data);
            assert_eq!(reconstructed.merkle_root(), original.merkle_root());
        }

        // too few shreds should leave the input untouched
        let mut input = into_array(&shreds[..DATA_SHREDS - 1]);
        let result = shredder.deshred_into(&mut input);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));
        assert_eq!(input.iter().flatten().count(), DATA_SHREDS - 1);

        Ok(())
    }

    #[test]
    fn regular_shredding() -> Result<()> {
        shredding_roundtrip::<RegularShredder>()
    }

    #[test]
    fn coding_only_shredding() -> Result<()> {
        shredding_roundtrip::<CodingOnlyShredder>()
    }

    #[test]
    fn aont_shredding() -> Result<()> {
        shredding_roundtrip::<AontShredder>()
    }

    #[test]
    fn pets_shredding() -> Result<()> {
        shredding_roundtrip::<PetsShredder>()
    }
}
