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
    slice_sig: Signature,
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
    pub fn slice_root(&self) -> SliceRoot {
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

/// Number of bytes in the commitment that the leader signs for each slice.
///
/// Layout: `slot` (u64 LE) || `slice_index` (u64 LE) || `is_last` (u8) || `slice_root` (32 B).
const SLICE_COMMITMENT_LEN: usize = 8 + 8 + 1 + 32;

/// Commitment the leader signs for each slice.
///
/// Binding the `SliceHeader` into the signature prevents replay attacks.
/// A shred for slot `s`, slice `i` is never valid for slot `s'` or slice `i'`.
/// What this commitment covers is determined by the crate-private `new` constructor.
///
/// This is an opaque capability, obtainable only via [`ValidatedShred::commitment`].
/// The inner byte layout is a protocol detail, not a stable API.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SliceCommitment([u8; SLICE_COMMITMENT_LEN]);

impl SliceCommitment {
    /// Creates a [`SliceCommitment`] covering a [`SliceHeader`] and a [`SliceRoot`].
    pub(crate) fn new(header: &SliceHeader, slice_root: &SliceRoot) -> Self {
        let mut buf = [0u8; SLICE_COMMITMENT_LEN];
        buf[0..8].copy_from_slice(&header.slot.inner().to_le_bytes());
        buf[8..16].copy_from_slice(&(header.slice_index.inner() as u64).to_le_bytes());
        buf[16] = u8::from(header.is_last);
        buf[17..49].copy_from_slice(slice_root.as_ref());
        Self(buf)
    }
}

impl AsRef<[u8]> for SliceCommitment {
    fn as_ref(&self) -> &[u8] {
        &self.0
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
    ) -> Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        // an empty set is too few shreds, not an invalid layout; catch it here
        // so it doesn't surface as the `InvalidLayout` that `try_new` returns
        if shreds.iter().all(Option::is_none) {
            return Err(DeshredError::NotEnoughShreds);
        }
        let shreds =
            ValidatedShreds::try_new(shreds, Self::DATA_OUTPUT_SHREDS, Self::CODING_OUTPUT_SHREDS)
                .ok_or(DeshredError::InvalidLayout)?;
        self.deshred_validated_shreds(shreds)
    }

    /// The core deshreding implementation that the actual shredders provide.
    ///
    /// NOTE: this is not part of the public API, use [`Shredder::deshred()`] instead.
    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError>;
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
    ) -> Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let (payload_bytes, raw_shreds) = self.0.deshred(shreds)?;
        let payload = SlicePayload::try_from(payload_bytes.as_slice())?;
        finalize_deshred(raw_shreds, shreds, payload)
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
    ) -> Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let (payload_bytes, mut raw_shreds) = self.0.deshred(shreds)?;
        let payload = SlicePayload::try_from(payload_bytes.as_slice())?;
        // this shredder outputs no data shreds
        raw_shreds.data = vec![];
        finalize_deshred(raw_shreds, shreds, payload)
    }
}

impl Default for CodingOnlyShredder {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_OUTPUT_SHREDS))
    }
}

/// A shredder using a PETS-style all-or-nothing construction.
///
/// The slice payload is encrypted under a random key, and the key is packed into
/// the tail of the last data shred, which is *withheld* from dissemination. The
/// remaining `DATA_SHREDS - 1` ciphertext data shreds and
/// `TOTAL_SHREDS - DATA_SHREDS + 1` coding shreds are output. The key can only be
/// reconstructed (via Reed-Solomon) once [`DATA_SHREDS`] shreds are available, so
/// any smaller set of shreds reveals nothing about the plaintext.
///
/// NOTE: This realizes the "withhold the key share" idea; it is not the
/// polynomial-based scheme of <https://arxiv.org/abs/2502.02774>.
pub struct PetsShredder(ReedSolomonCoder);

impl Shredder for PetsShredder {
    const MAX_DATA_SIZE: usize = AONT_MAX_DATA_SIZE;
    const DATA_OUTPUT_SHREDS: usize = DATA_SHREDS - 1;
    const CODING_OUTPUT_SHREDS: usize = TOTAL_SHREDS - DATA_SHREDS + 1;

    fn shred(
        &mut self,
        slice: Slice,
        sk: &SecretKey,
    ) -> Result<[ValidatedShred; TOTAL_SHREDS], ShredError> {
        let (header, payload) = slice.deconstruct();
        // the PETS key material is just the key itself
        let mut raw_shreds = aont_encode(&mut self.0, payload, |key, _ciphertext| key)?;
        // withhold the last data shred, which carries the key in its tail
        raw_shreds.data.pop();
        Ok(data_and_coding_to_output_shreds(header, raw_shreds, sk))
    }

    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let mut raw_shreds = self.0.reconstruct_data(shreds)?;
        // the PETS key is stored directly in the last shred's tail
        let payload = aont_decode(&raw_shreds, |key, _ciphertext| key)?;
        // withhold the last shred again to match the leader's Merkle tree
        raw_shreds.data.pop();
        finalize_deshred(raw_shreds, shreds, payload)
    }
}

impl Default for PetsShredder {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_OUTPUT_SHREDS))
    }
}

/// A shredder that uses the RAONT-RS all-or-nothing construction.
///
/// The slice payload is encrypted under a random key, and the *difference value*
/// `cd = key XOR H(ciphertext)` is packed into the tail of the last data shred
/// (all [`DATA_SHREDS`] data shreds and `TOTAL_SHREDS - DATA_SHREDS` coding shreds
/// are output). To recover the key one needs both `cd` and the entire ciphertext
/// (to recompute `H(ciphertext)`), so no set of fewer than [`DATA_SHREDS`] shreds
/// can.
///
/// See also: <https://eprint.iacr.org/2016/1014>
pub struct AontShredder(ReedSolomonCoder);

impl Shredder for AontShredder {
    const MAX_DATA_SIZE: usize = AONT_MAX_DATA_SIZE;
    const DATA_OUTPUT_SHREDS: usize = DATA_SHREDS;
    const CODING_OUTPUT_SHREDS: usize = TOTAL_SHREDS - DATA_SHREDS;

    fn shred(
        &mut self,
        slice: Slice,
        sk: &SecretKey,
    ) -> Result<[ValidatedShred; TOTAL_SHREDS], ShredError> {
        let (header, payload) = slice.deconstruct();
        // the RAONT-RS key material is the key XORed with the hash of the ciphertext
        let raw_shreds = aont_encode(&mut self.0, payload, aont_difference_value)?;
        Ok(data_and_coding_to_output_shreds(header, raw_shreds, sk))
    }

    fn deshred_validated_shreds(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
        let raw_shreds = self.0.reconstruct_data(shreds)?;
        // inverting `cd = key XOR H(ciphertext)` recovers the key (XOR is its own inverse)
        let payload = aont_decode(&raw_shreds, aont_difference_value)?;
        finalize_deshred(raw_shreds, shreds, payload)
    }
}

/// The RAONT-RS difference value `key XOR H(ciphertext)`.
///
/// XOR is its own inverse, so this maps key to `cd` when shredding and `cd` back
/// to key when deshredding.
fn aont_difference_value(
    mut key: [u8; cipher::KEY_BYTES],
    ciphertext: &[u8],
) -> [u8; cipher::KEY_BYTES] {
    let h = hash(ciphertext);
    for (k, hb) in key.iter_mut().zip(h.as_ref()) {
        *k ^= hb;
    }
    key
}

impl Default for AontShredder {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_OUTPUT_SHREDS))
    }
}

/// Completes deshredding; shared by all shredder variants.
///
/// Given the reconstructed (and already trimmed) `raw_shreds` and the
/// (already transformed) `payload`, this verifies the Merkle tree, builds the
/// [`ReconstructedSlice`], and reconstructs all [`TOTAL_SHREDS`] output shreds.
fn finalize_deshred(
    raw_shreds: RawShreds,
    shreds: ValidatedShreds,
    payload: SlicePayload,
) -> Result<(ReconstructedSlice, [ValidatedShred; TOTAL_SHREDS]), DeshredError> {
    let any_shred = shreds.any_shred();
    let slice_root = any_shred.slice_root().clone();

    // additional Merkle tree validity check
    // NOTE: This is necessary to catch maliciously constructed slices.
    let tree = check_merkle_tree(&raw_shreds, &slice_root)?;

    let slice = ReconstructedSlice::from_shreds(payload, any_shred, slice_root);
    let header = slice.to_header();

    // turn reconstructed shreds into output shreds (with root, path, sig)
    let leader_sig = any_shred.as_shred().slice_sig;
    let reconstructed_shreds = assemble_output_shreds(header, raw_shreds, &tree, leader_sig);
    Ok((slice, reconstructed_shreds))
}

/// Bytes used to store the true plaintext length after the key material.
const LEN_BYTES: usize = 4;

/// Size of the trailing key block: the key material plus the length field.
const KEY_BLOCK_BYTES: usize = cipher::KEY_BYTES + LEN_BYTES;

/// Maximum plaintext bytes the all-or-nothing layout can hold in one slice.
///
/// All [`DATA_SHREDS`] shreds carry ciphertext except for the trailing key block.
const AONT_MAX_DATA_SIZE: usize = DATA_SHREDS * MAX_DATA_PER_SHRED - KEY_BLOCK_BYTES;

// `aont_shred_bytes` rounds shred sizes up to the next even number; this only
// stays within `MAX_DATA_PER_SHRED` at max payload if that limit itself is even
const _: () = assert!(MAX_DATA_PER_SHRED.is_multiple_of(2));

/// Minimum shred size for the all-or-nothing layout.
///
/// The trailing key block must fit entirely within the last shred, and shred
/// sizes must be even (a `reed_solomon_simd` requirement).
const AONT_MIN_SHRED_BYTES: usize = KEY_BLOCK_BYTES + KEY_BLOCK_BYTES % 2;

/// Chooses the per-shred byte size for the all-or-nothing layout.
///
/// All [`DATA_SHREDS`] shreds together must hold `payload_len` ciphertext bytes
/// plus the [`KEY_BLOCK_BYTES`]-byte key block, every shred must be at least
/// [`AONT_MIN_SHRED_BYTES`] (so the key block fits in the last shred), and shred
/// sizes must be even.
fn aont_shred_bytes(payload_len: usize) -> usize {
    let needed = (payload_len + KEY_BLOCK_BYTES).div_ceil(DATA_SHREDS);
    needed.max(AONT_MIN_SHRED_BYTES).next_multiple_of(2)
}

/// Encrypts `payload` and lays it out for an all-or-nothing transform.
///
/// The layout is a single buffer of `DATA_SHREDS * shred_bytes` bytes:
///
/// ```text
/// [ Enc(plaintext ‖ zero-padding) | key_material | length ]
/// \------ ciphertext region ------/\----- key block ------/
/// ```
///
/// The plaintext is zero-padded so the ciphertext fills everything up to the
/// trailing key block; because the padding encrypts to keystream, the whole
/// ciphertext region is pseudorandom. The key block is the last
/// [`KEY_BLOCK_BYTES`] bytes and, since `shred_bytes >= AONT_MIN_SHRED_BYTES`,
/// lies entirely within the last shred.
///
/// Returns all [`DATA_SHREDS`] data shreds with coding; the caller decides
/// whether to keep or withhold the last (key-bearing) shred.
///
/// This confinement of the key material to a single, sufficiently large shred is
/// what makes the construction secure: no set of fewer than [`DATA_SHREDS`]
/// shreds can both obtain the key material and reconstruct the full ciphertext.
fn aont_encode(
    coder: &mut ReedSolomonCoder,
    payload: SlicePayload,
    key_material: impl FnOnce([u8; cipher::KEY_BYTES], &[u8]) -> [u8; cipher::KEY_BYTES],
) -> Result<RawShreds, ShredError> {
    let mut buffer: Vec<u8> = payload.into();
    let payload_len = buffer.len();
    if payload_len > AONT_MAX_DATA_SIZE {
        return Err(ShredError::TooMuchData);
    }

    let shred_bytes = aont_shred_bytes(payload_len);
    let region_len = DATA_SHREDS * shred_bytes - KEY_BLOCK_BYTES;

    // zero-pad the plaintext to fill the ciphertext region, then encrypt
    buffer.resize(region_len, 0);
    let key = cipher::encrypt_with_random_key(&mut buffer);
    let key_material = key_material(key, &buffer);

    // append the trailing key block: key material then the true plaintext length
    buffer.extend_from_slice(&key_material);
    buffer.extend_from_slice(&(payload_len as u32).to_le_bytes());

    let data: Vec<Vec<u8>> = buffer.chunks(shred_bytes).map(<[u8]>::to_vec).collect();
    debug_assert_eq!(data.len(), DATA_SHREDS);
    Ok(coder.encode_coding_from_data(&data))
}

/// Recovers the [`SlicePayload`] from an all-or-nothing layout.
///
/// Inverse of [`aont_encode`]: `derive_key` turns the trailing key material and
/// the full ciphertext region back into the symmetric key. `raw_shreds` must
/// contain all [`DATA_SHREDS`] data shreds.
///
/// # Errors
///
/// Returns [`DeshredError::BadEncoding`] if the layout is malformed or the
/// decrypted plaintext is not a valid [`SlicePayload`].
fn aont_decode(
    raw_shreds: &RawShreds,
    derive_key: impl FnOnce([u8; cipher::KEY_BYTES], &[u8]) -> [u8; cipher::KEY_BYTES],
) -> Result<SlicePayload, DeshredError> {
    // concatenate all data shreds: [ciphertext region | key material | length]
    let mut buffer = Vec::new();
    for shred in &raw_shreds.data {
        buffer.extend_from_slice(shred);
    }

    // split the trailing key block off the end
    let region_len = buffer
        .len()
        .checked_sub(KEY_BLOCK_BYTES)
        .ok_or(DeshredError::BadEncoding)?;
    let key_material: [u8; cipher::KEY_BYTES] = buffer[region_len..region_len + cipher::KEY_BYTES]
        .try_into()
        .expect("slice is exactly KEY_BYTES long");
    let len_bytes: [u8; LEN_BYTES] = buffer[region_len + cipher::KEY_BYTES..]
        .try_into()
        .expect("slice is exactly LEN_BYTES long");
    let payload_len = u32::from_le_bytes(len_bytes) as usize;
    if payload_len > region_len {
        return Err(DeshredError::BadEncoding);
    }

    buffer.truncate(region_len);
    let key = derive_key(key_material, &buffer);
    // decrypt only the real plaintext prefix; the rest was zero-padding
    buffer.truncate(payload_len);
    cipher::apply_keystream(key, &mut buffer);

    Ok(SlicePayload::try_from(buffer.as_slice())?)
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
    let slice_root = tree.get_root();
    let slice_sig = sk.sign_bytes(SliceCommitment::new(&header, &slice_root).as_ref());
    assemble_output_shreds(header, raw_shreds, &tree, slice_sig)
}

/// Assembles the reconstructed `raw_shreds` into the final output shreds.
///
/// Puts the `raw_shreds` together with the `header`, `slice_sig`,
/// and a Merkle proof generated from the given `tree`.
/// Used both when producing our own block and when reconstructing another leader's block.
///
/// The output contains all data shreds before all coding shreds.
fn assemble_output_shreds(
    header: SliceHeader,
    raw_shreds: RawShreds,
    tree: &SliceMerkleTree,
    slice_sig: Signature,
) -> [ValidatedShred; TOTAL_SHREDS] {
    let slice_root = tree.get_root();
    let num_data = raw_shreds.data.len();
    raw_shreds
        .data
        .into_iter()
        .chain(raw_shreds.coding)
        .enumerate()
        .map(|(index, data)| {
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
            ValidatedShred::new_validated(
                Shred {
                    payload_type,
                    slice_sig,
                    merkle_path: tree.create_proof(index),
                },
                slice_root.clone(),
            )
        })
        .collect::<Vec<_>>()
        .try_into()
        .expect("raw shreds always total exactly TOTAL_SHREDS")
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
    /// Shreds a `data_size`-byte slice, then checks that it can be restored from
    /// any sufficient subset of shreds and not from an insufficient one.
    fn shredding_roundtrip<S: Shredder>(data_size: usize) -> Result<()> {
        let mut shredder = S::default();
        let sk = SecretKey::new(&mut rand::rng());
        let slice = create_slice_with_invalid_txs(data_size);
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
    fn deshred_rejects_tampered_coding_shreds() {
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let (header, payload) = slice.deconstruct();
        let sk = SecretKey::new(&mut rand::rng());

        // a malicious leader signs a Merkle tree over tampered coding shreds
        let mut coder = ReedSolomonCoder::new(TOTAL_SHREDS - DATA_SHREDS);
        let mut raw_shreds = coder.shred(&payload.to_bytes()).unwrap();
        raw_shreds.coding[0][0] ^= 0xFF;
        let shreds = data_and_coding_to_output_shreds(header, raw_shreds, &sk);

        // reconstructing from the data shreds re-derives the correct coding
        // shreds, exposing the mismatch with the signed Merkle root
        let input = into_array(&shreds[..DATA_SHREDS]);
        let result = RegularShredder::default().deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::InvalidMerkleTree));
    }

    #[test]
    fn deshred_rejects_empty_input() {
        // an all-`None` array must error cleanly instead of panicking
        let empty = [const { None }; TOTAL_SHREDS];
        let result = RegularShredder::default().deshred(&empty);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));
    }

    #[test]
    fn deshred_rejects_wrong_shred_type_layout() {
        let sk = SecretKey::new(&mut rand::rng());
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let shreds = CodingOnlyShredder::default().shred(slice, &sk).unwrap();

        // `CodingOnlyShredder` outputs only coding shreds, but `RegularShredder`
        // expects data shreds in the first `DATA_SHREDS` positions
        let input = into_array(&shreds);
        let result = RegularShredder::default().deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::InvalidLayout));
    }

    #[test]
    fn deshred_rejects_oversized_shreds() {
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let (header, _payload) = slice.deconstruct();
        let sk = SecretKey::new(&mut rand::rng());

        // a malicious leader signs shreds larger than `MAX_DATA_PER_SHRED`
        // (even size, so the Reed-Solomon decoder accepts it)
        let oversized = MAX_DATA_PER_SHRED + 2;
        let raw_shreds = RawShreds {
            data: vec![vec![0_u8; oversized]; DATA_SHREDS],
            coding: vec![vec![0_u8; oversized]; TOTAL_SHREDS - DATA_SHREDS],
        };
        let shreds = data_and_coding_to_output_shreds(header, raw_shreds, &sk);

        let input = into_array(&shreds[..DATA_SHREDS]);
        let result = RegularShredder::default().deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::TooMuchData));
    }

    #[test]
    fn deshred_rejects_all_zero_shreds() {
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let (header, _payload) = slice.deconstruct();
        let sk = SecretKey::new(&mut rand::rng());

        // a malicious leader signs all-zero shreds
        // -> reconstructed payload contains no 0x80 padding marker
        let raw_shreds = RawShreds {
            data: vec![vec![0_u8; MAX_DATA_PER_SHRED]; DATA_SHREDS],
            coding: vec![vec![0_u8; MAX_DATA_PER_SHRED]; TOTAL_SHREDS - DATA_SHREDS],
        };
        let shreds = data_and_coding_to_output_shreds(header, raw_shreds, &sk);

        let input = into_array(&shreds[..DATA_SHREDS]);
        let result = RegularShredder::default().deshred(&input);
        assert_eq!(result.err(), Some(DeshredError::BadEncoding));
    }

    /// Asserts that shredding a slice one byte too large errors (never panics).
    ///
    /// The AONT/PETS shredders reserve space for the encryption key, so their
    /// limit is below [`MAX_DATA_PER_SLICE`]; using `S::MAX_DATA_SIZE` exercises
    /// each shredder right at its own boundary.
    fn shred_rejects_oversized<S: Shredder>() {
        let sk = SecretKey::new(&mut rand::rng());
        // one byte more than fits into this shredder's slice
        let slice = create_slice_with_invalid_txs(S::MAX_DATA_SIZE + 1);
        let result = S::default().shred(slice, &sk);
        assert_eq!(result.err(), Some(ShredError::TooMuchData));
    }

    #[test]
    fn shred_rejects_oversized_slice() {
        shred_rejects_oversized::<RegularShredder>();
        shred_rejects_oversized::<CodingOnlyShredder>();
        shred_rejects_oversized::<AontShredder>();
        shred_rejects_oversized::<PetsShredder>();
    }

    /// Asserts that deshredding errors (never panics) when the reconstructed
    /// payload is too short to contain the trailing encryption key.
    ///
    /// Only meaningful for the key-bearing shredders ([`AontShredder`],
    /// [`PetsShredder`]). The shred layout is derived from the shredder's own
    /// constants: `S::CODING_OUTPUT_SHREDS` coding shreds, and the data shreds
    /// truncated to `S::DATA_OUTPUT_SHREDS` (PETS drops the one carrying the key).
    fn deshred_rejects_short_payload<S: Shredder>() {
        let (header, _payload) = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE).deconstruct();
        let sk = SecretKey::new(&mut rand::rng());

        // a malicious leader crafts shreds whose reconstructed payload is too
        // short to contain the encryption key expected at the end
        let short_payload = vec![0xAA_u8; cipher::KEY_BYTES - 1];

        let mut coder = ReedSolomonCoder::new(S::CODING_OUTPUT_SHREDS);
        let mut raw_shreds = coder.shred(&short_payload).unwrap();
        // keep only the data shreds this shredder outputs (PETS drops the key shred)
        raw_shreds.data.truncate(S::DATA_OUTPUT_SHREDS);
        let shreds = data_and_coding_to_output_shreds(header, raw_shreds, &sk);

        let result = S::default().deshred(&into_array(&shreds));
        assert_eq!(result.err(), Some(DeshredError::BadEncoding));
    }

    #[test]
    fn deshred_rejects_payload_too_short_for_key() {
        deshred_rejects_short_payload::<AontShredder>();
        deshred_rejects_short_payload::<PetsShredder>();
    }

    /// Slice sizes exercised by the roundtrip tests, including tiny slices that
    /// used to break the all-or-nothing shredders' confidentiality.
    fn roundtrip_sizes<S: Shredder>() -> [usize; 4] {
        // smallest representable slice
        let min = SlicePayload::new(None, Vec::new()).to_bytes().len();
        [min, 40, 1000, S::MAX_DATA_SIZE]
    }

    #[test]
    fn regular_shredding() -> Result<()> {
        roundtrip_sizes::<RegularShredder>()
            .into_iter()
            .try_for_each(shredding_roundtrip::<RegularShredder>)
    }

    #[test]
    fn coding_only_shredding() -> Result<()> {
        roundtrip_sizes::<CodingOnlyShredder>()
            .into_iter()
            .try_for_each(shredding_roundtrip::<CodingOnlyShredder>)
    }

    #[test]
    fn aont_shredding() -> Result<()> {
        roundtrip_sizes::<AontShredder>()
            .into_iter()
            .try_for_each(shredding_roundtrip::<AontShredder>)
    }

    #[test]
    fn pets_shredding() -> Result<()> {
        roundtrip_sizes::<PetsShredder>()
            .into_iter()
            .try_for_each(shredding_roundtrip::<PetsShredder>)
    }

    /// Asserts that the PETS symmetric key is *confined* to the single withheld
    /// key shred, so the `DATA_SHREDS - 1` data shreds an adversary receives
    /// expose **zero** key bytes.
    ///
    /// PETS drops the last data shred (which carries the key), so we recover it
    /// by Reed-Solomon reconstruction and read the real key off the buffer tail.
    /// The check is *positional* rather than a content search: it proves the
    /// whole key block lies within the withheld shred's byte range. That also
    /// rules out a layout that spread the key across all `DATA_SHREDS` shreds —
    /// which a "the contiguous key doesn't appear" test would miss, since
    /// `DATA_SHREDS - 1` shreds would then still hand the adversary all but a
    /// `1 / DATA_SHREDS` fraction of it.
    ///
    /// AONT needs no analogous test: it disseminates all data shreds and stores
    /// only `key XOR H(ciphertext)`, never the raw key, so its confidentiality
    /// rests on "`DATA_SHREDS - 1` shreds can't decode", covered by
    /// [`shredding_roundtrip`].
    #[test]
    fn pets_small_slice_hides_key() {
        let mut shredder = PetsShredder::default();
        let sk = SecretKey::new(&mut rand::rng());
        let slice = create_slice_with_invalid_txs(40);
        let plaintext = slice.clone().deconstruct().1.to_bytes();

        let shreds = shredder.shred(slice, &sk).unwrap();

        // reconstruct *all* DATA_SHREDS raw data shreds
        let array = into_array(&shreds);
        let validated = ValidatedShreds::try_new(
            &array,
            PetsShredder::DATA_OUTPUT_SHREDS,
            PetsShredder::CODING_OUTPUT_SHREDS,
        )
        .unwrap();
        let mut coder = ReedSolomonCoder::new(PetsShredder::CODING_OUTPUT_SHREDS);
        let raw = coder.reconstruct_data(validated).unwrap();

        // the buffer laid out across the data shreds is [ ciphertext | key | len ]
        let shred_bytes = raw.data[0].len();
        let buffer: Vec<u8> = raw.data.iter().flatten().copied().collect();
        let key_start = buffer.len() - KEY_BLOCK_BYTES;
        let key: [u8; cipher::KEY_BYTES] = buffer[key_start..key_start + cipher::KEY_BYTES]
            .try_into()
            .unwrap();

        // guard against vacuity: this must really be the encryption key
        let mut decrypted = buffer[..key_start].to_vec();
        cipher::apply_keystream(key, &mut decrypted);
        assert!(decrypted.starts_with(&plaintext), "recovered the wrong key");

        // the entire key block must sit inside the last (withheld) shred,
        // so no key byte lands in any of the DATA_SHREDS - 1 disseminated data shreds
        let withheld_start = (DATA_SHREDS - 1) * shred_bytes;
        assert!(
            key_start >= withheld_start,
            "key block spills out of the withheld shred into disseminated data",
        );
    }
}
