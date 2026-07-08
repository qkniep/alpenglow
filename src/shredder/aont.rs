// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Byte-level all-or-nothing transforms over Reed-Solomon erasure coding.
//!
//! This is the confidentiality core beneath the AONT shredders: it turns a
//! slice's plaintext bytes into erasure-coded raw shreds such that fewer than
//! [`DATA_SHREDS`] shreds reveal nothing about the plaintext, and reconstructs
//! them back. It depends only on the erasure layer and the symmetric
//! [`cipher`](crate::crypto::cipher) — never on Merkle trees, signatures, or the
//! wire `Shred` format, which are the shredder layer's concern.
//!
//! Two constructions are provided:
//! - [`RaontRs`] stores `key XOR H(ciphertext)` in the last data shred.
//! - [`WithholdPets`] withholds the single data shred that carries the key.

use super::reed_solomon::{RawShreds, ReceivedShreds, ReedSolomonCoder};
use super::{DATA_SHREDS, DeshredError, MAX_DATA_PER_SHRED, ShredError, TOTAL_SHREDS};
use crate::crypto::{cipher, hash};

/// Bytes used to store the true plaintext length after the key material.
const LEN_BYTES: usize = 4;

/// Size of the trailing key block: the key material plus the length field.
pub(super) const KEY_BLOCK_BYTES: usize = cipher::KEY_BYTES + LEN_BYTES;

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

/// A byte-level all-or-nothing transform over Reed-Solomon erasure coding.
///
/// Implementers encrypt the payload and bind the key into the erasure-coded
/// shreds so that fewer than [`DATA_SHREDS`] shreds reveal nothing. The shredder
/// layer wraps them with the Merkle tree, signature, and wire format.
pub(super) trait Aont: Default {
    /// Maximum plaintext bytes this transform can hold in one slice.
    const MAX_DATA_SIZE: usize;
    /// Number of data shreds output (a variant may withhold one).
    const DATA_SHREDS_OUT: usize;
    /// Number of coding shreds output.
    const CODING_SHREDS_OUT: usize;

    /// Encodes plaintext `payload` bytes into raw erasure-coded shreds.
    fn encode(&mut self, payload: &[u8]) -> Result<RawShreds, ShredError>;

    /// Recovers the plaintext from `>= DATA_SHREDS` received shreds.
    ///
    /// Also returns the fully reconstructed [`RawShreds`] so the caller can
    /// rebuild the Merkle tree for verification and re-dissemination.
    fn decode(&mut self, shreds: ReceivedShreds<'_>) -> Result<(Vec<u8>, RawShreds), DeshredError>;
}

/// The RAONT-RS all-or-nothing construction.
///
/// The slice payload is encrypted under a random key, and the *difference value*
/// `cd = key XOR H(ciphertext)` is packed into the tail of the last data shred
/// (all [`DATA_SHREDS`] data shreds and `TOTAL_SHREDS - DATA_SHREDS` coding shreds
/// are output). To recover the key one needs both `cd` and the entire ciphertext
/// (to recompute `H(ciphertext)`), so no set of fewer than [`DATA_SHREDS`] shreds
/// can. See also: <https://eprint.iacr.org/2016/1014>
pub(super) struct RaontRs(ReedSolomonCoder);

impl Default for RaontRs {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_SHREDS_OUT))
    }
}

impl Aont for RaontRs {
    const MAX_DATA_SIZE: usize = AONT_MAX_DATA_SIZE;
    const DATA_SHREDS_OUT: usize = DATA_SHREDS;
    const CODING_SHREDS_OUT: usize = TOTAL_SHREDS - DATA_SHREDS;

    fn encode(&mut self, payload: &[u8]) -> Result<RawShreds, ShredError> {
        // the RAONT-RS key material is the key XORed with the hash of the ciphertext
        aont_encode(&mut self.0, payload, difference_value)
    }

    fn decode(&mut self, shreds: ReceivedShreds<'_>) -> Result<(Vec<u8>, RawShreds), DeshredError> {
        let raw_shreds = self.0.reconstruct_data(shreds)?;
        // inverting `cd = key XOR H(ciphertext)` recovers the key (XOR is its own inverse)
        let payload = aont_decode(&raw_shreds, difference_value)?;
        Ok((payload, raw_shreds))
    }
}

/// The PETS-style all-or-nothing construction ("withhold the key share").
///
/// The slice payload is encrypted under a random key packed into the tail of the
/// last data shred, which is *withheld* from dissemination; the key is only
/// recoverable via Reed-Solomon once [`DATA_SHREDS`] shreds are available.
pub(super) struct WithholdPets(ReedSolomonCoder);

impl Default for WithholdPets {
    fn default() -> Self {
        Self(ReedSolomonCoder::new(Self::CODING_SHREDS_OUT))
    }
}

impl Aont for WithholdPets {
    const MAX_DATA_SIZE: usize = AONT_MAX_DATA_SIZE;
    const DATA_SHREDS_OUT: usize = DATA_SHREDS - 1;
    const CODING_SHREDS_OUT: usize = TOTAL_SHREDS - DATA_SHREDS + 1;

    fn encode(&mut self, payload: &[u8]) -> Result<RawShreds, ShredError> {
        // the PETS key material is just the key itself
        let mut raw_shreds = aont_encode(&mut self.0, payload, |key, _ciphertext| key)?;
        // withhold the last data shred, which carries the key in its tail
        raw_shreds.data.pop();
        Ok(raw_shreds)
    }

    fn decode(&mut self, shreds: ReceivedShreds<'_>) -> Result<(Vec<u8>, RawShreds), DeshredError> {
        let mut raw_shreds = self.0.reconstruct_data(shreds)?;
        // the PETS key is stored directly in the last shred's tail
        let payload = aont_decode(&raw_shreds, |key, _ciphertext| key)?;
        // withhold the last shred again to match the leader's Merkle tree
        raw_shreds.data.pop();
        Ok((payload, raw_shreds))
    }
}

/// The RAONT-RS difference value `key XOR H(ciphertext)`.
///
/// XOR is its own inverse, so this maps key to `cd` when shredding and `cd` back
/// to key when deshredding.
fn difference_value(
    mut key: [u8; cipher::KEY_BYTES],
    ciphertext: &[u8],
) -> [u8; cipher::KEY_BYTES] {
    let h = hash(ciphertext);
    for (k, hb) in key.iter_mut().zip(h.as_ref()) {
        *k ^= hb;
    }
    key
}

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
    payload: &[u8],
    key_material: impl FnOnce([u8; cipher::KEY_BYTES], &[u8]) -> [u8; cipher::KEY_BYTES],
) -> Result<RawShreds, ShredError> {
    let mut buffer = payload.to_vec();
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

/// Recovers the plaintext bytes from an all-or-nothing layout.
///
/// Inverse of [`aont_encode`]: `derive_key` turns the trailing key material and
/// the full ciphertext region back into the symmetric key. `raw_shreds` must
/// contain all [`DATA_SHREDS`] data shreds.
///
/// # Errors
///
/// Returns [`DeshredError::BadEncoding`] if the layout is malformed.
fn aont_decode(
    raw_shreds: &RawShreds,
    derive_key: impl FnOnce([u8; cipher::KEY_BYTES], &[u8]) -> [u8; cipher::KEY_BYTES],
) -> Result<Vec<u8>, DeshredError> {
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

    Ok(buffer)
}
