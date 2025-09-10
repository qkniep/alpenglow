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
//! It also uses the [`Slice`] struct defined in the [`crate::slice`] module.

mod reed_solomon;
mod validated_shred;

use aes::Aes128;
use aes::cipher::{Array, KeyIvInit, StreamCipher};
use ctr::Ctr64LE;
use rand::{RngCore, rng};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use self::reed_solomon::{
    ReedSolomonDeshredError, ReedSolomonShredError, reed_solomon_deshred, reed_solomon_shred,
};
pub use self::validated_shred::{ShredVerifyError, ValidatedShred};
use crate::crypto::signature::{SecretKey, Signature};
use crate::crypto::{Hash, MerkleTree, hash};
use crate::types::{Slice, SliceHeader};

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
    #[error("more shreds than expected")]
    TooManyShreds,
    #[error("shreds are part of invalid Merkle tree")]
    InvalidMerkleTree,
}

impl From<ReedSolomonDeshredError> for DeshredError {
    fn from(err: ReedSolomonDeshredError) -> Self {
        match err {
            ReedSolomonDeshredError::TooMuchData => Self::TooMuchData,
            ReedSolomonDeshredError::NotEnoughShreds => Self::NotEnoughShreds,
            ReedSolomonDeshredError::TooManyShreds => Self::TooManyShreds,
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
    /// Verifies only the Merkle proof of this shred.
    ///
    /// For full verification, see [`ValidatedShred::new`].
    ///
    /// Returns `true` iff the Merkle root matches the given root and the proof is valid.
    #[must_use]
    pub fn verify_path_only(&self, root: &Hash) -> bool {
        if &self.merkle_root != root {
            return false;
        }
        MerkleTree::check_proof(
            &self.payload().data,
            self.payload().index_in_slice,
            self.merkle_root,
            &self.merkle_path,
        )
    }

    pub const fn payload(&self) -> &ShredPayload {
        match &self.payload_type {
            ShredPayloadType::Coding(p) | ShredPayloadType::Data(p) => p,
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
    /// Slice header replicated in each shred.
    pub(crate) header: SliceHeader,
    /// Index of this shred within the slice.
    pub(crate) index_in_slice: usize,
    /// Raw payload bytes of this shred, part of the erasure-coded slice payload.
    pub(crate) data: bytes::Bytes,
}

impl ShredPayload {
    /// Returns the index of this shred within the entire slot.
    #[must_use]
    pub fn index_in_slot(&self) -> usize {
        self.header.slice_index.inner() * TOTAL_SHREDS + self.index_in_slice
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
    /// - Should always return [`ShredError::TooMuchData`] if the `slice` is
    ///   too big, i.e., more than [`Shredder::MAX_DATA_SIZE`] bytes.
    fn shred(slice: Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredError>;

    /// Puts the given shreds back together into a complete slice.
    ///
    /// Additionally, outputs all `TOTAL_SHREDS` reconstructed shreds.
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
    fn deshred(shreds: &[Shred]) -> Result<(Slice, Vec<Shred>), DeshredError>;
}

/// A shredder that augments the [`DATA_SHREDS`] data shreds with
/// `TOTAL_SHREDS - DATA_SHREDS` coding shreds and outputs both.
pub struct RegularShredder;

impl Shredder for RegularShredder {
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE;

    fn shred(slice: Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredError> {
        let (header, payload) = slice.deconstruct();
        let (data, coding) = reed_solomon_shred(
            header,
            payload.into(),
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS,
        )?;
        Ok(data_and_coding_to_output_shreds(data, coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<(Slice, Vec<Shred>), DeshredError> {
        let payload =
            reed_solomon_deshred(shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS, DATA_SHREDS)?;
        let slice = Slice::from_shreds(payload.into(), &shreds[0]);

        // additional Merkle tree validity check
        let merkle_root = shreds[0].merkle_root;
        let (header, payload) = slice.clone().deconstruct();
        let (data, coding) = reed_solomon_shred(
            header,
            payload.into(),
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS,
        )?;
        let tree = build_merkle_tree(&data, &coding);
        if tree.get_root() != merkle_root {
            return Err(DeshredError::InvalidMerkleTree);
        }

        // turn reconstructed shreds into output shreds (with root, path, sig)
        let leader_sig = shreds[0].merkle_root_sig;
        let reconstructed_shreds =
            create_output_shreds_for_other_leader(data, coding, tree, leader_sig);

        Ok((slice, reconstructed_shreds))
    }
}

/// A shredder that only produces [`TOTAL_SHREDS`] coding shreds.
pub struct CodingOnlyShredder;

impl Shredder for CodingOnlyShredder {
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE;

    fn shred(slice: Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredError> {
        let (header, payload) = slice.deconstruct();
        let (_data, coding) =
            reed_solomon_shred(header, payload.into(), DATA_SHREDS, TOTAL_SHREDS)?;
        Ok(data_and_coding_to_output_shreds(vec![], coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<(Slice, Vec<Shred>), DeshredError> {
        let payload = reed_solomon_deshred(shreds, DATA_SHREDS, TOTAL_SHREDS, 0)?;
        let slice = Slice::from_shreds(payload.into(), &shreds[0]);

        // additional Merkle tree validity check
        let merkle_root = shreds[0].merkle_root;
        let (header, payload) = slice.clone().deconstruct();
        let (_, coding) = reed_solomon_shred(header, payload.into(), DATA_SHREDS, TOTAL_SHREDS)?;
        let tree = build_merkle_tree(&[], &coding);
        if tree.get_root() != merkle_root {
            return Err(DeshredError::InvalidMerkleTree);
        }

        // turn reconstructed shreds into output shreds (with root, path, sig)
        let leader_sig = shreds[0].merkle_root_sig;
        let reconstructed_shreds =
            create_output_shreds_for_other_leader(Vec::new(), coding, tree, leader_sig);

        Ok((slice, reconstructed_shreds))
    }
}

/// A shredder that uses the PETS all-or-nothing construction.
///
/// It outputs `DATA_SHREDS-1` encrypted data shreds and
/// `TOTAL_SHREDS - DATA_SHREDS + 1` coding shreds.
///
/// See also: <https://arxiv.org/abs/2502.02774>
pub struct PetsShredder;

impl Shredder for PetsShredder {
    // needs 16 bytes for symmmetric encryption key
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE - 16;

    fn shred(slice: Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredError> {
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
        let (mut data, coding) =
            reed_solomon_shred(header, payload, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS + 1)?;
        // delete data shred containing key
        data.pop();

        Ok(data_and_coding_to_output_shreds(data, coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<(Slice, Vec<Shred>), DeshredError> {
        let mut buffer = reed_solomon_deshred(
            shreds,
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS + 1,
            DATA_SHREDS - 1,
        )?;
        if buffer.len() < 16 {
            return Err(DeshredError::BadEncoding);
        }

        // additional Merkle tree validity check
        let merkle_root = shreds[0].merkle_root;
        let header = shreds[0].payload().header.clone();
        let (mut data, coding) = reed_solomon_shred(
            header,
            buffer.clone(),
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS + 1,
        )?;
        data.pop();
        let tree = build_merkle_tree(&data, &coding);
        if tree.get_root() != merkle_root {
            return Err(DeshredError::InvalidMerkleTree);
        }

        // decrypt slice
        let tail = buffer.split_off(buffer.len() - 16);
        let iv = Array::from([0u8; 16]);
        let key = Array::try_from(tail.as_slice()).expect("tail should have correct length");

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut buffer);
        let slice = Slice::from_shreds(buffer.into(), &shreds[0]);

        // turn reconstructed shreds into output shreds (with root, path, sig)
        let leader_sig = shreds[0].merkle_root_sig;
        let reconstructed_shreds =
            create_output_shreds_for_other_leader(Vec::new(), coding, tree, leader_sig);

        Ok((slice, reconstructed_shreds))
    }
}

/// A shredder that uses the RAONT-RS all-or-nothing construction.
///
/// It outputs [`DATA_SHREDS`] encrypted data shreds and
/// `TOTAL_SHREDS - DATA_SHREDS` coding shreds.
///
/// See also: <https://eprint.iacr.org/2016/1014>
pub struct AontShredder;

impl Shredder for AontShredder {
    // needs 16 bytes for symmmetric encryption key
    const MAX_DATA_SIZE: usize = MAX_DATA_PER_SLICE - 16;

    fn shred(slice: Slice, sk: &SecretKey) -> Result<Vec<Shred>, ShredError> {
        let (header, payload) = slice.deconstruct();
        let mut payload: Vec<u8> = payload.into();
        assert!(payload.len() <= Self::MAX_DATA_SIZE);

        let mut rng = rng();
        let mut key = Array::from([0; 16]);
        rng.fill_bytes(&mut key);
        let iv = Array::from([0u8; 16]);

        let mut cipher = Ctr64LE::<Aes128>::new(&key, &iv);
        cipher.apply_keystream(&mut payload);

        let hash = hash(&payload);
        for i in 0..16 {
            payload.push(hash[i] ^ key[i]);
        }

        let (data, coding) =
            reed_solomon_shred(header, payload, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS)?;
        Ok(data_and_coding_to_output_shreds(data, coding, sk))
    }

    fn deshred(shreds: &[Shred]) -> Result<(Slice, Vec<Shred>), DeshredError> {
        let mut buffer =
            reed_solomon_deshred(shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS, DATA_SHREDS)?;
        if buffer.len() < 16 {
            return Err(DeshredError::BadEncoding);
        }

        // additional Merkle tree validity check
        let merkle_root = shreds[0].merkle_root;
        let header = shreds[0].payload().header.clone();
        let (data, coding) = reed_solomon_shred(
            header,
            buffer.clone(),
            DATA_SHREDS,
            TOTAL_SHREDS - DATA_SHREDS,
        )?;
        let tree = build_merkle_tree(&data, &coding);
        if tree.get_root() != merkle_root {
            return Err(DeshredError::InvalidMerkleTree);
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
        let slice = Slice::from_shreds(buffer.into(), &shreds[0]);

        // turn reconstructed shreds into output shreds (with root, path, sig)
        let leader_sig = shreds[0].merkle_root_sig;
        let reconstructed_shreds =
            create_output_shreds_for_other_leader(Vec::new(), coding, tree, leader_sig);

        Ok((slice, reconstructed_shreds))
    }
}

/// Generates the Merkle tree, signs the root, and outputs shreds.
///
/// Each returned shred contains the Merkle root, its own path and the signature.
pub fn data_and_coding_to_output_shreds(
    data: Vec<DataShred>,
    coding: Vec<CodingShred>,
    sk: &SecretKey,
) -> Vec<Shred> {
    let mut shreds = Vec::with_capacity(data.len() + coding.len());
    let num_data_shreds = data.len();

    let tree = build_merkle_tree(&data, &coding);
    let merkle_root = tree.get_root();
    let sig = sk.sign(&merkle_root);

    for d in data {
        let merkle_path = tree.create_proof(d.0.index_in_slice);
        shreds.push(Shred {
            payload_type: ShredPayloadType::Data(d.0),
            merkle_root,
            merkle_root_sig: sig,
            merkle_path,
        });
    }
    for mut c in coding {
        c.0.index_in_slice += num_data_shreds;
        let merkle_path = tree.create_proof(c.0.index_in_slice);
        shreds.push(Shred {
            payload_type: ShredPayloadType::Coding(c.0),
            merkle_root,
            merkle_root_sig: sig,
            merkle_path,
        });
    }

    shreds
}

/// Puts the root, path, and signature of the leader into shreds.
///
/// This is analogous to [`data_and_coding_to_output_shreds`], but for another leader.
/// Instead of signing the root, copies the existing signature from another shred.
/// Also, requires the Merkle tree to already be calculated from reconstructed shreds.
///
/// Each returned shred contains the Merkle root, its own path and the signature.
pub fn create_output_shreds_for_other_leader(
    data: Vec<DataShred>,
    coding: Vec<CodingShred>,
    tree: MerkleTree,
    leader_signature: Signature,
) -> Vec<Shred> {
    let mut shreds = Vec::with_capacity(data.len() + coding.len());
    let num_data_shreds = data.len();
    let merkle_root = tree.get_root();

    for d in data {
        let merkle_path = tree.create_proof(d.0.index_in_slice);
        shreds.push(Shred {
            payload_type: ShredPayloadType::Data(d.0),
            merkle_root,
            merkle_root_sig: leader_signature,
            merkle_path,
        });
    }
    for mut c in coding {
        c.0.index_in_slice += num_data_shreds;
        let merkle_path = tree.create_proof(c.0.index_in_slice);
        shreds.push(Shred {
            payload_type: ShredPayloadType::Coding(c.0),
            merkle_root,
            merkle_root_sig: leader_signature,
            merkle_path,
        });
    }

    shreds
}

/// Builds the Merkle tree for a slice, where the leaves are the given shreds.
fn build_merkle_tree(data_shreds: &[DataShred], coding_shreds: &[CodingShred]) -> MerkleTree {
    // zero-allocation chaining of slices
    let leaves = data_shreds
        .iter()
        .map(|d| d.0.data.as_ref())
        .chain(coding_shreds.iter().map(|c| c.0.data.as_ref()));
    MerkleTree::new_from_iter(leaves)
}

#[cfg(test)]
mod tests {
    use color_eyre::Result;

    use super::*;
    use crate::types::slice::create_slice_with_invalid_txs;

    #[test]
    fn regular_shredding() -> Result<()> {
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let shreds = RegularShredder::shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let (slice_restored, _) = RegularShredder::deshred(&shreds)?;
        slice.merkle_root = slice_restored.merkle_root;
        assert_eq!(slice_restored, slice);

        // restore only from coding shreds
        let (slice_restored, _) = RegularShredder::deshred(&shreds[..DATA_SHREDS])?;
        assert_eq!(slice_restored, slice);

        // restore only from data shreds
        let (slice_restored, _) = RegularShredder::deshred(&shreds[DATA_SHREDS..])?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let (slice_restored, _) = RegularShredder::deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let (slice_restored, _) = RegularShredder::deshred(&shreds[start..end])?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let (slice_restored, _) = RegularShredder::deshred(&shreds[1..])?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let result = RegularShredder::deshred(&shreds[..1]);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        // cannot restore from too few shreds
        let result = RegularShredder::deshred(&shreds[..DATA_SHREDS - 1]);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn coding_only_shredding() -> Result<()> {
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
        let shreds = CodingOnlyShredder::shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let (slice_restored, _) = CodingOnlyShredder::deshred(&shreds)?;
        slice.merkle_root = slice_restored.merkle_root;
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let (slice_restored, _) = CodingOnlyShredder::deshred(&shreds[..DATA_SHREDS])?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let (slice_restored, _) = CodingOnlyShredder::deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let (slice_restored, _) = CodingOnlyShredder::deshred(&shreds[1..])?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let result = CodingOnlyShredder::deshred(&shreds[..1]);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        // cannot restore from too few shreds
        let result = CodingOnlyShredder::deshred(&shreds[..DATA_SHREDS - 1]);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn aont_shredding() -> Result<()> {
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let shreds = AontShredder::shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let (slice_restored, _) = AontShredder::deshred(&shreds)?;
        slice.merkle_root = slice_restored.merkle_root;
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let (slice_restored, _) = AontShredder::deshred(&shreds[..DATA_SHREDS])?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let (slice_restored, _) = AontShredder::deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let (slice_restored, _) = AontShredder::deshred(&shreds[start..end])?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let (slice_restored, _) = AontShredder::deshred(&shreds[1..])?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let result = AontShredder::deshred(&shreds[..1]);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        // cannot restore from too few shreds
        let result = AontShredder::deshred(&shreds[..DATA_SHREDS - 1]);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        Ok(())
    }

    #[test]
    fn pets_shredding() -> Result<()> {
        let sk = SecretKey::new(&mut rng());
        let mut slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let shreds = PetsShredder::shred(slice.clone(), &sk)?;
        assert_eq!(shreds.len(), TOTAL_SHREDS);

        // restore from all shreds
        let (slice_restored, _) = PetsShredder::deshred(&shreds)?;
        slice.merkle_root = slice_restored.merkle_root;
        assert_eq!(slice_restored, slice);

        // restore from just enough shreds
        let (slice_restored, _) = PetsShredder::deshred(&shreds[..DATA_SHREDS])?;
        assert_eq!(slice_restored, slice);

        // restore from non-consecutive shreds
        let nc_shreds = [&shreds[..1], &shreds[DATA_SHREDS + 1..]].concat();
        let (slice_restored, _) = PetsShredder::deshred(&nc_shreds)?;
        assert_eq!(slice_restored, slice);

        // restore from half coding / half data shreds
        let start = DATA_SHREDS / 2;
        let end = DATA_SHREDS / 2 + DATA_SHREDS;
        let (slice_restored, _) = PetsShredder::deshred(&shreds[start..end])?;
        assert_eq!(slice_restored, slice);

        // restore from all but one shred
        let (slice_restored, _) = PetsShredder::deshred(&shreds[1..])?;
        assert_eq!(slice_restored, slice);

        // cannot restore from one shred
        let result = PetsShredder::deshred(&shreds[..1]);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        // cannot restore from too few shreds
        let result = PetsShredder::deshred(&shreds[..DATA_SHREDS - 1]);
        assert_eq!(result.err(), Some(DeshredError::NotEnoughShreds));

        Ok(())
    }
}
