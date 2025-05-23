// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Cryptographic primitives.
//!
//! This module contains any cryptographic primitives used by the library.

pub mod aggsig;
pub mod hash;
pub mod merkle;
pub mod signature;

pub use aggsig::{AggregateSignature, IndividualSignature};
pub use hash::{Hash, ShortHash, hash};
pub use merkle::MerkleTree;
pub use signature::Signature;

/// A type that can be converted into a byte string to be signed.
///
/// It is important to note that this may well be different from serializing
/// the type to bytes. For example, a type containing a signature can have a
/// `bytes_to_sign` implementation that serializes all fields except the
/// signature. Also, serialization may be implementation-specific (e.g. specific
/// to the storage engine) while `bytes_to_sign` is part of the protocol.
pub trait Signable {
    /// Returns the exact byte string to be signed.
    fn bytes_to_sign(&self) -> Vec<u8>;
}
