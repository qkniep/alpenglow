// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Cryptographic hash function.
//!
//! This module abstratcs the specific cryptographic hash function used
//! throughout the entire library. Currently, SHA-256 is used.

use sha2::{Digest, Sha256};

/// Regular hash type that should be used almost always.
pub type Hash = [u8; 32];

/// A short hash that only provides 64 bit resistance against collision attacks.
///
/// It should only ever be used if you are 100% certain that (second) preimage
/// resistance is enough for the use case. Otherwise, use `Hash`.
pub type ShortHash = [u8; 16];

/// Hashes the given data using SHA-256.
#[must_use]
pub fn hash(data: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

/// Truncates the given hash to a shorter 128-bit hash.
#[must_use]
pub fn truncate(hash: Hash) -> ShortHash {
    hash[..16].try_into().expect("wrong length")
}
