// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Cryptographic hash function.
//!
//! This module abstratcs the specific cryptographic hash function used
//! throughout the entire library. Currently, SHA-256 is used.

use sha2::{Digest, Sha256};

/// Regular hash that should be used in most cases.
///
/// This provides 256-bit resistance against (second) preimage attacks
/// and 128-bit resistance against collision attacks.
pub type Hash = [u8; 32];

/// Short hash that should be used carefully.
///
/// It provides 128-bit resistance agains (second) preimage attacks,
/// but only provides 64-bit resistance against collision attacks.
/// Only use this if you are 100% certain that (second) preimage
/// resistance is enough for the use case. Otherwise, use `Hash`.
pub type ShortHash = [u8; 16];

/// Hashes the given data using SHA-256.
#[must_use]
pub fn hash(data: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

/// Hashes all the given data slices together using SHA-256.
#[must_use]
pub fn hash_all(data: &[&[u8]]) -> Hash {
    let mut hasher = Sha256::new();
    for item in data {
        hasher.update(item);
    }
    hasher.finalize().into()
}

/// Truncates the given hash into a [`ShortHash`].
#[must_use]
pub fn truncate(hash: Hash) -> ShortHash {
    hash[..16].try_into().expect("wrong length")
}
