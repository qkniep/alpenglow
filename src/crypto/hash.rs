// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Cryptographic hash function.
//!
//! This module abstratcs the specific cryptographic hash function used
//! throughout the entire library. Currently, SHA-256 is used.

use std::fmt::Display;

use serde::{Deserialize, Serialize};
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

#[derive(PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Debug, Serialize, Deserialize)]
pub struct BlockHash(Hash);

impl BlockHash {
    pub(super) fn new(hash: Hash) -> Self {
        Self(hash)
    }

    pub fn genesis() -> Self {
        Self(Hash::default())
    }

    pub fn inner(&self) -> Hash {
        self.0
    }

    #[cfg(test)]
    pub fn new_random() -> Self {
        use rand::RngCore;

        let mut hash = Hash::default();
        rand::rng().fill_bytes(&mut hash);
        Self(hash)
    }
}

impl Display for BlockHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", hex::encode(&self.0[..8]))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    const HASH_ITERATIONS: u64 = 100_000;

    #[test]
    fn deterministic() {
        let hash1 = hash(&[0; 32]);
        let hash2 = hash(&[0; 32]);
        assert_eq!(hash1, hash2);

        for i in 0..HASH_ITERATIONS {
            let bytes = i.to_be_bytes();
            let hash1 = hash(&bytes);
            let hash2 = hash(&bytes);
            assert_eq!(hash1, hash2);
        }
    }

    #[test]
    fn unique() {
        let hash1 = hash(&[0; 16]);
        let hash2 = hash(&[0; 32]);
        assert_ne!(hash1, hash2);

        // should find no duplicate hashes
        let unique_hashes = (0..HASH_ITERATIONS)
            .map(|i| {
                let bytes = i.to_be_bytes();
                hash(&bytes)
            })
            .collect::<HashSet<_>>()
            .len();
        assert_eq!(unique_hashes as u64, HASH_ITERATIONS);

        // should find no duplicate truncated hashes
        let unique_hashes = (0..HASH_ITERATIONS)
            .map(|i| {
                let bytes = i.to_be_bytes();
                truncate(hash(&bytes))
            })
            .collect::<HashSet<_>>()
            .len();
        assert_eq!(unique_hashes as u64, HASH_ITERATIONS);
    }

    #[test]
    fn concatenation() {
        let hash_direct = hash(&[[0; 32], [1; 32]].concat());
        let hash_all_1 = hash_all(&[&[0; 32], &[1; 32]]);
        let hash_all_2 = hash_all(&[&[0; 16], &[0; 16], &[1; 16], &[1; 16]]);
        assert_eq!(hash_all_1, hash_direct);
        assert_eq!(hash_all_2, hash_direct);
    }
}
