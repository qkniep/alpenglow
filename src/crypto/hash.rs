// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Cryptographic hash function.
//!
//! This module abstratcs the hash function used throughout the entire library.
//! Currently, SHA-256, specifically the implementation from the [`sha2`] crate is used.

use sha2::{Digest, Sha256};
use wincode::{SchemaRead, SchemaWrite};

/// Regular hash that should be used in most cases.
///
/// This provides 256-bit resistance against (second) preimage attacks.
/// It also provides 128-bit resistance against collision attacks.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, SchemaRead, SchemaWrite)]
pub struct Hash(pub(super) [u8; 32]);

impl Hash {
    /// Creates a random hash for testing.
    #[cfg(test)]
    pub fn random_for_test() -> Self {
        let mut bytes = [0; 32];
        rand::RngCore::fill_bytes(&mut rand::rng(), &mut bytes);
        Hash(bytes)
    }
}

impl AsRef<[u8]> for Hash {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl std::hash::Hash for Hash {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write(&self.0);
    }
}

/// Short hash that should be used carefully.
///
/// Usually a regular [`self::Hash`] is what you want.
///
/// This provides up to 128-bit resistance against (second) preimage attacks.
/// However, it provides at most 64-bit resistance against collision attacks.
/// Only use this if you are 100% certain that second preimage resistance is enough!
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct ShortHash([u8; 16]);

impl AsRef<[u8]> for ShortHash {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl std::hash::Hash for ShortHash {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write(&self.0);
    }
}

/// Hashes the given data using SHA-256.
#[must_use]
pub fn hash(data: &[u8]) -> Hash {
    Hash(Sha256::digest(data).into())
}

/// Hashes all the given data concatenated together.
#[must_use]
pub fn hash_all(data: &[&[u8]]) -> Hash {
    let mut hasher = Sha256::new();
    for item in data {
        hasher.update(item);
    }
    Hash(hasher.finalize().into())
}

/// Truncates the given hash into a [`ShortHash`].
#[must_use]
pub fn truncate(hash: Hash) -> ShortHash {
    ShortHash(hash.0[..16].try_into().expect("wrong length"))
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
