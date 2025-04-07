// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use sha2::{Digest, Sha256};

/// Regular hash type that should be used almost always.
pub type Hash = [u8; 32];

/// A short hash that only provides 64 bit resistance against collision attacks.
///
/// It should only ever be used if you are 100% certain that (second) preimage
/// resistance is enough for the use case. Otherwise, use `Hash`.
pub type ShortHash = [u8; 16];

#[must_use]
pub fn hash(data: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

#[must_use]
pub fn truncate(hash: Hash) -> ShortHash {
    hash[..16].try_into().expect("wrong length")
}
