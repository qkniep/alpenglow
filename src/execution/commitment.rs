// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Lattice hash commitment over the execution state.
//!
//! [`LtHash`] is a homomorphic, additive hash over a set of state entries:
//! the commitment to a state is the lane-wise wrapping sum of per-entry
//! hashes. This gives O(1) incremental updates: inserting an entry adds its
//! hash to the commitment, removing an entry subtracts it, and updating an
//! entry does both. The commitment is independent of the order in which
//! entries were added or removed, so it commits to the *contents* of a state
//! and nothing else.
//!
//! This is the same construction as the lattice hash used for Solana's
//! accounts hash, instantiated with SHA-256 in counter mode instead of
//! BLAKE3 to avoid an additional dependency. Finding two sets of entries
//! with the same commitment amounts to solving a generalized birthday
//! problem over the 1024 lanes of 16 bits each.
//!
//! For use as a compact wire-format commitment, the full 2048-byte lattice
//! hash is compressed to a 32-byte [`StateCommitment`] via [`LtHash::digest`].
//!
//! # Examples
//!
//! Maintaining a commitment alongside a [`State`]:
//!
//! ```
//! use alpenglow::execution::commitment::LtHash;
//! use alpenglow::execution::state::State;
//!
//! let mut state = State::new();
//! let mut commitment = LtHash::identity();
//!
//! // Apply a write to the state and fold it into the commitment.
//! let (key, value) = ([1; 32], vec![42]);
//! let old = state.insert(key, value.clone());
//! commitment.observe(&key, old.as_deref(), Some(&value));
//!
//! // Remove the entry again: the commitment returns to the identity.
//! let old = state.remove(&key);
//! commitment.observe(&key, old.as_deref(), None);
//! assert_eq!(commitment, LtHash::identity());
//! ```
//!
//! [`State`]: crate::execution::state::State

use std::fmt;
use std::ops::{AddAssign, SubAssign};

use derive_more::{From, Into};
use wincode::{SchemaRead, SchemaWrite};

use crate::crypto::Hash;
use crate::crypto::hash::{hash, hash_all};
use crate::execution::state::Address;

/// Number of 16-bit lanes in a lattice hash.
const NUM_LANES: usize = 1024;

/// Number of lanes filled by a single 32-byte SHA-256 output.
const LANES_PER_BLOCK: usize = 16;

/// Compact wire-format commitment to the contents of an execution state.
///
/// This is the value that crosses from the execution engine into consensus,
/// e.g. to be embedded in blocks or compared across validators. It is a
/// distinct type from other 32-byte hashes (block hashes, Merkle roots) so
/// the different kinds of commitments cannot be mixed up.
///
/// Produced by compressing a full [`LtHash`] via [`LtHash::digest`].
#[repr(transparent)]
#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into, SchemaRead, SchemaWrite,
)]
pub struct StateCommitment(Hash);

/// Homomorphic hash committing to the contents of an execution state.
///
/// See the [module documentation](self) for details.
#[derive(Clone, PartialEq, Eq)]
pub struct LtHash {
    /// Lanes of the lattice hash; arithmetic is lane-wise mod 2^16.
    lanes: [u16; NUM_LANES],
}

impl LtHash {
    /// Returns the identity element, i.e. the commitment to an empty state.
    #[must_use]
    pub const fn identity() -> Self {
        Self {
            lanes: [0; NUM_LANES],
        }
    }

    /// Folds the insertion of an entry into the commitment.
    pub fn add_entry(&mut self, key: &Address, value: &[u8]) {
        *self += &Self::hash_entry(key, value);
    }

    /// Folds the removal of an entry out of the commitment.
    ///
    /// The exact same entry (key and value) must currently be part of the
    /// committed contents, otherwise the commitment loses its meaning.
    pub fn remove_entry(&mut self, key: &Address, value: &[u8]) {
        *self -= &Self::hash_entry(key, value);
    }

    /// Folds a state write into the commitment.
    ///
    /// `old` must be the value previously stored under `key` (`None` if the
    /// key was vacant) and `new` the value now stored (`None` if deleted).
    /// This is exactly the information returned by the write operations on
    /// [`State`](crate::execution::state::State).
    pub fn observe(&mut self, key: &Address, old: Option<&[u8]>, new: Option<&[u8]>) {
        if let Some(old) = old {
            self.remove_entry(key, old);
        }
        if let Some(new) = new {
            self.add_entry(key, new);
        }
    }

    /// Returns the compact [`StateCommitment`] digest of this commitment.
    ///
    /// This is the wire-format value to embed in blocks or compare across
    /// validators; it compresses the full lattice hash with SHA-256.
    #[must_use]
    pub fn digest(&self) -> StateCommitment {
        let mut bytes = [0; NUM_LANES * 2];
        for (chunk, lane) in bytes.chunks_exact_mut(2).zip(&self.lanes) {
            chunk.copy_from_slice(&lane.to_le_bytes());
        }
        StateCommitment(hash(&bytes))
    }

    /// Computes the lattice hash of a single state entry.
    ///
    /// The entry is compressed with SHA-256 and then expanded into the lanes
    /// in counter mode. Since [`Address`]es have a fixed size, the
    /// concatenation `key || value` is injective over entries.
    fn hash_entry(key: &Address, value: &[u8]) -> Self {
        let seed = hash_all(&[key.as_slice(), value]);
        let mut lanes = [0; NUM_LANES];
        for (counter, block_lanes) in lanes.chunks_exact_mut(LANES_PER_BLOCK).enumerate() {
            let block = hash_all(&[seed.as_ref(), &counter.to_le_bytes()]);
            let block_bytes = block.as_ref().chunks_exact(2);
            for (lane, bytes) in block_lanes.iter_mut().zip(block_bytes) {
                *lane = u16::from_le_bytes([bytes[0], bytes[1]]);
            }
        }
        Self { lanes }
    }
}

impl Default for LtHash {
    fn default() -> Self {
        Self::identity()
    }
}

impl AddAssign<&Self> for LtHash {
    /// Combines two commitments into the commitment to the union of their entries.
    fn add_assign(&mut self, rhs: &Self) {
        for (lane, other) in self.lanes.iter_mut().zip(&rhs.lanes) {
            *lane = lane.wrapping_add(*other);
        }
    }
}

impl SubAssign<&Self> for LtHash {
    /// Removes one commitment's entries from another.
    fn sub_assign(&mut self, rhs: &Self) {
        for (lane, other) in self.lanes.iter_mut().zip(&rhs.lanes) {
            *lane = lane.wrapping_sub(*other);
        }
    }
}

impl fmt::Debug for LtHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("LtHash").field(&self.digest()).finish()
    }
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use super::*;
    use crate::execution::state::State;

    /// Returns `count` random (address, value) entries.
    fn random_entries(rng: &mut impl Rng, count: usize) -> Vec<(Address, Vec<u8>)> {
        (0..count)
            .map(|_| {
                let mut key = [0; 32];
                rng.fill_bytes(&mut key);
                let mut value = vec![0; rng.random_range(1..16)];
                rng.fill_bytes(&mut value);
                (key, value)
            })
            .collect()
    }

    #[test]
    fn identity_is_default() {
        assert_eq!(LtHash::identity(), LtHash::default());
    }

    #[test]
    fn add_remove_returns_to_identity() {
        let mut rng = rand::rng();
        let entries = random_entries(&mut rng, 10);

        let mut lthash = LtHash::identity();
        for (key, value) in &entries {
            lthash.add_entry(key, value);
        }
        assert_ne!(lthash, LtHash::identity());

        // Removing all entries again (in a different order) returns to the identity.
        for (key, value) in entries.iter().rev() {
            lthash.remove_entry(key, value);
        }
        assert_eq!(lthash, LtHash::identity());
    }

    #[test]
    fn order_independent() {
        let mut rng = rand::rng();
        let entries = random_entries(&mut rng, 10);

        let mut forward = LtHash::identity();
        for (key, value) in &entries {
            forward.add_entry(key, value);
        }
        let mut backward = LtHash::identity();
        for (key, value) in entries.iter().rev() {
            backward.add_entry(key, value);
        }
        assert_eq!(forward, backward);
        assert_eq!(forward.digest(), backward.digest());
    }

    #[test]
    fn distinct_contents_distinct_commitments() {
        let mut rng = rand::rng();
        let entries = random_entries(&mut rng, 4);

        // Build the commitment to every subset of the entries.
        let mut digests = Vec::new();
        for subset in 0_u32..(1 << entries.len()) {
            let mut lthash = LtHash::identity();
            for (i, (key, value)) in entries.iter().enumerate() {
                if subset & (1 << i) != 0 {
                    lthash.add_entry(key, value);
                }
            }
            digests.push(lthash.digest());
        }

        // All subsets must have distinct digests.
        let count = digests.len();
        digests.sort_unstable();
        digests.dedup();
        assert_eq!(digests.len(), count);
    }

    #[test]
    fn observe_is_remove_then_add() {
        let mut rng = rand::rng();
        let mut key = [0; 32];
        rng.fill_bytes(&mut key);
        let (old_value, new_value) = ([1_u8, 2, 3], [4_u8, 5]);

        let mut base = LtHash::identity();
        for (key, value) in &random_entries(&mut rng, 5) {
            base.add_entry(key, value);
        }
        base.add_entry(&key, &old_value);

        // Observing an update is the same as removing the old entry and
        // adding the new one.
        let mut via_observe = base.clone();
        via_observe.observe(&key, Some(&old_value), Some(&new_value));
        let mut manual = base.clone();
        manual.remove_entry(&key, &old_value);
        manual.add_entry(&key, &new_value);
        assert_eq!(via_observe, manual);

        // Observing with neither old nor new value is a no-op.
        let mut noop = base.clone();
        noop.observe(&key, None, None);
        assert_eq!(noop, base);
    }

    #[test]
    fn combining_commitments_is_additive() {
        let mut rng = rand::rng();
        let entries_a = random_entries(&mut rng, 5);
        let entries_b = random_entries(&mut rng, 5);

        let mut lthash_a = LtHash::identity();
        for (key, value) in &entries_a {
            lthash_a.add_entry(key, value);
        }
        let mut lthash_b = LtHash::identity();
        for (key, value) in &entries_b {
            lthash_b.add_entry(key, value);
        }
        let mut lthash_union = LtHash::identity();
        for (key, value) in entries_a.iter().chain(&entries_b) {
            lthash_union.add_entry(key, value);
        }

        // Commitments of disjoint sets combine by addition into the
        // commitment of their union.
        let mut combined = lthash_a.clone();
        combined += &lthash_b;
        assert_eq!(combined, lthash_union);

        // And subtracting one part yields back the other.
        combined -= &lthash_a;
        assert_eq!(combined, lthash_b);
    }

    #[test]
    fn incremental_matches_recomputed() {
        let mut rng = rand::rng();
        let mut state = State::new();
        let mut commitment = LtHash::identity();

        // Apply random inserts, updates, and removals to the state, keeping
        // the commitment in sync via `observe`.
        let keys: Vec<Address> = random_entries(&mut rng, 16)
            .into_iter()
            .map(|(key, _)| key)
            .collect();
        for _ in 0..100 {
            let key = keys[rng.random_range(0..keys.len())];
            if rng.random_bool(0.7) {
                let mut value = vec![0; rng.random_range(1..16)];
                rng.fill_bytes(&mut value);
                let old = state.insert(key, value.clone());
                commitment.observe(&key, old.as_deref(), Some(&value));
            } else {
                let old = state.remove(&key);
                commitment.observe(&key, old.as_deref(), None);
            }
        }

        // The incrementally maintained commitment matches one recomputed
        // from scratch over the final contents of the state.
        let mut recomputed = LtHash::identity();
        for (key, value) in &state {
            recomputed.add_entry(key, value);
        }
        assert_eq!(commitment, recomputed);
        assert_eq!(commitment.digest(), recomputed.digest());
    }
}
