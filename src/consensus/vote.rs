// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Vote types used for the consensus protocol.
//!
//! Each vote kind is represented by its own concrete struct:
//! - [`NotarVote`]
//! - [`NotarFallbackVote`]
//! - [`SkipVote`]
//! - [`SkipFallbackVote`]
//! - [`FinalVote`]
//!
//! The [`Vote`] enum is a sum type over all these vote kinds.

use wincode::{SchemaRead, SchemaWrite};

use crate::crypto::aggsig::{PublicKey, SecretKey};
use crate::crypto::merkle::BlockHash;
use crate::crypto::{IndividualSignature, Signable};
use crate::{Slot, ValidatorId};

/// Payload used internally for computing bytes to sign for a vote.
///
/// This type is intentionally not part of the public API.
/// Each typed vote struct signs the corresponding `VoteKind` variant.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub(crate) enum VoteKind {
    /// A notarization vote for a given block hash in a given slot.
    Notar(Slot, BlockHash),
    /// A notar-fallback vote for a given block hash in a given slot.
    NotarFallback(Slot, BlockHash),
    /// A skip vote for a given slot.
    Skip(Slot),
    /// A fast finalization vote for a given slot.
    SkipFallback(Slot),
    /// A finalization vote for a given slot.
    Final(Slot),
}

impl Signable for VoteKind {
    fn bytes_to_sign(&self) -> Vec<u8> {
        wincode::serialize(self).expect("serialization should not panic")
    }
}

/// Trait for signed typed votes, providing access to signature and signer.
///
/// Implemented by all concrete vote structs to enable generic certificate aggregation.
pub(crate) trait SignedVote {
    fn sig(&self) -> &IndividualSignature;
    fn signer(&self) -> ValidatorId;
}

/// A signed notarization vote.
///
/// This vote is cast immediately after obtaining a valid block.
/// With synchronous execution, this is only after successful execution.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct NotarVote {
    slot: Slot,
    block_hash: BlockHash,
    sig: IndividualSignature,
    signer: ValidatorId,
}

impl NotarVote {
    /// Creates a new notarization vote.
    #[must_use]
    pub fn new(slot: Slot, block_hash: BlockHash, sk: &SecretKey, signer: ValidatorId) -> Self {
        let kind = VoteKind::Notar(slot, block_hash.clone());
        let sig = sk.sign(&kind.bytes_to_sign());
        Self {
            slot,
            block_hash,
            sig,
            signer,
        }
    }

    /// Returns the slot this vote is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        self.slot
    }

    /// Returns the block hash this vote is for.
    #[must_use]
    pub const fn block_hash(&self) -> &BlockHash {
        &self.block_hash
    }

    /// Checks whether this vote's signature is valid under the given public key.
    #[must_use]
    pub fn check_sig(&self, pk: &PublicKey) -> bool {
        let msg = VoteKind::Notar(self.slot, self.block_hash.clone()).bytes_to_sign();
        self.sig.verify(&msg, pk)
    }
}

impl SignedVote for NotarVote {
    fn sig(&self) -> &IndividualSignature {
        &self.sig
    }

    fn signer(&self) -> ValidatorId {
        self.signer
    }
}

/// A signed notar-fallback vote.
///
/// This vote is only cast after the validator initially:
/// - cast a [`SkipVote`], OR
/// - cast a [`NotarVote`] for a different block.
///
/// Requires the validator to see:
/// - 40% notar votes for the block, OR
/// - 60% skip votes + notar votes for the block, 20% of which are notar votes.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct NotarFallbackVote {
    slot: Slot,
    block_hash: BlockHash,
    sig: IndividualSignature,
    signer: ValidatorId,
}

impl NotarFallbackVote {
    /// Creates a new notar-fallback vote.
    #[must_use]
    pub fn new(slot: Slot, block_hash: BlockHash, sk: &SecretKey, signer: ValidatorId) -> Self {
        let kind = VoteKind::NotarFallback(slot, block_hash.clone());
        let sig = sk.sign(&kind.bytes_to_sign());
        Self {
            slot,
            block_hash,
            sig,
            signer,
        }
    }

    /// Returns the slot this vote is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        self.slot
    }

    /// Returns the block hash this vote is for.
    #[must_use]
    pub const fn block_hash(&self) -> &BlockHash {
        &self.block_hash
    }

    /// Checks whether this vote's signature is valid under the given public key.
    #[must_use]
    pub fn check_sig(&self, pk: &PublicKey) -> bool {
        let msg = VoteKind::NotarFallback(self.slot, self.block_hash.clone()).bytes_to_sign();
        self.sig.verify(&msg, pk)
    }
}

impl SignedVote for NotarFallbackVote {
    fn sig(&self) -> &IndividualSignature {
        &self.sig
    }

    fn signer(&self) -> ValidatorId {
        self.signer
    }
}

/// A signed skip vote.
///
/// This vote is cast when seeing an invalid block or timing out on a slot.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct SkipVote {
    slot: Slot,
    sig: IndividualSignature,
    signer: ValidatorId,
}

impl SkipVote {
    /// Creates a new skip vote.
    #[must_use]
    pub fn new(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        let kind = VoteKind::Skip(slot);
        let sig = sk.sign(&kind.bytes_to_sign());
        Self { slot, sig, signer }
    }

    /// Returns the slot this vote is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        self.slot
    }

    /// Checks whether this vote's signature is valid under the given public key.
    #[must_use]
    pub fn check_sig(&self, pk: &PublicKey) -> bool {
        let msg = VoteKind::Skip(self.slot).bytes_to_sign();
        self.sig.verify(&msg, pk)
    }
}

impl SignedVote for SkipVote {
    fn sig(&self) -> &IndividualSignature {
        &self.sig
    }

    fn signer(&self) -> ValidatorId {
        self.signer
    }
}

/// A signed skip-fallback vote.
///
/// This vote is only cast after the validator initially cast a [`NotarVote`].
///
/// Requires the validator to see `skip + sum_notar - max_notar` >= 40%, where:
/// - `skip` is the total stake of skip votes,
/// - `sum_notar` is the total stake of notar votes, and
/// - `max_notar` is the stake of notar votes for the most notarized block.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct SkipFallbackVote {
    slot: Slot,
    sig: IndividualSignature,
    signer: ValidatorId,
}

impl SkipFallbackVote {
    /// Creates a new skip-fallback vote.
    #[must_use]
    pub fn new(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        let kind = VoteKind::SkipFallback(slot);
        let sig = sk.sign(&kind.bytes_to_sign());
        Self { slot, sig, signer }
    }

    /// Returns the slot this vote is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        self.slot
    }

    /// Checks whether this vote's signature is valid under the given public key.
    #[must_use]
    pub fn check_sig(&self, pk: &PublicKey) -> bool {
        let msg = VoteKind::SkipFallback(self.slot).bytes_to_sign();
        self.sig.verify(&msg, pk)
    }
}

impl SignedVote for SkipFallbackVote {
    fn sig(&self) -> &IndividualSignature {
        &self.sig
    }

    fn signer(&self) -> ValidatorId {
        self.signer
    }
}

/// A signed finalization vote.
///
/// This vote is cast when a notarization certificate has been seen for a block.
///
/// Requires that the validator:
/// - previously voted notar on the block, AND
/// - did NOT previously vote skip, skip-fallback, or notar-fallback.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct FinalVote {
    slot: Slot,
    sig: IndividualSignature,
    signer: ValidatorId,
}

impl FinalVote {
    /// Creates a new finalization vote.
    #[must_use]
    pub fn new(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        let kind = VoteKind::Final(slot);
        let sig = sk.sign(&kind.bytes_to_sign());
        Self { slot, sig, signer }
    }

    /// Returns the slot this vote is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        self.slot
    }

    /// Checks whether this vote's signature is valid under the given public key.
    #[must_use]
    pub fn check_sig(&self, pk: &PublicKey) -> bool {
        let msg = VoteKind::Final(self.slot).bytes_to_sign();
        self.sig.verify(&msg, pk)
    }
}

impl SignedVote for FinalVote {
    fn sig(&self) -> &IndividualSignature {
        &self.sig
    }

    fn signer(&self) -> ValidatorId {
        self.signer
    }
}

/// A signed vote in consensus.
///
/// This is a sum type over all concrete vote kinds:
/// - [`NotarVote`]
/// - [`NotarFallbackVote`]
/// - [`SkipVote`]
/// - [`SkipFallbackVote`]
/// - [`FinalVote`]
///
/// Use this type in contexts where a generic vote is required,
/// such as when receiving a vote over the network or re-broadcasting during standstill recovery.
/// For type-safe storage or certificate construction, prefer the concrete vote types.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub enum Vote {
    /// A notarization vote.
    Notar(NotarVote),
    /// A notar-fallback vote.
    NotarFallback(NotarFallbackVote),
    /// A skip vote.
    Skip(SkipVote),
    /// A skip-fallback vote.
    SkipFallback(SkipFallbackVote),
    /// A finalization vote.
    Final(FinalVote),
}

impl Vote {
    /// Creates a new notarization vote.
    #[must_use]
    pub fn new_notar(
        slot: Slot,
        block_hash: BlockHash,
        sk: &SecretKey,
        signer: ValidatorId,
    ) -> Self {
        Self::Notar(NotarVote::new(slot, block_hash, sk, signer))
    }

    /// Creates a new notar-fallback vote.
    #[must_use]
    pub fn new_notar_fallback(
        slot: Slot,
        block_hash: BlockHash,
        sk: &SecretKey,
        signer: ValidatorId,
    ) -> Self {
        Self::NotarFallback(NotarFallbackVote::new(slot, block_hash, sk, signer))
    }

    /// Creates a new skip vote.
    #[must_use]
    pub fn new_skip(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        Self::Skip(SkipVote::new(slot, sk, signer))
    }

    /// Creates a new skip-fallback vote.
    #[must_use]
    pub fn new_skip_fallback(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        Self::SkipFallback(SkipFallbackVote::new(slot, sk, signer))
    }

    /// Creates a new finalization vote.
    #[must_use]
    pub fn new_final(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        Self::Final(FinalVote::new(slot, sk, signer))
    }

    /// Checks whether this vote's signature is valid under the given public key.
    #[must_use]
    #[hotpath::measure]
    pub fn check_sig(&self, pk: &PublicKey) -> bool {
        match self {
            Self::Notar(v) => v.check_sig(pk),
            Self::NotarFallback(v) => v.check_sig(pk),
            Self::Skip(v) => v.check_sig(pk),
            Self::SkipFallback(v) => v.check_sig(pk),
            Self::Final(v) => v.check_sig(pk),
        }
    }

    /// Returns the slot number this vote corresponds to.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        match self {
            Self::Notar(v) => v.slot,
            Self::NotarFallback(v) => v.slot,
            Self::Skip(v) => v.slot,
            Self::SkipFallback(v) => v.slot,
            Self::Final(v) => v.slot,
        }
    }

    /// Returns the block hash this vote corresponds to, if any.
    ///
    /// Returns `None` for skip(-fallback) and finalization votes.
    #[must_use]
    pub const fn block_hash(&self) -> Option<&BlockHash> {
        match self {
            Self::Notar(v) => Some(&v.block_hash),
            Self::NotarFallback(v) => Some(&v.block_hash),
            Self::Skip(_) | Self::SkipFallback(_) | Self::Final(_) => None,
        }
    }

    /// Returns the signer of this vote.
    #[must_use]
    pub const fn signer(&self) -> ValidatorId {
        match self {
            Self::Notar(v) => v.signer,
            Self::NotarFallback(v) => v.signer,
            Self::Skip(v) => v.signer,
            Self::SkipFallback(v) => v.signer,
            Self::Final(v) => v.signer,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;

    #[test]
    fn basic() {
        let sk = SecretKey::new(&mut rand::rng());
        let pk = sk.to_pk();

        let vote = Vote::new_notar(Slot::new(0), GENESIS_BLOCK_HASH, &sk, ValidatorId::new(0));
        assert!(matches!(vote, Vote::Notar(_)));
        assert!(vote.check_sig(&pk));

        let vote =
            Vote::new_notar_fallback(Slot::new(0), GENESIS_BLOCK_HASH, &sk, ValidatorId::new(0));
        assert!(matches!(vote, Vote::NotarFallback(_)));
        assert!(vote.check_sig(&pk));

        let vote = Vote::new_skip(Slot::new(0), &sk, ValidatorId::new(0));
        assert!(matches!(vote, Vote::Skip(_)));
        assert!(vote.check_sig(&pk));

        let vote = Vote::new_skip_fallback(Slot::new(0), &sk, ValidatorId::new(0));
        assert!(matches!(vote, Vote::SkipFallback(_)));
        assert!(vote.check_sig(&pk));

        let vote = Vote::new_final(Slot::new(0), &sk, ValidatorId::new(0));
        assert!(matches!(vote, Vote::Final(_)));
        assert!(vote.check_sig(&pk));
    }
}
