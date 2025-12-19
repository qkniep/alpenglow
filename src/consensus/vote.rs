// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Vote types used for the consensus protocol.
//!
//!

use wincode::{SchemaRead, SchemaWrite};

use crate::crypto::aggsig::{PublicKey, SecretKey};
use crate::crypto::merkle::BlockHash;
use crate::crypto::{IndividualSignature, Signable};
use crate::{Slot, ValidatorId};

/// A signed vote used in consensus.
///
/// `Vote` wraps a [`VoteKind`] with the signer's public key and signature,
/// allowing type-specific data to be authenticated and verified.
///
/// This struct is produced by signing the bytes of a `VoteKind` instance.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub struct Vote {
    kind: VoteKind,
    sig: IndividualSignature,
    signer: ValidatorId,
}

/// Represents the type-specific vote payload as per the protocol.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub enum VoteKind {
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

impl Vote {
    /// Creates a new vote directly from its [`VoteKind`].
    #[must_use]
    pub fn new(kind: VoteKind, sk: &SecretKey, signer: ValidatorId) -> Self {
        let sig = sk.sign(&kind.bytes_to_sign());
        Self { kind, sig, signer }
    }

    /// Creates a new notarization vote.
    /// That is, a vote corresponding to the [`VoteKind::Notar`] variant.
    #[must_use]
    pub fn new_notar(
        slot: Slot,
        block_hash: BlockHash,
        sk: &SecretKey,
        signer: ValidatorId,
    ) -> Self {
        let kind = VoteKind::Notar(slot, block_hash);
        Self::new(kind, sk, signer)
    }

    /// Creates a new notar-fallback vote.
    /// That is, a vote corresponding to the [`VoteKind::NotarFallback`] variant.
    #[must_use]
    pub fn new_notar_fallback(
        slot: Slot,
        block_hash: BlockHash,
        sk: &SecretKey,
        signer: ValidatorId,
    ) -> Self {
        let kind = VoteKind::NotarFallback(slot, block_hash);
        Self::new(kind, sk, signer)
    }

    /// Creates a new skip vote.
    /// That is, a vote corresponding to the [`VoteKind::Skip`] variant.
    #[must_use]
    pub fn new_skip(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        let kind = VoteKind::Skip(slot);
        Self::new(kind, sk, signer)
    }

    /// Creates a new skip-fallback vote.
    /// That is, a vote corresponding to the [`VoteKind::SkipFallback`] variant.
    #[must_use]
    pub fn new_skip_fallback(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        let kind = VoteKind::SkipFallback(slot);
        Self::new(kind, sk, signer)
    }

    /// Creates a new finalization vote.
    /// That is, a vote corresponding to the [`VoteKind::Final`] variant.
    #[must_use]
    pub fn new_final(slot: Slot, sk: &SecretKey, signer: ValidatorId) -> Self {
        let kind = VoteKind::Final(slot);
        Self::new(kind, sk, signer)
    }

    /// Checks whether this vote's signature is valid under the given public key.
    #[must_use]
    pub fn check_sig(&self, pk: &PublicKey) -> bool {
        let msg = self.kind.bytes_to_sign();
        self.sig.verify(&msg, pk)
    }

    /// Returns the [`VoteKind`] of this vote.
    #[must_use]
    pub const fn kind(&self) -> &VoteKind {
        &self.kind
    }

    /// Returns `true` iff this is a notarization vote.
    #[must_use]
    pub const fn is_notar(&self) -> bool {
        matches!(self.kind, VoteKind::Notar(_, _))
    }

    /// Returns `true` iff this is a notar-fallback vote.
    #[must_use]
    pub const fn is_notar_fallback(&self) -> bool {
        matches!(self.kind, VoteKind::NotarFallback(_, _))
    }

    /// Returns `true` iff this is a skip vote.
    #[must_use]
    pub const fn is_skip(&self) -> bool {
        matches!(self.kind, VoteKind::Skip(_))
    }

    /// Returns `true` iff this is a skip-fallback vote.
    #[must_use]
    pub const fn is_skip_fallback(&self) -> bool {
        matches!(self.kind, VoteKind::SkipFallback(_))
    }

    /// Returns `true` iff this is a finalization vote.
    #[must_use]
    pub const fn is_final(&self) -> bool {
        matches!(self.kind, VoteKind::Final(_))
    }

    /// Returns the slot number this vote corresponds to.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        self.kind.slot()
    }

    /// Returns the block hash this vote corresponds to, if any.
    ///
    /// Returns `None` if the vote is a skip(-fallback) or finalization vote.
    #[must_use]
    pub const fn block_hash(&self) -> Option<&BlockHash> {
        self.kind.block_hash()
    }

    /// Returns the signature of this vote.
    #[must_use]
    pub const fn sig(&self) -> &IndividualSignature {
        &self.sig
    }

    /// Returns the signer of this vote.
    #[must_use]
    pub const fn signer(&self) -> ValidatorId {
        self.signer
    }
}

impl VoteKind {
    /// Returns the slot number this vote corresponds to.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        match self {
            Self::Notar(slot, _)
            | Self::NotarFallback(slot, _)
            | Self::Skip(slot)
            | Self::SkipFallback(slot)
            | Self::Final(slot) => *slot,
        }
    }

    /// Returns the block hash this vote corresponds to, if any.
    ///
    /// Returns `None` if the vote is a skip(-fallback) or finalization vote.
    #[must_use]
    pub const fn block_hash(&self) -> Option<&BlockHash> {
        match self {
            Self::Notar(_, hash) | Self::NotarFallback(_, hash) => Some(hash),
            Self::Skip(_) | Self::SkipFallback(_) | Self::Final(_) => None,
        }
    }
}

impl Signable for VoteKind {
    fn bytes_to_sign(&self) -> Vec<u8> {
        wincode::serialize(self).expect("serialization should not panic")
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

        let vote = Vote::new_notar(Slot::new(0), GENESIS_BLOCK_HASH, &sk, 0);
        assert!(vote.is_notar());
        assert!(vote.check_sig(&pk));

        let vote = Vote::new_notar_fallback(Slot::new(0), GENESIS_BLOCK_HASH, &sk, 0);
        assert!(vote.is_notar_fallback());
        assert!(vote.check_sig(&pk));

        let vote = Vote::new_skip(Slot::new(0), &sk, 0);
        assert!(vote.is_skip());
        assert!(vote.check_sig(&pk));

        let vote = Vote::new_skip_fallback(Slot::new(0), &sk, 0);
        assert!(vote.is_skip_fallback());
        assert!(vote.check_sig(&pk));

        let vote = Vote::new_final(Slot::new(0), &sk, 0);
        assert!(vote.is_final());
        assert!(vote.check_sig(&pk));
    }
}
