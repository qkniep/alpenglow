// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatedShred`] type.

use thiserror::Error;

use crate::crypto::merkle::SliceRoot;
use crate::crypto::signature::PublicKey;
use crate::shredder::{Shred, ShredPayload, SliceCommitment};

/// Different errors returned from [`ValidatedShred::try_new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum ShredVerifyError {
    /// The signature verification failed.
    #[error("signature verification failed")]
    InvalidSignature,
    /// Leader showed equivocation: a valid signature was seen for a different commitment.
    #[error("leader equivocation: signed two slices with different commitments")]
    Equivocation,
}

/// A verified wrapper around a [`Shred`].
///
/// It uses the new type pattern to encode verification in the type system.
/// The encapsulated [`Shred`] has passed all required checks.
///
/// The slice's Merkle root is derived and cached at construction time
/// because it is needed for signature verification anyways.
/// So calling [`ValidatedShred::merkle_root`] does't re-calculate it.
#[derive(Clone, Debug)]
pub struct ValidatedShred {
    shred: Shred,
    merkle_root: SliceRoot,
}

impl ValidatedShred {
    /// Performs various verification checks on the [`Shred`] and if they succeed, returns a shred.
    ///
    /// `cached_commitment`: The [`SliceCommitment`] of an earlier shred verified for
    /// the same slice, if any. Used to skip expensive signature verification when the new
    /// shred reproduces the exact same authenticated content, and to detect leader
    /// equivocation otherwise.
    ///
    /// The fast path **must** compare the full commitment — comparing only the Merkle
    /// root would let header tampering (e.g. flipping `is_last`) slip through, since the
    /// Merkle root commits to payload data but not to the `SliceHeader` fields the
    /// signature covers.
    ///
    /// # Errors
    ///
    /// Returns [`ShredVerifyError`] if the [`Shred`] does not pass all verification checks.
    #[hotpath::measure]
    pub fn try_new(
        shred: Shred,
        cached_commitment: Option<&SliceCommitment>,
        pk: &PublicKey,
    ) -> Result<Self, ShredVerifyError> {
        let derived_root = shred.merkle_root();
        let msg = SliceCommitment::new(&shred.payload().header, &derived_root);

        match cached_commitment {
            Some(cached) => {
                if cached == &msg {
                    return Ok(Self {
                        shred,
                        merkle_root: derived_root,
                    });
                }
                if shred.merkle_root_sig.verify_bytes(msg.as_ref(), pk) {
                    Err(ShredVerifyError::Equivocation)
                } else {
                    Err(ShredVerifyError::InvalidSignature)
                }
            }
            None => {
                if shred.merkle_root_sig.verify_bytes(msg.as_ref(), pk) {
                    Ok(Self {
                        shred,
                        merkle_root: derived_root,
                    })
                } else {
                    Err(ShredVerifyError::InvalidSignature)
                }
            }
        }
    }

    /// The [`SliceCommitment`] the leader's signature covers for this shred.
    ///
    /// Suitable for seeding a cache to short-circuit re-verification of further
    /// shreds in the same slice (see [`ValidatedShred::try_new`]). Uses the cached
    /// Merkle root, so it does not re-derive it from the proof.
    #[must_use]
    pub fn commitment(&self) -> SliceCommitment {
        SliceCommitment::new(&self.shred.payload().header, &self.merkle_root)
    }

    /// Creates a new [`ValidatedShred`] when the inner [`Shred`] does not need to be verified.
    ///
    /// Used only by the parent module to wrap shreds that are already known to be valid.
    /// The caller must pass the slice's Merkle root, which avoids re-deriving it from the shred's proof.
    pub(super) fn new_validated(shred: Shred, merkle_root: SliceRoot) -> Self {
        debug_assert_eq!(shred.merkle_root(), merkle_root);
        Self { shred, merkle_root }
    }

    /// Returns the cached Merkle root of the slice this shred belongs to.
    ///
    /// Unlike [`Shred::merkle_root`], this does not re-derive the root from the proof.
    #[must_use]
    pub fn merkle_root(&self) -> &SliceRoot {
        &self.merkle_root
    }

    /// References the payload contained in the inner [`Shred`].
    #[must_use]
    pub fn payload(&self) -> &ShredPayload {
        self.shred.payload()
    }

    /// Returns `true` iff the inner [`Shred`] is a data shred.
    #[must_use]
    pub fn is_data(&self) -> bool {
        self.shred.is_data()
    }

    /// Returns `true` iff the inner [`Shred`] is a coding shred.
    #[must_use]
    pub fn is_coding(&self) -> bool {
        self.shred.is_coding()
    }

    /// Borrows the inner [`Shred`].
    #[must_use]
    pub fn as_shred(&self) -> &Shred {
        &self.shred
    }

    /// Get access to the inner [`Shred`] consuming self.
    pub fn into_shred(self) -> Shred {
        self.shred
    }
}

#[cfg(test)]
mod tests {
    use rand::rng;

    use super::*;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{RegularShredder, Shredder};
    use crate::types::slice::create_slice_with_invalid_txs;

    fn create_random_shred() -> (Shred, SecretKey) {
        let mut shredder = RegularShredder::default();
        let sk = SecretKey::new(&mut rng());
        let slice = create_slice_with_invalid_txs(RegularShredder::MAX_DATA_SIZE);
        let shreds = shredder.shred(slice, &sk).unwrap();
        let shred = shreds[shreds.len() - 1].clone().into_shred();
        (shred, sk)
    }

    #[test]
    fn shred_verification() {
        let (shred, sk) = create_random_shred();
        let cached = SliceCommitment::new(&shred.payload().header, &shred.merkle_root());
        let random_pk = SecretKey::new(&mut rng()).to_pk();

        // checking against other public key should fail
        let res = ValidatedShred::try_new(shred.clone(), None, &random_pk);
        assert!(matches!(res, Err(ShredVerifyError::InvalidSignature)));

        // checking against correct public key should succeed
        let res = ValidatedShred::try_new(shred, None, &sk.to_pk());
        assert!(res.is_ok());

        let (invalid_shred, invalid_shred_sk) = create_random_shred();

        // checking against other public key should fail
        // and should not be considered as equivocation
        let res = ValidatedShred::try_new(invalid_shred.clone(), Some(&cached), &random_pk);
        assert!(matches!(res, Err(ShredVerifyError::InvalidSignature)));

        // checking different shred (with different Merkle root and valid sig)
        // against existing signed message should fail and detect equivocation
        let res = ValidatedShred::try_new(invalid_shred, Some(&cached), &invalid_shred_sk.to_pk());
        assert!(matches!(res, Err(ShredVerifyError::Equivocation)));
    }

    /// Mutating any `SliceHeader` field on a real shred must invalidate the
    /// signature on **both** verification paths:
    /// - cold path (`cached_commitment = None`): full Ed25519 verify fails.
    /// - fast path (`cached_commitment = Some`): the cached bytes mismatch the
    ///   tampered shred's commitment, forcing a re-verify that then fails.
    ///
    /// The fast path is the regression-critical one: comparing only the Merkle
    /// root in the cache would let header tampering (e.g. flipping `is_last` on
    /// a shred whose data is identical to one we've already accepted) slip
    /// through without ever re-checking the signature.
    #[test]
    fn header_is_bound_to_signature() {
        use crate::Slot;
        use crate::types::SliceIndex;

        let (shred, sk) = create_random_shred();
        let pk = sk.to_pk();
        let cached = SliceCommitment::new(&shred.payload().header, &shred.merkle_root());

        // baseline: original shred verifies on both paths
        assert!(ValidatedShred::try_new(shred.clone(), None, &pk).is_ok());
        assert!(ValidatedShred::try_new(shred.clone(), Some(&cached), &pk).is_ok());

        // Each mutation tampers one header field and must be rejected on both
        // verification paths. `expect_invalid` runs both.
        let expect_invalid = |tampered: Shred| {
            for cache in [None, Some(&cached)] {
                let res = ValidatedShred::try_new(tampered.clone(), cache, &pk);
                assert!(
                    matches!(res, Err(ShredVerifyError::InvalidSignature)),
                    "tampered header accepted (cached={}): {res:?}",
                    cache.is_some(),
                );
            }
        };

        // cross-slot replay: mutate header.slot
        let mut tampered = shred.clone();
        let original_slot = tampered.payload().header.slot;
        tampered.payload_mut().header.slot = Slot::new(original_slot.inner() + 1);
        expect_invalid(tampered);

        // mutate header.slice_index — derive the new index from the original so
        // the mutation can never be a no-op (which would leave the signature valid).
        let mut tampered = shred.clone();
        let original_index = tampered.payload().header.slice_index.inner();
        tampered.payload_mut().header.slice_index = SliceIndex::new_for_test(original_index + 1);
        expect_invalid(tampered);

        // mutate header.is_last — regression case: same Merkle root as cached,
        // only the header bit differs. Caching just the root would have
        // accepted this on the fast path. (Last use of `shred`, so move it.)
        let mut tampered = shred;
        tampered.payload_mut().header.is_last = !tampered.payload().header.is_last;
        expect_invalid(tampered);
    }
}
