// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatedShred`] type.

use thiserror::Error;

use crate::crypto::merkle::SliceRoot;
use crate::crypto::signature::PublicKey;
use crate::shredder::{Shred, ShredPayload, SliceCommitment};

/// Different errors returned from [`ValidatedShred::try_new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum ShredValidationError {
    /// The signature verification failed.
    #[error("signature verification failed")]
    InvalidSignature,
    /// Leader showed equivocation: a valid signature was seen for a different commitment.
    #[error("leader equivocation: signed two slices with different commitments")]
    Equivocation,
}

/// A validated wrapper around a [`Shred`].
///
/// It uses the new type pattern to encode verification in the type system.
/// The encapsulated [`Shred`] has passed all required checks.
///
/// The slice's Merkle root is derived and cached at construction time
/// because it is needed for signature verification anyways.
/// So calling [`ValidatedShred::slice_root`] does't re-calculate it.
#[derive(Clone, Debug)]
pub struct ValidatedShred {
    shred: Shred,
    slice_root: SliceRoot,
}

impl ValidatedShred {
    /// Validates the inner [`Shred`] and returns a new [`ValidatedShred`].
    ///
    /// Derives the [`SliceCommitment`] from `shred` and uses `cached_commitment`,
    /// the [`SliceCommitment`] of an earlier shred verified for the same slice,
    /// if any, to skip signature verification or detect leader equivocation.
    /// Signature verification can only be skipped if the two commitments match.
    ///
    /// # Errors
    ///
    /// - [`ShredValidationError::InvalidSignature`] if the signature verification fails
    ///   against the shred's commitment.
    /// - [`ShredValidationError::Equivocation`] if the signature is valid but
    ///   the shred's commitment does not match the cached commitment.
    #[hotpath::measure]
    pub fn try_new(
        shred: Shred,
        cached_commitment: Option<&SliceCommitment>,
        pk: &PublicKey,
    ) -> Result<Self, ShredValidationError> {
        let slice_root = shred.slice_root();
        let msg = SliceCommitment::new(&shred.payload().header, &slice_root);

        match cached_commitment {
            Some(cached) => {
                if cached == &msg {
                    return Ok(Self { shred, slice_root });
                }
                if shred.slice_sig.verify_bytes(msg.as_ref(), pk) {
                    Err(ShredValidationError::Equivocation)
                } else {
                    Err(ShredValidationError::InvalidSignature)
                }
            }
            None => {
                if shred.slice_sig.verify_bytes(msg.as_ref(), pk) {
                    Ok(Self { shred, slice_root })
                } else {
                    Err(ShredValidationError::InvalidSignature)
                }
            }
        }
    }

    /// Creates a new [`ValidatedShred`] when the inner [`Shred`] does not need to be verified.
    ///
    /// Used only by the parent module to wrap shreds that are already known to be valid.
    /// The caller must pass the slice's Merkle root, which avoids re-deriving it from the shred's proof.
    pub(super) fn new_validated(shred: Shred, slice_root: SliceRoot) -> Self {
        debug_assert_eq!(shred.slice_root(), slice_root);
        Self { shred, slice_root }
    }

    /// The [`SliceCommitment`] the leader's signature covers for this shred.
    ///
    /// This commitment binds to the slice header and the Merkle root.
    /// Suitable for seeding a cache to short-circuit re-verification
    /// of further shreds in the same slice (see [`ValidatedShred::try_new`]).
    /// Uses the cached Merkle root, so it does not re-derive it from the proof.
    #[must_use]
    pub fn commitment(&self) -> SliceCommitment {
        SliceCommitment::new(&self.shred.payload().header, &self.slice_root)
    }

    /// Returns the cached Merkle root of the slice this shred belongs to.
    ///
    /// Unlike [`Shred::slice_root`], this does not re-derive the root from the proof.
    #[must_use]
    pub fn slice_root(&self) -> &SliceRoot {
        &self.slice_root
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
    use crate::types::SliceIndex;
    use crate::types::slice::create_slice_with_invalid_txs;

    fn create_random_shred() -> (Shred, SecretKey) {
        let mut shredder = RegularShredder::default();
        let sk = SecretKey::new(&mut rng());
        let slice = create_slice_with_invalid_txs(RegularShredder::MAX_DATA_SIZE);
        let shreds = shredder.shred(&slice, &sk).unwrap();
        let shred = shreds[shreds.len() - 1].clone().into_shred();
        (shred, sk)
    }

    #[test]
    fn shred_verification() {
        let (shred, sk) = create_random_shred();
        let cached = SliceCommitment::new(&shred.payload().header, &shred.slice_root());
        let random_pk = SecretKey::new(&mut rng()).to_pk();

        // checking against other public key should fail
        let res = ValidatedShred::try_new(shred.clone(), None, &random_pk);
        assert!(matches!(res, Err(ShredValidationError::InvalidSignature)));

        // checking against correct public key should succeed
        let res = ValidatedShred::try_new(shred, None, &sk.to_pk());
        assert!(res.is_ok());

        let (other_shred, other_sk) = create_random_shred();

        // checking against wrong public key should fail
        // and should not be considered as equivocation
        let res = ValidatedShred::try_new(other_shred.clone(), Some(&cached), &random_pk);
        assert!(matches!(res, Err(ShredValidationError::InvalidSignature)));

        // checking different shred with valid signature should detect equivocation
        let res = ValidatedShred::try_new(other_shred, Some(&cached), &other_sk.to_pk());
        assert!(matches!(res, Err(ShredValidationError::Equivocation)));
    }

    #[test]
    fn commitment_binds_header() {
        let (shred, sk) = create_random_shred();
        let pk = sk.to_pk();
        let cached = SliceCommitment::new(&shred.payload().header, &shred.slice_root());

        // baseline: original shred verifies on both paths
        assert!(ValidatedShred::try_new(shred.clone(), None, &pk).is_ok());
        assert!(ValidatedShred::try_new(shred.clone(), Some(&cached), &pk).is_ok());

        // `expect_invalid` runs both verification paths (with/without cached commitment)
        let expect_invalid = |tampered: Shred| {
            for cache in [None, Some(&cached)] {
                let res = ValidatedShred::try_new(tampered.clone(), cache, &pk);
                assert!(
                    matches!(res, Err(ShredValidationError::InvalidSignature)),
                    "tampered header accepted (cached={}): {res:?}",
                    cache.is_some(),
                );
            }
        };

        // cross-slot replay
        let mut tampered = shred.clone();
        let original_slot = tampered.payload().header.slot;
        tampered.payload_mut().header.slot = original_slot.next();
        expect_invalid(tampered);

        // cross-slice replay
        let mut tampered = shred.clone();
        let original_index = tampered.payload().header.slice_index.inner();
        tampered.payload_mut().header.slice_index = SliceIndex::new_for_test(original_index + 1);
        expect_invalid(tampered);

        // length extension
        let mut tampered = shred;
        tampered.payload_mut().header.is_last = !tampered.payload().header.is_last;
        expect_invalid(tampered);
    }
}
