// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatedShred`] type.

use std::ops::{Deref, DerefMut};

use crate::crypto::merkle::SliceRoot;
use crate::crypto::signature::PublicKey;
use crate::shredder::Shred;

/// Different errors returned from [`ValidatedShred::try_new`].
#[derive(Debug)]
pub enum ShredVerifyError {
    /// The signature verification failed.
    InvalidSignature,
    /// Leader showed equivocation: a valid signature was seen on a different Merkle root.
    Equivocation,
}

/// A verified wrapper around a [`Shred`].
///
/// It uses the new type pattern to encode verification in the type system.
/// The encapsulated [`Shred`] has passed all required checks.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct ValidatedShred(Shred);

impl ValidatedShred {
    /// Performs various verification checks on the [`Shred`] and if they succeed, returns a shred.
    ///
    /// `cached_merkle_root`: Refers to Merkle root of the slice, if known from earlier shred.
    /// It is used to potentially skip expensive signature verification or detect equivocation.
    ///
    /// # Errors
    ///
    /// Returns [`ShredVerifyError`] if the [`Shred`] does not pass all verification checks.
    #[hotpath::measure]
    pub fn try_new(
        shred: Shred,
        cached_merkle_root: Option<&SliceRoot>,
        pk: &PublicKey,
    ) -> Result<Self, ShredVerifyError> {
        let derived_root = shred.merkle_root();

        match cached_merkle_root {
            Some(root) => {
                if root == &derived_root {
                    return Ok(Self(shred));
                }
                if shred.merkle_root_sig.verify(derived_root.as_ref(), pk) {
                    Err(ShredVerifyError::Equivocation)
                } else {
                    Err(ShredVerifyError::InvalidSignature)
                }
            }
            None => {
                if shred.merkle_root_sig.verify(derived_root.as_ref(), pk) {
                    Ok(Self(shred))
                } else {
                    Err(ShredVerifyError::InvalidSignature)
                }
            }
        }
    }

    /// Creates a new [`ValidatedShred`] when the inner [`Shred`] does not need to be verified.
    ///
    /// Used only by the parent module to create a validated shred when it is guaranteed that the inner shred comes from verified sources and does not need to be verified.
    pub(super) fn new_validated(shred: Shred) -> Self {
        Self(shred)
    }

    /// Get access to the inner [`Shred`] consuming self.
    pub fn into_shred(self) -> Shred {
        self.0
    }
}

impl Deref for ValidatedShred {
    type Target = Shred;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ValidatedShred {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use rand::rng;

    use super::*;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
    use crate::types::slice::create_slice_with_invalid_txs;

    fn create_random_shred() -> (Shred, SecretKey) {
        let mut shredder = RegularShredder::default();
        let sk = SecretKey::new(&mut rng());
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let shreds = shredder.shred(slice, &sk).unwrap();
        let shred = shreds[shreds.len() - 1].clone().into_shred();
        (shred, sk)
    }

    #[test]
    fn shred_verification() {
        let (shred, sk) = create_random_shred();
        let merkle_root = shred.merkle_root();
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
        let res = ValidatedShred::try_new(invalid_shred.clone(), Some(&merkle_root), &random_pk);
        assert!(matches!(res, Err(ShredVerifyError::InvalidSignature)));

        // checking different shred (with different Merkle root and valid sig)
        // against existing Merkle root should fail and detect equivocation
        let res =
            ValidatedShred::try_new(invalid_shred, Some(&merkle_root), &invalid_shred_sk.to_pk());
        assert!(matches!(res, Err(ShredVerifyError::Equivocation)));
    }
}
