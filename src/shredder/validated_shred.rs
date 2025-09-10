use std::collections::btree_map::Entry;

use crate::crypto::signature::PublicKey;
use crate::crypto::{Hash, MerkleTree};
use crate::shredder::Shred;
use crate::types::SliceIndex;

/// Different errors returned from [`ValidatedShred::new`].
#[derive(Debug)]
pub enum ShredVerifyError {
    /// The shred contained an invalid Merkle proof.
    InvalidProof,
    /// The signature verification failed.
    InvalidSignature,
    /// Leader showed equivocation.
    /// The Merkle root does not match the root from a previous shred.
    Equivocation,
}

/// Using the new type pattern, this struct provides the guarantee that various verification checks have been performaned on the encapsulated [`Shred`].
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ValidatedShred(Shred);

impl ValidatedShred {
    /// Performs various verification checks on the [`Shred`] and if they succeed, returns a shred.
    ///
    /// `cached_merkle_root`: Refers to Merkle root of the slice, if known from earlier shred.
    /// It is used to potentially skip expensive signature verification or detect equivocation.
    pub fn new(
        shred: Shred,
        cached_merkle_root: Entry<SliceIndex, Hash>,
        pk: &PublicKey,
    ) -> Result<Self, ShredVerifyError> {
        if !MerkleTree::check_proof(
            &shred.payload().data,
            shred.payload().index_in_slice,
            shred.merkle_root,
            &shred.merkle_path,
        ) {
            return Err(ShredVerifyError::InvalidProof);
        }

        match cached_merkle_root {
            Entry::Occupied(entry) => {
                if entry.get() == &shred.merkle_root {
                    return Ok(Self(shred));
                }
                if shred.merkle_root_sig.verify(&shred.merkle_root, pk) {
                    Err(ShredVerifyError::Equivocation)
                } else {
                    Err(ShredVerifyError::InvalidSignature)
                }
            }
            Entry::Vacant(entry) => {
                if shred.merkle_root_sig.verify(&shred.merkle_root, pk) {
                    entry.insert(shred.merkle_root);
                    Ok(Self(shred))
                } else {
                    Err(ShredVerifyError::InvalidSignature)
                }
            }
        }
    }

    /// Get a reference to the inner [`Shred`].
    pub fn to_shred(&self) -> &Shred {
        &self.0
    }

    /// Get access to the inner [`Shred`] consuming self.
    pub fn into_shred(self) -> Shred {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use rand::rng;

    use super::*;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
    use crate::types::slice::create_slice_with_invalid_txs;

    fn create_random_shred() -> (Shred, SecretKey) {
        let sk = SecretKey::new(&mut rng());
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let mut shreds = RegularShredder::shred(slice, &sk).unwrap();
        (shreds.pop().unwrap(), sk)
    }

    #[test]
    fn shred_verification() {
        let mut map = BTreeMap::new();
        let slice_index = SliceIndex::first();
        let random_pk = SecretKey::new(&mut rng()).to_pk();

        let (shred, sk) = create_random_shred();

        // checking against other public key should fail
        let res = ValidatedShred::new(shred.clone(), map.entry(slice_index), &random_pk);
        assert!(matches!(res, Err(ShredVerifyError::InvalidSignature)));
        assert!(!map.contains_key(&slice_index));

        // checking against correct public key should succeed
        let res = ValidatedShred::new(shred, map.entry(slice_index), &sk.to_pk());
        assert!(res.is_ok());
        assert!(map.contains_key(&slice_index));

        let (invalid_shred, invalid_shred_sk) = create_random_shred();

        // checking against other public key should fail
        // and should not be considered as equivocation
        let res = ValidatedShred::new(invalid_shred.clone(), map.entry(slice_index), &random_pk);
        assert!(matches!(res, Err(ShredVerifyError::InvalidSignature)));

        // checking different shred (with different Merkle root and valid sig)
        // against existing map entry should fail and detect equivocation
        let res = ValidatedShred::new(
            invalid_shred,
            map.entry(slice_index),
            &invalid_shred_sk.to_pk(),
        );
        assert!(matches!(res, Err(ShredVerifyError::Equivocation)));
    }
}
