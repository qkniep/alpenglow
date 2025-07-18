// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of an aggregate signature scheme.
//!
//! This uses the [`blst`] implementation of BLS signatures.
//! Specifically, it uses the BLS12-381 G2 (min sig) signature scheme.
//!
//! # Examples
//!
//! ```
//! use alpenglow::crypto::aggsig::{AggregateSignature, SecretKey};
//!
//! let msg = b"hello world";
//!
//! let sk1 = SecretKey::new(&mut rand::rng());
//! let pk1 = sk1.to_pk();
//! let sig1 = sk1.sign(msg);
//!
//! let sk2 = SecretKey::new(&mut rand::rng());
//! let pk2 = sk2.to_pk();
//! let sig2 = sk2.sign(msg);
//!
//! let mut aggsig = AggregateSignature::new(&[sig1, sig2], [0, 1], 2);
//! assert!(aggsig.verify(msg, &[pk1, pk2]));
//! ```

use bitvec::vec::BitVec;
use blst::BLST_ERROR;
use blst::min_sig::AggregateSignature as BlstAggSig;
use blst::min_sig::PublicKey as BlstPublicKey;
use blst::min_sig::SecretKey as BlstSecretKey;
use blst::min_sig::Signature as BlstSignature;
use rand::prelude::*;
use serde::Deserializer;
use serde::{Deserialize, Serialize};

use crate::ValidatorId;

const DST: &[u8] = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_";

/// A secret key for the aggregate signature scheme.
///
/// This is a wrapper around [`blst::min_sig::SecretKey`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SecretKey(BlstSecretKey);

/// A public key for the aggregate signature scheme.
///
/// This is a wrapper around [`blst::min_sig::PublicKey`].
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct PublicKey(BlstPublicKey);

impl PublicKey {
    pub fn try_from_bytes(pk_in: &[u8]) -> Result<Self, BLST_ERROR> {
        Ok(Self(BlstPublicKey::from_bytes(pk_in)?))
    }
    pub fn from_array_of_bytes<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let buf: Vec<u8> = Deserialize::deserialize(deserializer)?;

        Self::try_from_bytes(&buf)
            .map_err(|e| serde::de::Error::custom(format!("BLST error {e:?}")))
    }
}
/// An individual signature as part of the aggregate signature scheme.
///
/// This is a wrapper around [`blst::min_sig::Signature`].
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct IndividualSignature(pub BlstSignature);

/// An aggregated signature that contains a bitmask of signers.
///
/// This is a wrapper around [`blst::min_sig::Signature`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AggregateSignature {
    sig: BlstSignature,
    bitmask: BitVec,
}

impl SecretKey {
    /// Generates a new secret key.
    ///
    /// The required entropy is derived from the provided `rng`.
    pub fn new(rng: &mut impl CryptoRng) -> Self {
        let mut ikm = [0u8; 32];
        rng.fill_bytes(&mut ikm);

        let sk = blst::min_sig::SecretKey::key_gen(&ikm, &[])
            .expect("key_gen only fails for wrong sized ikm");
        Self(sk)
    }

    pub fn try_from_bytes(sk_in: &[u8]) -> Result<Self, BLST_ERROR> {
        Ok(Self(blst::min_sig::SecretKey::from_bytes(sk_in)?))
    }
    /// Converts this secret key into the corresponding public key.
    #[must_use]
    pub fn to_pk(&self) -> PublicKey {
        let pk = self.0.sk_to_pk();
        PublicKey(pk)
    }

    /// Signs the byte string `msg` using this secret key.
    // TODO: use `Signable` here, and add new `sign_bytes` function?
    #[must_use]
    pub fn sign(&self, msg: &[u8]) -> IndividualSignature {
        let sig = self.0.sign(msg, DST, &[]);
        IndividualSignature(sig)
    }

    pub fn from_array_of_bytes<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let buf: Vec<u8> = Deserialize::deserialize(deserializer)?;

        Self::try_from_bytes(&buf)
            .map_err(|e| serde::de::Error::custom(format!("BLST error {e:?}")))
    }
}

impl AsRef<BlstPublicKey> for PublicKey {
    fn as_ref(&self) -> &BlstPublicKey {
        &self.0
    }
}

impl IndividualSignature {
    /// Verifies that this is a valid signature of `msg` under `pk`.
    #[must_use]
    pub fn verify(&self, msg: &[u8], pk: &PublicKey) -> bool {
        self.0.verify(true, msg, DST, &[], &pk.0, true) == blst::BLST_ERROR::BLST_SUCCESS
    }
}

impl AggregateSignature {
    /// Aggregates the signatures of `sigs` into a single BLS signature.
    ///
    /// Augments the aggregate signature with a bitmask of length `num_bits`,
    /// where the bits in `indices` are set to 1.
    #[must_use]
    pub fn new<'a>(
        sigs: impl IntoIterator<Item = &'a IndividualSignature>,
        indices: impl IntoIterator<Item = ValidatorId>,
        num_bits: usize,
    ) -> Self {
        let mut sigs_iter = sigs.into_iter();
        let mut agg_sig = BlstAggSig::from_signature(&sigs_iter.next().unwrap().0);
        for sig in sigs_iter {
            agg_sig.add_signature(&sig.0, true).unwrap();
        }

        let mut bitmask = bitvec::bitvec![0; num_bits];
        for i in indices {
            bitmask.set(i as usize, true);
        }

        Self {
            sig: agg_sig.to_signature(),
            bitmask,
        }
    }

    /// Verifies the aggregate signature against `msg` and `pks`.
    #[must_use]
    pub fn verify(&self, msg: &[u8], pks: &[PublicKey]) -> bool {
        if self.bitmask.len() != pks.len() {
            return false;
        }
        let pks: Vec<_> = self.signers().map(|v| pks[v as usize].as_ref()).collect();
        let err = self.sig.fast_aggregate_verify(true, msg, DST, &pks);
        err == blst::BLST_ERROR::BLST_SUCCESS
    }

    /// Verifies the aggregate signature against `msg` and `pks`.
    #[must_use]
    pub fn verify_without_bitmask(&self, msg: &[u8], pks: &[PublicKey]) -> bool {
        if self.bitmask.count_ones() != pks.len() {
            return false;
        }
        let pks: Vec<_> = pks.iter().map(|p| p.as_ref()).collect();
        let err = self.sig.fast_aggregate_verify(true, msg, DST, &pks);
        err == blst::BLST_ERROR::BLST_SUCCESS
    }

    /// Returns `true` iff this validator's signature is part of the aggregate.
    #[must_use]
    pub fn is_signer(&self, validator_id: ValidatorId) -> bool {
        *self
            .bitmask
            .get(validator_id as usize)
            .as_deref()
            .unwrap_or(&false)
    }

    /// Iterates over all signers of this aggregate signature.
    pub fn signers(&self) -> impl Iterator<Item = ValidatorId> {
        self.bitmask.iter_ones().map(|i| i as ValidatorId)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let sk = SecretKey::new(&mut rand::rng());
        let pk = sk.to_pk();
        let msg = b"blst is such a blast";
        let sig = sk.sign(msg);
        assert!(sig.verify(msg, &pk));
    }

    #[test]
    fn aggregate() {
        let msg = b"blst is such a blast";

        let sk1 = SecretKey::new(&mut rand::rng());
        let pk1 = sk1.to_pk();
        let sig1 = sk1.sign(msg);

        let sk2 = SecretKey::new(&mut rand::rng());
        let pk2 = sk2.to_pk();
        let sig2 = sk2.sign(msg);

        // check individual signatures
        assert!(sig1.verify(msg, &pk1));
        assert!(sig2.verify(msg, &pk2));

        let mut aggsig = AggregateSignature::new(&[sig1, sig2], [0, 1], 2);

        // check aggregate signature
        assert!(aggsig.verify(msg, &[pk1, pk2]));
        assert!(aggsig.verify_without_bitmask(msg, &[pk1, pk2]));
        assert!(aggsig.verify_without_bitmask(msg, &[pk2, pk1]));

        // check failure cases
        assert!(!aggsig.verify(msg, &[pk1, pk2, pk1]));
        assert!(!aggsig.verify(msg, &[pk1, pk1]));
        assert!(!aggsig.verify(msg, &[pk1]));
        assert!(!aggsig.verify(msg, &[]));
        assert!(!aggsig.verify(b"not the original message", &[pk1]));
        assert!(!aggsig.verify_without_bitmask(msg, &[pk1, pk2, pk1]));
        assert!(!aggsig.verify_without_bitmask(msg, &[pk1, pk1]));
        assert!(!aggsig.verify_without_bitmask(msg, &[pk1]));
        assert!(!aggsig.verify_without_bitmask(msg, &[]));
        assert!(!aggsig.verify_without_bitmask(b"not the original message", &[pk1]));

        // modifying bitmask makes signature invalid
        aggsig.bitmask.set(0, false);
        assert!(!aggsig.verify(msg, &[pk1, pk2]));
        assert!(!aggsig.verify(msg, &[pk2]));
        assert!(!aggsig.verify_without_bitmask(msg, &[pk1, pk2]));
        assert!(!aggsig.verify_without_bitmask(msg, &[pk2]));
        aggsig.bitmask.set(1, false);
        assert!(!aggsig.verify(msg, &[pk1, pk2]));
        assert!(!aggsig.verify(msg, &[]));
        assert!(!aggsig.verify_without_bitmask(msg, &[pk1, pk2]));
        assert!(!aggsig.verify_without_bitmask(msg, &[]));
    }

    #[test]
    fn signers() {
        let msg = b"blst is such a blast";

        let sk1 = SecretKey::new(&mut rand::rng());
        let pk1 = sk1.to_pk();
        let sig1 = sk1.sign(msg);

        let sk2 = SecretKey::new(&mut rand::rng());
        let pk2 = sk2.to_pk();
        let sig2 = sk2.sign(msg);

        let sk3 = SecretKey::new(&mut rand::rng());
        let pk3 = sk3.to_pk();
        let sig3 = sk3.sign(msg);

        assert!(sig1.verify(msg, &pk1));
        assert!(sig2.verify(msg, &pk2));
        assert!(sig3.verify(msg, &pk3));

        // only aggregate over 2/3 signatures
        let aggsig = AggregateSignature::new(&[sig1, sig3], [0, 2], 3);

        // check signers bitmask
        let signers: Vec<_> = aggsig.signers().collect();
        assert_eq!(signers.len(), 2);
        assert!(signers.contains(&0));
        assert!(!signers.contains(&1));
        assert!(signers.contains(&2));

        // check aggregate signature
        assert!(aggsig.verify_without_bitmask(msg, &[pk1, pk3]));
        assert!(aggsig.verify(msg, &[pk1, pk2, pk3]));

        // order for set of PKs matters
        assert!(!aggsig.verify(msg, &[pk2, pk1, pk3]));
        assert!(!aggsig.verify(msg, &[pk1, pk3, pk2]));
        assert!(!aggsig.verify(msg, &[pk2, pk3, pk1]));
        assert!(!aggsig.verify(msg, &[pk3, pk1, pk2]));
    }
}
