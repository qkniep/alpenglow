// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of an aggregate signature scheme.
//!
//! This uses the [`blst`] implementation of BLS signatures.
//! Specifically, it uses the BLS12-381 G1 (min sig) signature scheme.
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

use std::mem::MaybeUninit;

use bitvec::vec::BitVec;
use blst::BLST_ERROR;
use blst::min_sig::{
    AggregateSignature as BlstAggSig, PublicKey as BlstPublicKey, SecretKey as BlstSecretKey,
    Signature as BlstSignature,
};
use log::warn;
use rand::prelude::*;
use serde::{Deserialize, Deserializer, Serialize};
use static_assertions::const_assert_eq;
use wincode::{SchemaRead, SchemaWrite};

use crate::ValidatorId;

/// Domain separator corresponding to the G1 (min sig), RO (random oracle) variant.
const DST: &[u8] = b"BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_";

/// Size of an uncompressed BLS signature (in the `min_sig` scheme).
///
/// We deal with uncompressed signatures everywhere.
/// This way signatures are twice as big as if we used compressed signatures.
/// However, we save the time of uncompressing the signature before verifying.
const UNCOMPRESSED_SIG_SIZE: usize = 96;
const_assert_eq!(
    UNCOMPRESSED_SIG_SIZE,
    std::mem::size_of::<blst::blst_p1_affine>()
);

/// Maximum number of signers that can be aggregated into an aggregate signature.
const MAX_SIGNERS: usize = 2048;

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
    /// Tries to convert a byte array into a public key.
    ///
    /// Returns a `BLST_ERROR` if the provided bytes are not a valid BLS public key.
    pub fn try_from_bytes(pk_in: &[u8]) -> Result<Self, BLST_ERROR> {
        Ok(Self(BlstPublicKey::from_bytes(pk_in)?))
    }

    /// Tries to deserialize a `Vec<u8>` into a public key.
    ///
    /// This is for use with `serde(deserialize_with)`.
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
//
// NOTE: Deriving `PartialEq` and `Eq` to support testing.
// It only makes sense beccause the underlying signature scheme happens to be deterministic and unique.
// Reevaluate if we change the signature scheme.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IndividualSignature(BlstSignature);

impl<'de> SchemaRead<'de> for IndividualSignature {
    type Dst = IndividualSignature;

    fn read(
        reader: &mut impl wincode::io::Reader<'de>,
        dst: &mut MaybeUninit<Self::Dst>,
    ) -> wincode::ReadResult<()> {
        let sig_bytes = reader.borrow_exact(UNCOMPRESSED_SIG_SIZE)?;
        let sig = BlstSignature::deserialize(sig_bytes).map_err(|e| {
            warn!("encountered invalid BLS sig: {e:?}");
            wincode::ReadError::Custom("invalid BLS encoding")
        })?;
        dst.write(IndividualSignature(sig));
        wincode::ReadResult::Ok(())
    }
}

impl SchemaWrite for IndividualSignature {
    type Src = IndividualSignature;

    fn size_of(_src: &Self::Src) -> wincode::WriteResult<usize> {
        Ok(UNCOMPRESSED_SIG_SIZE)
    }

    fn write(writer: &mut impl wincode::io::Writer, src: &Self::Src) -> wincode::WriteResult<()> {
        Ok(writer.write(&src.0.serialize())?)
    }
}

/// An aggregated signature that contains a bitmask of signers.
///
/// This is a wrapper around [`blst::min_sig::Signature`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggregateSignature {
    sig: BlstSignature,
    bitmask: BitVec,
}

impl<'de> SchemaRead<'de> for AggregateSignature {
    type Dst = AggregateSignature;

    fn read(
        reader: &mut impl wincode::io::Reader<'de>,
        dst: &mut MaybeUninit<Self::Dst>,
    ) -> wincode::ReadResult<()> {
        // read raw data
        let sig_bytes = reader.borrow_exact(UNCOMPRESSED_SIG_SIZE)?;
        let num_bits = <usize>::get(reader)?;
        let bitmask_raw_vec = <Vec<usize>>::get(reader)?;

        // map BLS signature
        let sig = BlstSignature::from_bytes(sig_bytes).map_err(|e| {
            warn!("encountered invalid BLS sig: {e:?}");
            wincode::ReadError::Custom("invalid BLS encoding")
        })?;

        // map bitmask
        if bitmask_raw_vec.len() > MAX_SIGNERS.div_ceil(usize::BITS as usize) {
            warn!(
                "bitmask too long: {} bits > {} max signers",
                bitmask_raw_vec.len() * usize::BITS as usize,
                MAX_SIGNERS
            );
            return Err(wincode::ReadError::Custom("bitmask too long"));
        }
        if num_bits > usize::BITS as usize * bitmask_raw_vec.len() {
            warn!(
                "want to use too many bits: {} bits > {} bits allocated",
                num_bits,
                bitmask_raw_vec.len() * usize::BITS as usize,
            );
            return Err(wincode::ReadError::Custom("want to use too many bits"));
        }
        let mut bitmask =
            BitVec::try_from_vec(bitmask_raw_vec).expect("bitmask vector should never be too big");

        // the `BitVec` is now initialized with some `usize` elements
        // we only want to use the first `num_bits` bits, as this is the intended length
        // some last bits may be uninitialized and will be ignored by `BitVec`
        bitmask.truncate(num_bits);

        dst.write(AggregateSignature { sig, bitmask });
        wincode::ReadResult::Ok(())
    }
}

impl SchemaWrite for AggregateSignature {
    type Src = AggregateSignature;

    fn size_of(src: &Self::Src) -> wincode::WriteResult<usize> {
        let bitslice_num_elements = src.bitmask.as_bitslice().len();
        // sig + num_bits + num_usizes + usize_len * num_usizes
        Ok(UNCOMPRESSED_SIG_SIZE + 8 + 8 + 8 * bitslice_num_elements)
    }

    fn write(writer: &mut impl wincode::io::Writer, src: &Self::Src) -> wincode::WriteResult<()> {
        writer.write(&src.sig.serialize())?;
        <usize as SchemaWrite>::write(writer, &src.bitmask.as_bitslice().len())?;
        let data = src.bitmask.as_bitslice().domain();
        <usize as SchemaWrite>::write(writer, &data.len())?;
        for elem in data {
            <usize as SchemaWrite>::write(writer, &elem)?;
        }
        Ok(())
    }
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

    /// Tries to convert a byte string into a secret key.
    ///
    /// Returns a `BLST_ERROR` if the provided bytes are not a valid BLS secret key.
    pub fn try_from_bytes(sk_in: &[u8]) -> Result<Self, BLST_ERROR> {
        Ok(Self(blst::min_sig::SecretKey::from_bytes(sk_in)?))
    }

    /// Tries to deserialize a `Vec<u8>` into a secret key.
    ///
    /// This is for use with `serde(deserialize_with)`.
    pub fn from_array_of_bytes<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let buf: Vec<u8> = Deserialize::deserialize(deserializer)?;

        Self::try_from_bytes(&buf)
            .map_err(|e| serde::de::Error::custom(format!("BLST error {e:?}")))
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
        let pks: Vec<_> = self.signers().map(|v| &pks[v as usize].0).collect();
        let err = self.sig.fast_aggregate_verify(true, msg, DST, &pks);
        err == blst::BLST_ERROR::BLST_SUCCESS
    }

    /// Verifies the aggregate signature against `msg` and `pks`.
    #[must_use]
    pub fn verify_without_bitmask(&self, msg: &[u8], pks: &[PublicKey]) -> bool {
        if self.bitmask.count_ones() != pks.len() {
            return false;
        }
        let pks: Vec<_> = pks.iter().map(|p| &p.0).collect();
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

    #[test]
    fn serialize_toml() {
        #[derive(Serialize, Deserialize)]
        struct KeyPair {
            #[serde(deserialize_with = "SecretKey::from_array_of_bytes")]
            sk: SecretKey,
            #[serde(deserialize_with = "PublicKey::from_array_of_bytes")]
            pk: PublicKey,
        }

        let sk = SecretKey::new(&mut rand::rng());
        let pk = sk.to_pk();

        // serialize and deserialize to/from TOML
        let kp = KeyPair { sk, pk };
        let serialized = toml::to_string(&kp).unwrap();
        let deserialized: KeyPair = toml::from_str(&serialized).unwrap();
        assert_eq!(kp.sk.0.to_bytes(), deserialized.sk.0.to_bytes());
        assert_eq!(kp.pk.0.to_bytes(), deserialized.pk.0.to_bytes());

        // wrong type for secret key
        let wrong_sk_str = format!("sk = \"hello\"\npk = {:?}", kp.pk.0.to_bytes());
        let deserialized: Result<KeyPair, toml::de::Error> = toml::from_str(&wrong_sk_str);
        assert!(deserialized.is_err());

        // invalid bytes for secret key
        let wrong_sk_str = format!("sk = [0, 0, 0, 0]\npk = {:?}", kp.pk.0.to_bytes());
        let deserialized: Result<KeyPair, toml::de::Error> = toml::from_str(&wrong_sk_str);
        assert!(deserialized.is_err());

        // wrong type for public key
        let wrong_pk_str = format!("sk = {:?}\npk = \"hello\"", kp.sk.0.to_bytes());
        let deserialized: Result<KeyPair, toml::de::Error> = toml::from_str(&wrong_pk_str);
        assert!(deserialized.is_err());

        // invalid bytes for public key
        let wrong_pk_str = format!("sk = {:?}\npk = [0, 0, 0, 0]", kp.sk.0.to_bytes());
        let deserialized: Result<KeyPair, toml::de::Error> = toml::from_str(&wrong_pk_str);
        assert!(deserialized.is_err());
    }
}
