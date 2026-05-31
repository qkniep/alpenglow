// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of a digital signature scheme.
//!
//! This module abstracts the digital signatures used throughout the entire library.
//! Currently, it provides Ed25519 digital signature scheme, as specified in [RFC 8032].
//! Specifically, it is a wrapper around the [`ed25519_zebra`] crate.
//!
//! [RFC 8032]: https://tools.ietf.org/html/rfc8032

use ed25519_zebra::{SigningKey, VerificationKey};
use rand::CryptoRng;
use serde::{Deserialize, Serialize};
use wincode::{SchemaRead, SchemaWrite};

use crate::crypto::Signable;

/// Secret key for the digital signature scheme.
///
/// This is a wrapper around [`ed25519_zebra::SigningKey`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SecretKey(SigningKey);

/// Public key for the digital signature scheme.
///
/// This is a wrapper around [`ed25519_zebra::VerificationKey`].
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct PublicKey(VerificationKey);

wincode::pod_wrapper! {
    unsafe struct PodSignature(ed25519_zebra::Signature);
}

/// Digital signature.
///
/// This is a wrapper around [`ed25519_zebra::Signature`].
#[derive(Clone, Copy, Debug, SchemaRead, SchemaWrite)]
pub struct Signature(#[wincode(with = "PodSignature")] ed25519_zebra::Signature);

impl SecretKey {
    /// Generates a new secret key.
    ///
    /// The required entropy is derived from the provided `rng`.
    pub fn new(rng: &mut impl CryptoRng) -> Self {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes[..]);
        let sk: SigningKey = bytes.into();
        Self(sk)
    }

    /// Converts this secret key into the corresponding public key.
    #[must_use]
    pub fn to_pk(&self) -> PublicKey {
        let pk = self.0.verification_key();
        PublicKey(pk)
    }

    /// Signs `msg` using this secret key.
    #[must_use]
    pub fn sign(&self, msg: &impl Signable) -> Signature {
        self.sign_bytes(&msg.bytes_to_sign())
    }

    /// Signs the raw byte string `msg` using this secret key.
    ///
    /// Prefer [`sign`](Self::sign) if possible.
    #[must_use]
    pub fn sign_bytes(&self, msg: &[u8]) -> Signature {
        let sig = self.0.sign(msg);
        Signature(sig)
    }

    /// Returns the bytes of this secret key.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; 32] {
        self.0.as_bytes()
    }
}

impl PublicKey {
    /// Returns the bytes of this public key.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; 32] {
        // `ed25519_zebra::VerificationKey` exposes its bytes as `&[u8]`; the key
        // is always 32 bytes, so reborrowing into `&[u8; 32]` cannot fail.
        self.0
            .as_ref()
            .try_into()
            .expect("verification key is always 32 bytes")
    }
}

impl Signature {
    /// Verifies that this is a valid signature of `msg` under `pk`.
    #[must_use]
    pub fn verify(&self, msg: &impl Signable, pk: &PublicKey) -> bool {
        self.verify_bytes(&msg.bytes_to_sign(), pk)
    }

    /// Verifies that this is a valid signature of the raw byte string `msg` under `pk`.
    ///
    /// Prefer [`verify`](Self::verify) if possible.
    #[must_use]
    pub fn verify_bytes(&self, msg: &[u8], pk: &PublicKey) -> bool {
        pk.0.verify(&self.0, msg).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let sk = SecretKey::new(&mut rand::rng());
        let pk = sk.to_pk();
        assert_ne!(sk.as_bytes(), pk.as_bytes());
        let msg = b"ed25519 is pretty fine";
        let sig = sk.sign_bytes(msg);
        assert!(sig.verify_bytes(msg, &pk));
    }

    #[test]
    fn wincode() {
        let sk = SecretKey::new(&mut rand::rng());
        let msg = b"ed25519 is pretty fine";
        let sig = sk.sign_bytes(msg);
        let bytes = wincode::serialize(&sig).unwrap();
        let recovered_sig: Signature = wincode::deserialize(&bytes).unwrap();
        assert_eq!(sig.0.to_bytes(), recovered_sig.0.to_bytes());
    }
}
