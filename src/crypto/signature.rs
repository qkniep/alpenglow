// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of a digital signature scheme.
//!
//! This module abstratcs the digital signatures used throughout the entire library.
//! Currently, it provides Ed25519 digital signature scheme, as specified in [RFC 8032].
//! Specifically, it is a wrapper around the [`ed25519_consensus`] crate.
//!
//! [RFC 8032]: https://tools.ietf.org/html/rfc8032

use ed25519_consensus::{SigningKey, VerificationKey};
use rand::CryptoRng;
use serde::{Deserialize, Serialize};
use wincode::containers::Pod;
use wincode::{SchemaRead, SchemaWrite};

/// Secret key for the digital signature scheme.
///
/// This is a wrapper around [`ed25519_consensus::SigningKey`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SecretKey(SigningKey);

/// Public key for the digital signature scheme.
///
/// This is a wrapper around [`ed25519_consensus::VerificationKey`].
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct PublicKey(VerificationKey);

/// Digital signature.
///
/// This is a wrapper around [`ed25519_consensus::Signature`].
#[derive(Clone, Copy, Debug, SchemaRead, SchemaWrite)]
pub struct Signature(#[wincode(with = "Pod<_>")] ed25519_consensus::Signature);

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

    /// Signs the byte string `msg` using this secret key.
    // TODO: use `Signable` here, and add new `sign_bytes` function?
    #[must_use]
    pub fn sign(&self, msg: &[u8]) -> Signature {
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
        self.0.as_bytes()
    }
}

impl Signature {
    /// Verifies that this is a valid signature of `msg` under `pk`.
    #[must_use]
    pub fn verify(&self, msg: &[u8], pk: &PublicKey) -> bool {
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
        let sig = sk.sign(msg);
        assert!(sig.verify(msg, &pk));
    }
}
