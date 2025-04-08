// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of a digital signature scheme.
//!
//!

use ed25519_consensus::{SigningKey, VerificationKey};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};

/// A secret key for the digital signature scheme.
///
/// This is a wrapper around [`ed25519_consensus::SigningKey`].
#[derive(Clone, Debug)]
pub struct SecretKey(SigningKey);

/// A public key for the digital signature scheme.
///
/// This is a wrapper around [`ed25519_consensus::VerificationKey`].
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct PublicKey(VerificationKey);

/// A digital signature.
///
/// This is a wrapper around [`ed25519_consensus::Signature`].
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct Signature(ed25519_consensus::Signature);

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
}

impl AsRef<VerificationKey> for PublicKey {
    fn as_ref(&self) -> &VerificationKey {
        &self.0
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
        let msg = b"ed25519 is pretty fine";
        let sig = sk.sign(msg);
        assert!(sig.verify(msg, &pk));
    }
}
