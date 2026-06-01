// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Symmetric encryption.
//!
//! This module abstracts the symmetric cipher used throughout the entire library.
//! Currently, AES-128 in CTR mode, specifically the implementation from the
//! [`aes`] and [`ctr`] crates, is used.

use aes::Aes128;
use aes::cipher::{Array, KeyIvInit, StreamCipher};
use ctr::Ctr64LE;
use rand::prelude::*;

/// Number of bytes in a symmetric encryption key.
pub(crate) const KEY_BYTES: usize = 16;

/// Applies the cipher's keystream to `buffer` in place.
///
/// The cipher is a stream cipher, so this performs both encryption and decryption.
///
/// Uses a fixed all-zero IV, so a key must never be used for more than one buffer.
pub(crate) fn apply_keystream(key: [u8; KEY_BYTES], buffer: &mut [u8]) {
    let iv = Array::from([0; 16]);
    let mut cipher = Ctr64LE::<Aes128>::new(&Array::from(key), &iv);
    cipher.apply_keystream(buffer);
}

/// Encrypts `buffer` in place under a freshly generated random key.
///
/// Returns the key, without it the contents of `buffer` cannot be recovered.
#[must_use]
pub(crate) fn encrypt_with_random_key(buffer: &mut [u8]) -> [u8; KEY_BYTES] {
    let mut key = [0; KEY_BYTES];
    rand::rng().fill_bytes(&mut key);
    apply_keystream(key, buffer);
    key
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let plaintext = b"some plaintext payload".to_vec();
        let mut buffer = plaintext.clone();
        let key = encrypt_with_random_key(&mut buffer);
        assert_ne!(buffer, plaintext);
        apply_keystream(key, &mut buffer);
        assert_eq!(buffer, plaintext);
    }

    #[test]
    fn random_keys_differ() {
        let plaintext = b"some plaintext payload".to_vec();
        let mut buffer1 = plaintext.clone();
        let mut buffer2 = plaintext.clone();
        let key1 = encrypt_with_random_key(&mut buffer1);
        let key2 = encrypt_with_random_key(&mut buffer2);
        assert_ne!(key1, key2);
        assert_ne!(buffer1, buffer2);
    }
}
