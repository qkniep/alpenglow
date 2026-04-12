#![no_main]

use alpenglow::consensus::Vote;
use alpenglow::crypto::aggsig::SecretKey;
use libfuzzer_sys::fuzz_target;

// Fuzz vote signature verification using structure-aware fuzzing.
// Generates a (Vote, key_bytes) pair; the vote may have an arbitrary (likely invalid)
// signature, and we verify it against a BLS public key derived from key_bytes.
//
// Invariant: check_sig must never panic regardless of the vote content or key material.
fuzz_target!(|data: (Vote, [u8; 32])| {
    let (vote, key_bytes) = data;
    // Derive a key pair from the fuzzer-controlled bytes; skip if not a valid BLS scalar.
    let Ok(sk) = SecretKey::try_from_bytes(&key_bytes) else {
        return;
    };
    let pk = sk.to_pk();
    // Must not panic; may return false for arbitrary (likely invalid) vote signatures.
    let _ = vote.check_sig(&pk);
});
