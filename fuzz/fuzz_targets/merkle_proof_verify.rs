#![no_main]

use alpenglow::crypto::Hash;
use alpenglow::crypto::merkle::{MAX_MERKLE_TREE_HEIGHT, PlainMerkleTree};
use libfuzzer_sys::fuzz_target;

// Fuzz Merkle proof verification with structure-aware inputs.
// Hash values are generated as typed 32-byte arrays (not raw bytes mangled into a usize index).
// The proof depth is capped at MAX_MERKLE_TREE_HEIGHT to match the tree implementation.
//
// Invariant: check_proof and check_proof_last must never panic for any well-typed input.
fuzz_target!(|data: (Vec<u8>, usize, Hash, Vec<Hash>)| {
    let (leaf, index, root, proof) = data;
    if proof.len() > MAX_MERKLE_TREE_HEIGHT {
        return;
    }
    let _ = PlainMerkleTree::check_proof(&leaf, index, &root, &proof);
    let _ = PlainMerkleTree::check_proof_last(&leaf, index, &root, &proof);
});
