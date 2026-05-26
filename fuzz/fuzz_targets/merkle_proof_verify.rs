#![no_main]

use alpenglow::crypto::Hash;
use alpenglow::crypto::merkle::PlainMerkleTree;
use libfuzzer_sys::fuzz_target;

// Fuzz Merkle proof verification with structured inputs.
// Consumes raw bytes to construct a leaf, root hash, proof hashes, and index,
// then calls both `check_proof` and `check_proof_last` to ensure they never
// panic on any combination of inputs.
fuzz_target!(|data: &[u8]| {
    // Need at least: 1 byte index + 1 byte leaf_len + 32 bytes root + 32 bytes (one proof hash)
    if data.len() < 66 {
        return;
    }

    let index = data[0] as usize;
    let leaf_len = data[1] as usize;
    let rest = &data[2..];

    if rest.len() < leaf_len + 32 {
        return;
    }

    let leaf = rest[..leaf_len].to_vec();
    let root_bytes = &rest[leaf_len..leaf_len + 32];
    let proof_bytes = &rest[leaf_len + 32..];

    // Each proof hash is 32 bytes; limit proof depth to MAX_MERKLE_TREE_HEIGHT (32)
    let num_hashes = proof_bytes.len() / 32;
    if num_hashes == 0 || num_hashes > 32 {
        return;
    }

    // Deserialize root and proof hashes via wincode (Hash is SchemaRead)
    let Ok(root) = wincode::deserialize::<Hash>(root_bytes) else {
        return;
    };
    let proof: Result<Vec<Hash>, _> = (0..num_hashes)
        .map(|i| wincode::deserialize::<Hash>(&proof_bytes[i * 32..(i + 1) * 32]))
        .collect();
    let Ok(proof) = proof else {
        return;
    };

    // These must never panic regardless of input
    let _ = PlainMerkleTree::check_proof(&leaf, index, &root, &proof);
    let _ = PlainMerkleTree::check_proof_last(&leaf, index, &root, &proof);
});
