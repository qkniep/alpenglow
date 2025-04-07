// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::crypto::aggsig::{PublicKey, SecretKey};
use alpenglow::crypto::{Hash, MerkleTree, Signature, hash};
use alpenglow::shredder::{MAX_DATA_PER_SHRED, MAX_DATA_PER_SLICE};
use divan::counter::{BytesCount, ItemsCount};
use rand::RngCore;

fn main() {
    // run registered benchmarks.
    divan::main();
}

#[divan::bench(name = "hash", consts = [16, 32, MAX_DATA_PER_SHRED, MAX_DATA_PER_SLICE])]
fn hash_bytes<const N: usize>(bencher: divan::Bencher) {
    bencher
        .counter(BytesCount::new(N))
        .with_inputs(|| (0..N).map(|_| rand::random::<u8>()).collect())
        .bench_values(|s: Vec<u8>| hash(&s));
}

#[divan::bench(consts = [64, 512, 1024])]
fn merkle_tree<const N: usize>(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut leaves = vec![Vec::new(); N];
            for leaf in &mut leaves {
                rng.fill_bytes(leaf);
            }
            leaves
        })
        .bench_values(|leaves: Vec<Vec<u8>>| {
            let _ = MerkleTree::new(&leaves);
        });
}

#[divan::bench(consts = [64, 512, 1024])]
fn merkle_proof<const N: usize>(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut leaves = vec![Vec::new(); N];
            for leaf in &mut leaves {
                rng.fill_bytes(leaf);
            }
            MerkleTree::new(&leaves)
        })
        .bench_values(|tree: MerkleTree| tree.create_proof(0));
}

#[divan::bench(consts = [64, 512, 1024])]
fn merkle_verify<const N: usize>(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut leaves = vec![Vec::new(); N];
            for leaf in &mut leaves {
                rng.fill_bytes(leaf);
            }
            let tree = MerkleTree::new(&leaves);
            let proof = tree.create_proof(0);
            (tree, leaves[0].clone(), 0, proof)
        })
        .bench_values(
            |(tree, data, index, proof): (MerkleTree, Vec<u8>, usize, Vec<Hash>)| {
                MerkleTree::check_proof(&data, index, tree.get_root(), &proof)
            },
        );
}

#[divan::bench]
fn sign(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut bytes = [0; 128];
            rng.fill_bytes(&mut bytes);
            let sk = SecretKey::new(&mut rng);
            (sk, bytes)
        })
        .bench_values(|(sk, bytes): (SecretKey, [u8; 128])| {
            let _ = sk.sign(&bytes);
        });
}

#[divan::bench]
fn verify_sig(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut bytes = [0; 128];
            rng.fill_bytes(&mut bytes);
            let sk = SecretKey::new(&mut rng);
            (sk.sign(&bytes), bytes, sk.to_pk())
        })
        .bench_values(|(sig, bytes, pk): (Signature, [u8; 128], PublicKey)| {
            sig.verify(&bytes, &pk)
        });
}
