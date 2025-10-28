// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::crypto::merkle::{SliceMerkleTree, SliceProof};
use alpenglow::crypto::{IndividualSignature, Signature, aggsig, hash, signature};
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
            let _ = SliceMerkleTree::new(&leaves);
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
            SliceMerkleTree::new(&leaves)
        })
        .bench_values(|tree: SliceMerkleTree| tree.create_proof(0));
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
            let tree = SliceMerkleTree::new(&leaves);
            let proof = tree.create_proof(0);
            (tree, leaves[0].clone(), 0, proof)
        })
        .bench_values(
            |(tree, data, index, proof): (SliceMerkleTree, Vec<u8>, usize, SliceProof)| {
                SliceMerkleTree::check_proof(&data, index, &tree.get_root(), &proof)
            },
        );
}

#[divan::bench]
fn sign_ed25519(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut bytes = [0; 128];
            rng.fill_bytes(&mut bytes);
            let sk = signature::SecretKey::new(&mut rng);
            (sk, bytes)
        })
        .bench_values(|(sk, bytes): (signature::SecretKey, [u8; 128])| {
            let _ = sk.sign(&bytes);
        });
}

#[divan::bench]
fn verify_ed25519(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut bytes = [0; 128];
            rng.fill_bytes(&mut bytes);
            let sk = signature::SecretKey::new(&mut rng);
            (sk.sign(&bytes), bytes, sk.to_pk())
        })
        .bench_values(
            |(sig, bytes, pk): (Signature, [u8; 128], signature::PublicKey)| {
                sig.verify(&bytes, &pk)
            },
        );
}

#[divan::bench(consts = [100, 1000, 10_000])]
fn aggregate_bls<const N: usize>(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut bytes = [0; 128];
            let mut pks = Vec::new();
            for _ in 0..N {
                rng.fill_bytes(&mut bytes);
                let sk = blst::min_pk::SecretKey::key_gen(&bytes, &[]).unwrap();
                pks.push(sk.sk_to_pk());
            }
            pks
        })
        .bench_values(|pks: Vec<blst::min_pk::PublicKey>| {
            let pk_refs: Vec<_> = pks.iter().collect();
            blst::min_pk::AggregatePublicKey::aggregate(&pk_refs, false)
        });
}

#[divan::bench]
fn compress_bls(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut ikm = [0; 32];
            let mut msg = [0; 32];
            rng.fill_bytes(&mut ikm);
            rng.fill_bytes(&mut msg);
            let sk = blst::min_sig::SecretKey::key_gen(&ikm, &[]).unwrap();
            sk.sign(&msg, &[], &[])
        })
        .bench_values(|sig: blst::min_sig::Signature| sig.compress());
}

#[divan::bench]
fn uncompress_bls(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut ikm = [0; 32];
            let mut msg = [0; 32];
            rng.fill_bytes(&mut ikm);
            rng.fill_bytes(&mut msg);
            let sk = blst::min_sig::SecretKey::key_gen(&ikm, &[]).unwrap();
            let sig = sk.sign(&msg, &[], &[]);
            sig.compress()
        })
        .bench_values(|comp: [u8; 48]| blst::min_sig::Signature::uncompress(&comp));
}

#[divan::bench]
fn sign_bls(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut bytes = [0; 128];
            rng.fill_bytes(&mut bytes);
            let sk = aggsig::SecretKey::new(&mut rng);
            (sk, bytes)
        })
        .bench_values(|(sk, bytes): (aggsig::SecretKey, [u8; 128])| {
            let _ = sk.sign(&bytes);
        });
}

#[divan::bench]
fn verify_bls(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut bytes = [0; 128];
            rng.fill_bytes(&mut bytes);
            let sk = aggsig::SecretKey::new(&mut rng);
            (sk.sign(&bytes), bytes, sk.to_pk())
        })
        .bench_values(
            |(sig, bytes, pk): (IndividualSignature, [u8; 128], aggsig::PublicKey)| {
                sig.verify(&bytes, &pk)
            },
        );
}
