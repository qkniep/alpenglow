// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Benchmarks the per-shred verification path.
//!
//! `try_new_cold` measures the cost callers pay today — every shred goes
//! through a full Ed25519 verify because [`ShredVerifier`] passes `None` for
//! the cached Merkle root.
//!
//! `try_new_warm` measures the cost a future shared `SliceRootCache` could
//! deliver: when a previously verified root for the slice is already known,
//! [`ValidatedShred::try_new`] short-circuits on a root comparison without
//! touching Ed25519.
//!
//! `slice_cold` / `slice_warm` repeat the same comparison across a full slice
//! (one shred per index) so the gap reflects the amortization opportunity at
//! slice granularity, where dissemination typically delivers many shreds with
//! the same Merkle root.

use alpenglow::crypto::merkle::SliceRoot;
use alpenglow::crypto::signature::{PublicKey, SecretKey};
use alpenglow::shredder::{
    MAX_DATA_PER_SLICE, RegularShredder, Shred, Shredder, TOTAL_SHREDS, ValidatedShred,
};
use alpenglow::types::slice::create_slice_with_invalid_txs;
use divan::counter::ItemsCount;

fn main() {
    divan::main();
}

fn one_shred() -> (Shred, PublicKey, SliceRoot) {
    let mut shredder = RegularShredder::default();
    let sk = SecretKey::new(&mut rand::rng());
    let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
    let shreds = shredder.shred(slice, &sk).unwrap();
    let pk = sk.to_pk();
    let merkle_root = shreds[0].merkle_root().clone();
    let shred = shreds[0].clone().into_shred();
    (shred, pk, merkle_root)
}

fn slice_shreds() -> ([Shred; TOTAL_SHREDS], PublicKey, SliceRoot) {
    let mut shredder = RegularShredder::default();
    let sk = SecretKey::new(&mut rand::rng());
    let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
    let validated = shredder.shred(slice, &sk).unwrap();
    let pk = sk.to_pk();
    let merkle_root = validated[0].merkle_root().clone();
    let shreds: [Shred; TOTAL_SHREDS] =
        validated.map(alpenglow::shredder::ValidatedShred::into_shred);
    (shreds, pk, merkle_root)
}

/// Cost of verifying a single shred without a cached Merkle root.
/// This is what [`ShredVerifier`] does today.
#[divan::bench]
fn try_new_cold(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let (shred, pk, _root) = one_shred();
            (shred, pk)
        })
        .bench_values(|(shred, pk): (Shred, PublicKey)| {
            ValidatedShred::try_new(shred, None, &pk).unwrap()
        });
}

/// Cost of verifying a single shred when its slice's root is already cached
/// and matches. This is the fast path we'd recover with a `SliceRootCache`.
#[divan::bench]
fn try_new_warm(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let (shred, pk, root) = one_shred();
            (shred, pk, root)
        })
        .bench_values(|(shred, pk, root): (Shred, PublicKey, SliceRoot)| {
            ValidatedShred::try_new(shred, Some(&root), &pk).unwrap()
        });
}

/// Cost of verifying every shred in a full slice with no cache. Reflects the
/// worst-case current behavior when a node receives many shreds of the same
/// slice: every shred pays an independent Ed25519 verify.
#[divan::bench]
fn slice_cold(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(TOTAL_SHREDS))
        .with_inputs(|| {
            let (shreds, pk, _root) = slice_shreds();
            (shreds, pk)
        })
        .bench_values(|(shreds, pk): ([Shred; TOTAL_SHREDS], PublicKey)| {
            for shred in shreds {
                let _ = ValidatedShred::try_new(shred, None, &pk).unwrap();
            }
        });
}

/// Cost of verifying every shred in a full slice with the slice's root cached
/// from the first shred onward. Reflects the achievable behavior with a
/// shared cache: one Ed25519 verify per slice, then root comparisons.
#[divan::bench]
fn slice_warm(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(TOTAL_SHREDS))
        .with_inputs(|| {
            let (shreds, pk, root) = slice_shreds();
            (shreds, pk, root)
        })
        .bench_values(|(shreds, pk, root): ([Shred; TOTAL_SHREDS], PublicKey, SliceRoot)| {
            for shred in shreds {
                let _ = ValidatedShred::try_new(shred, Some(&root), &pk).unwrap();
            }
        });
}
