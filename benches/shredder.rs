// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::crypto::signature::SecretKey;
use alpenglow::shredder::{
    AontShredder, CodingOnlyShredder, DATA_SHREDS, PetsShredder, RegularShredder, Shredder,
    ValidatedShred,
};
use alpenglow::types::Slice;
use alpenglow::types::slice::create_slice_with_invalid_txs;
use divan::counter::BytesCount;

fn main() {
    divan::main();
}

#[divan::bench(types = [RegularShredder, CodingOnlyShredder, PetsShredder, AontShredder])]
fn shred<S: Shredder>(bencher: divan::Bencher) {
    let size = S::MAX_DATA_SIZE;

    bencher
        .counter(BytesCount::new(size))
        .with_inputs(|| {
            let slice = create_slice_with_invalid_txs(size);
            let mut rng = rand::rng();
            let sk = SecretKey::new(&mut rng);
            (slice, sk)
        })
        .bench_values(|(slice, sk): (Slice, SecretKey)| {
            let _ = S::shred(slice, &sk).unwrap();
        });
}

#[divan::bench(types = [RegularShredder, CodingOnlyShredder, PetsShredder, AontShredder])]
fn deshred<S: Shredder>(bencher: divan::Bencher) {
    let size = S::MAX_DATA_SIZE;

    bencher
        .counter(BytesCount::new(size))
        .with_inputs(|| {
            let slice = create_slice_with_invalid_txs(size);
            let mut rng = rand::rng();
            let sk = SecretKey::new(&mut rng);
            S::shred(slice, &sk).unwrap()
        })
        .bench_values(|shreds: Vec<ValidatedShred>| {
            let _ = S::deshred(&shreds[DATA_SHREDS..]).unwrap();
        });
}
