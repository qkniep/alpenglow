// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::crypto::signature::SecretKey;
use alpenglow::shredder::{
    AontShredder, CodingOnlyShredder, PetsShredder, RegularShredder, Shredder, TOTAL_SHREDS,
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
            let mut shreds = S::shred(slice, &sk).unwrap().map(Some);
            for shred in shreds.iter_mut() {
                *shred = None;
            }
            shreds
        })
        .bench_values(|shreds: [Option<ValidatedShred>; TOTAL_SHREDS]| {
            let _ = S::deshred(&shreds).unwrap();
        });
}
