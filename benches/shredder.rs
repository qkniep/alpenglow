// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::crypto::signature::SecretKey;
use alpenglow::shredder::{
    AontShredder, CodingOnlyShredder, DATA_SHREDS, PetsShredder, RegularShredder, Shredder,
    TOTAL_SHREDS, ValidatedShred,
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
            let shredder = S::default();
            (shredder, slice, sk)
        })
        .bench_values(|(mut shredder, slice, sk): (S, Slice, SecretKey)| {
            let _ = shredder.shred(slice, &sk).unwrap();
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
            let mut shredder = S::default();
            let mut shreds = shredder.shred(slice, &sk).unwrap().map(Some);
            // need at least DATA_SHREDS to reconstruct and want to include as many coding shreds as possible which should be at the end of the array
            // so mark the first TOTAL_SHREDS - DATA_SHREDS as None
            for shred in shreds.iter_mut().take(TOTAL_SHREDS - DATA_SHREDS) {
                *shred = None;
            }
            (shredder, shreds)
        })
        .bench_values(
            |(mut shredder, shreds): (S, [Option<ValidatedShred>; TOTAL_SHREDS])| {
                let _ = shredder.deshred(&shreds).unwrap();
            },
        );
}
