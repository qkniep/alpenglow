// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::crypto::signature::SecretKey;
use alpenglow::shredder::{
    AontShredder, CodingOnlyShredder, DATA_SHREDS, PetsShredder, RegularShredder, Shred, Shredder,
    Slice,
};
use divan::counter::BytesCount;
use rand::prelude::*;

fn main() {
    divan::main();
}

#[divan::bench(types = [RegularShredder, CodingOnlyShredder, PetsShredder, AontShredder])]
fn shred<S: Shredder>(bencher: divan::Bencher) {
    let size = S::MAX_DATA_SIZE;

    bencher
        .counter(BytesCount::new(size))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut slice_data = vec![0; size];
            rng.fill_bytes(&mut slice_data);
            let slice = Slice {
                slot: 0,
                slice_index: 0,
                is_last: true,
                merkle_root: None,
                data: slice_data,
            };
            let sk = SecretKey::new(&mut rng);
            (slice, sk)
        })
        .bench_values(|(slice, sk): (Slice, SecretKey)| {
            let _ = S::shred(&slice, &sk).unwrap();
        });
}

#[divan::bench(types = [RegularShredder, CodingOnlyShredder, PetsShredder, AontShredder])]
fn deshred<S: Shredder>(bencher: divan::Bencher) {
    let size = S::MAX_DATA_SIZE;

    bencher
        .counter(BytesCount::new(size))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut slice_data = vec![0; size];
            rng.fill_bytes(&mut slice_data);
            let slice = Slice {
                slot: 0,
                slice_index: 0,
                is_last: true,
                merkle_root: None,
                data: slice_data,
            };
            let sk = SecretKey::new(&mut rng);
            S::shred(&slice, &sk).unwrap()
        })
        .bench_values(|shreds: Vec<Shred>| {
            let _ = S::deshred(&shreds[DATA_SHREDS..]).unwrap();
        });
}
