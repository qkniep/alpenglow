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
use rand::Rng;
use rand::rngs::ThreadRng;
use reed_solomon_simd::{ReedSolomonDecoder, ReedSolomonEncoder};

fn main() {
    divan::main();
}

#[divan::bench()]
fn test(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut rng = rand::rng();
            let shredder = ReedSolomonEncoder::new(1200, 2000, 32).unwrap();
            let shards: Vec<[u8; 32]> = (0..1200).map(|_| rng.random()).collect();
            (shredder, shards, rng)
        })
        .bench_values(
            |(mut shredder, shards, _rng): (ReedSolomonEncoder, Vec<[u8; 32]>, ThreadRng)| {
                for shard in shards {
                    shredder.add_original_shard(shard).unwrap();
                }
                let _ = shredder.encode().unwrap();
            },
        );
}

#[divan::bench()]
fn test2(bencher: divan::Bencher) {
    bencher
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut shredder = ReedSolomonEncoder::new(1200, 2000, 32).unwrap();
            let shards: Vec<[u8; 32]> = (0..1200).map(|_| rng.random()).collect();
            for shard in shards.iter() {
                shredder.add_original_shard(shard).unwrap();
            }
            let res = shredder.encode().unwrap();
            let recovered = res.recovery_iter().map(|s| s.to_vec()).collect::<Vec<_>>();
            let deshredder = ReedSolomonDecoder::new(1200, 2000, 32).unwrap();
            (deshredder, shards, recovered)
        })
        .bench_values(
            |(mut deshredder, shards, recovered): (
                ReedSolomonDecoder,
                Vec<[u8; 32]>,
                Vec<Vec<u8>>,
            )| {
                for (i, shard) in shards.iter().enumerate().skip(200) {
                    deshredder.add_original_shard(i, shard).unwrap();
                }
                for (i, shard) in recovered.iter().enumerate().take(200) {
                    deshredder.add_recovery_shard(i, shard).unwrap();
                }
                let _ = deshredder.decode().unwrap();
            },
        );
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
