// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::mem::MaybeUninit;

use alpenglow::consensus::{ConsensusMessage, Vote};
use alpenglow::crypto::{Hash, aggsig, signature};
use alpenglow::network::BINCODE_CONFIG;
use alpenglow::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shred, Shredder};
use alpenglow::types::Slot;
use alpenglow::types::slice::create_slice_with_invalid_txs;
use divan::counter::{BytesCount, ItemsCount};
use rand::{Rng, RngCore};
use serde::{Deserialize, Serialize};
use wincode::{SchemaRead, SchemaWrite};

fn main() {
    // run registered benchmarks.
    divan::main();
}

#[divan::bench]
fn serialize_vote(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut hash = Hash::default();
            rng.fill_bytes(&mut hash);
            let sk = aggsig::SecretKey::new(&mut rng);
            let vote = Vote::new_notar(Slot::new(0), hash, &sk, 0);
            ConsensusMessage::Vote(vote)
        })
        .bench_values(|msg: ConsensusMessage| bincode::serde::encode_to_vec(msg, BINCODE_CONFIG));
}

#[divan::bench]
fn deserialize_vote(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut hash = Hash::default();
            rng.fill_bytes(&mut hash);
            let sk = aggsig::SecretKey::new(&mut rng);
            let vote = Vote::new_notar(Slot::new(0), hash, &sk, 0);
            let msg = ConsensusMessage::Vote(vote);
            bincode::serde::encode_to_vec(msg, BINCODE_CONFIG).unwrap()
        })
        .bench_values(|bytes: Vec<u8>| {
            let (_msg, _bytes_read): (ConsensusMessage, usize) =
                bincode::serde::decode_from_slice(&bytes, BINCODE_CONFIG).unwrap();
        });
}

#[divan::bench]
fn serialize_vote_wincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut hash = Hash::default();
            rng.fill_bytes(&mut hash);
            let sk = aggsig::SecretKey::new(&mut rng);
            let vote = Vote::new_notar(Slot::new(0), hash, &sk, 0);
            ConsensusMessage::Vote(vote)
        })
        .bench_values(|msg: ConsensusMessage| wincode::serialize(&msg).unwrap());
}

#[divan::bench]
fn deserialize_vote_wincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut hash = Hash::default();
            rng.fill_bytes(&mut hash);
            let sk = aggsig::SecretKey::new(&mut rng);
            let vote = Vote::new_notar(Slot::new(0), hash, &sk, 0);
            let msg = ConsensusMessage::Vote(vote);
            wincode::serialize(&msg).unwrap()
        })
        .bench_values(|bytes: Vec<u8>| {
            let _msg: ConsensusMessage = wincode::deserialize(&bytes).unwrap();
        });
}

#[derive(Clone, Debug, Serialize, Deserialize, SchemaRead, SchemaWrite)]
struct FakeCert {
    slot: u64,
    #[wincode(with = "wincode::containers::Pod<[u8; 32]>")]
    hash: Hash,
    #[wincode(with = "wincode::containers::Vec<wincode::containers::Pod<_>>")]
    sig: Vec<u8>,
    #[wincode(with = "wincode::containers::Vec<wincode::containers::Pod<_>>")]
    bitmask: Vec<u8>,
}

impl FakeCert {
    fn new() -> Self {
        let mut rng = rand::rng();
        let mut sig = vec![0; 128];
        rng.fill_bytes(&mut sig);
        let mut bitmask = vec![255; 256];
        for _ in 0..200 {
            let pos = rng.random_range(0..256);
            let shift = rng.random_range(0..8);
            let mask = 1 << shift;
            bitmask[pos] |= 255 ^ mask;
        }
        Self {
            slot: rng.random(),
            hash: rng.random(),
            sig,
            bitmask,
        }
    }
}

#[divan::bench]
fn serialize_fake_cert_bincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(FakeCert::new)
        .bench_values(|msg: FakeCert| bincode::serde::encode_to_vec(msg, BINCODE_CONFIG).unwrap());
}

#[divan::bench]
fn deserialize_fake_cert_bincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let msg = FakeCert::new();
            bincode::serde::encode_to_vec(msg, BINCODE_CONFIG).unwrap()
        })
        .bench_values(|bytes: Vec<u8>| {
            let (_msg, _bytes_read): (FakeCert, usize) =
                bincode::serde::decode_from_slice(&bytes, BINCODE_CONFIG).unwrap();
        });
}

#[divan::bench]
fn serialize_fake_cert_wincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(FakeCert::new)
        .bench_values(|msg: FakeCert| wincode::serialize(&msg).unwrap());
}

#[divan::bench]
fn deserialize_fake_cert_wincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let msg = FakeCert::new();
            wincode::serialize(&msg).unwrap()
        })
        .bench_values(|bytes: Vec<u8>| {
            let _msg: FakeCert = wincode::deserialize(&bytes).unwrap();
        });
}

#[divan::bench]
fn serialize_slice(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(MAX_DATA_PER_SLICE))
        .with_inputs(|| {
            let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
            let mut rng = rand::rng();
            let sk = signature::SecretKey::new(&mut rng);
            RegularShredder::shred(slice, &sk)
                .unwrap()
                .into_iter()
                .map(|v| v.into_shred())
                .collect::<Vec<_>>()
        })
        .bench_values(|shreds: Vec<Shred>| {
            for shred in shreds {
                let _bytes = bincode::serde::encode_to_vec(shred, BINCODE_CONFIG).unwrap();
            }
        });
}

#[divan::bench]
fn serialize_slice_into(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(MAX_DATA_PER_SLICE))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
            let sk = signature::SecretKey::new(&mut rng);
            let shreds = RegularShredder::shred(slice, &sk)
                .unwrap()
                .into_iter()
                .map(|v| v.into_shred())
                .collect::<Vec<_>>();
            let buf = vec![0; 1500];
            (buf, shreds)
        })
        .bench_values(|(mut buf, shreds): (Vec<u8>, Vec<Shred>)| {
            for shred in shreds {
                let _ = bincode::serde::encode_into_slice(shred, &mut buf, BINCODE_CONFIG)
                    .expect("serialization should not panic");
            }
        });
}

#[divan::bench]
fn deserialize_slice(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(MAX_DATA_PER_SLICE))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
            let sk = signature::SecretKey::new(&mut rng);
            let shreds = RegularShredder::shred(slice, &sk).unwrap();
            let mut serialized = Vec::new();
            for shred in shreds {
                let bytes =
                    bincode::serde::encode_to_vec(shred.into_shred(), BINCODE_CONFIG).unwrap();
                serialized.push(bytes);
            }
            serialized
        })
        .bench_values(|serialized: Vec<Vec<u8>>| {
            for bytes in serialized {
                let (_shred, _bytes_read): (Shred, usize) =
                    bincode::serde::decode_from_slice(&bytes, BINCODE_CONFIG).unwrap();
            }
        });
}

#[divan::bench]
fn serialize_slice_wincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(MAX_DATA_PER_SLICE))
        .with_inputs(|| {
            let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
            let mut rng = rand::rng();
            let sk = signature::SecretKey::new(&mut rng);
            RegularShredder::shred(slice, &sk)
                .unwrap()
                .into_iter()
                .map(|v| v.into_shred())
                .collect::<Vec<_>>()
        })
        .bench_values(|shreds: Vec<Shred>| {
            for shred in shreds {
                let _bytes = wincode::serialize(&shred).unwrap();
            }
        });
}

#[divan::bench]
fn serialize_slice_into_wincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(MAX_DATA_PER_SLICE))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
            let sk = signature::SecretKey::new(&mut rng);
            let shreds = RegularShredder::shred(slice, &sk)
                .unwrap()
                .into_iter()
                .map(|v| v.into_shred())
                .collect::<Vec<_>>();
            let buf = vec![MaybeUninit::uninit(); 1500];
            (buf, shreds)
        })
        .bench_values(|(mut buf, shreds): (Vec<MaybeUninit<u8>>, Vec<Shred>)| {
            for shred in shreds {
                let _bytes_written = wincode::serialize_into(&shred, &mut buf)
                    .expect("serialization should not panic");
            }
        });
}

#[divan::bench]
fn deserialize_slice_wincode(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(MAX_DATA_PER_SLICE))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
            let sk = signature::SecretKey::new(&mut rng);
            let shreds = RegularShredder::shred(slice, &sk).unwrap();
            let mut serialized = Vec::new();
            for shred in shreds {
                let bytes = wincode::serialize(&shred.into_shred()).unwrap();
                serialized.push(bytes);
            }
            serialized
        })
        .bench_values(|serialized: Vec<Vec<u8>>| {
            for bytes in serialized {
                let _shred: Shred = wincode::deserialize(&bytes).unwrap();
            }
        });
}
