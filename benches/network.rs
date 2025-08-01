// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::Slot;
use alpenglow::consensus::Vote;
use alpenglow::crypto::{Hash, aggsig, signature};
use alpenglow::network::NetworkMessage;
use alpenglow::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
use alpenglow::slice::Slice;
use divan::counter::{BytesCount, ItemsCount};
use rand::RngCore;

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
            NetworkMessage::Vote(Vote::new_notar(Slot::new(0), hash, &sk, 0))
        })
        .bench_values(|msg: NetworkMessage| msg.to_bytes());
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
            let msg = NetworkMessage::Vote(Vote::new_notar(Slot::new(0), hash, &sk, 0));
            msg.to_bytes()
        })
        .bench_values(|bytes: Vec<u8>| NetworkMessage::from_bytes(&bytes));
}

#[divan::bench]
fn serialize_slice(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(MAX_DATA_PER_SLICE))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let mut slice_data = vec![0; MAX_DATA_PER_SLICE];
            rng.fill_bytes(&mut slice_data);
            let slice = Slice {
                slot: Slot::new(0),
                slice_index: 0,
                is_last: true,
                merkle_root: None,
                data: slice_data,
            };
            let sk = signature::SecretKey::new(&mut rng);
            let shreds = RegularShredder::shred(slice, &sk).unwrap();
            shreds.into_iter().map(NetworkMessage::Shred).collect()
        })
        .bench_values(|msgs: Vec<NetworkMessage>| {
            for msg in msgs {
                let _ = msg.to_bytes();
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
            let mut slice_data = vec![0; MAX_DATA_PER_SLICE];
            rng.fill_bytes(&mut slice_data);
            let slice = Slice {
                slot: Slot::new(0),
                slice_index: 0,
                is_last: true,
                merkle_root: None,
                data: slice_data,
            };
            let sk = signature::SecretKey::new(&mut rng);
            let shreds = RegularShredder::shred(slice, &sk).unwrap();
            let buf = vec![0; 1500];
            let msgs = shreds.into_iter().map(NetworkMessage::Shred).collect();
            (buf, msgs)
        })
        .bench_values(|(mut buf, msgs): (Vec<u8>, Vec<NetworkMessage>)| {
            for msg in msgs {
                let _ =
                    bincode::serde::encode_into_slice(msg, &mut buf, bincode::config::standard())
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
            let mut slice_data = vec![0; MAX_DATA_PER_SLICE];
            rng.fill_bytes(&mut slice_data);
            let slice = Slice {
                slot: Slot::new(0),
                slice_index: 0,
                is_last: true,
                merkle_root: None,
                data: slice_data,
            };
            let sk = signature::SecretKey::new(&mut rng);
            let shreds = RegularShredder::shred(slice, &sk).unwrap();
            let msgs: Vec<_> = shreds.into_iter().map(NetworkMessage::Shred).collect();
            let mut serialized = Vec::new();
            for msg in msgs {
                serialized.push(msg.to_bytes());
            }
            serialized
        })
        .bench_values(|serialized: Vec<Vec<u8>>| {
            for bytes in serialized {
                let _ = NetworkMessage::from_bytes(&bytes);
            }
        });
}
