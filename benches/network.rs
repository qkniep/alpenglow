// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::consensus::{Cert, ConsensusMessage, NotarCert, Vote};
use alpenglow::crypto::aggsig::SecretKey;
use alpenglow::crypto::merkle::GENESIS_BLOCK_HASH;
use alpenglow::crypto::{aggsig, signature};
use alpenglow::network::localhost_ip_sockaddr;
use alpenglow::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shred, Shredder};
use alpenglow::types::Slot;
use alpenglow::types::slice::create_slice_with_invalid_txs;
use alpenglow::{ValidatorId, ValidatorInfo};
use divan::counter::{BytesCount, ItemsCount};

fn main() {
    // run registered benchmarks.
    divan::main();
}

fn generate_vote() -> Vote {
    let mut rng = rand::rng();
    let hash = GENESIS_BLOCK_HASH;
    let sk = aggsig::SecretKey::new(&mut rng);
    Vote::new_notar(Slot::new(0), hash, &sk, 0)
}

#[divan::bench]
fn serialize_vote(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| ConsensusMessage::Vote(generate_vote()))
        .bench_values(|msg: ConsensusMessage| wincode::serialize(&msg).unwrap());
}

#[divan::bench]
fn deserialize_vote(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let msg = ConsensusMessage::Vote(generate_vote());
            wincode::serialize(&msg).unwrap()
        })
        .bench_values(|bytes: Vec<u8>| {
            let _msg: ConsensusMessage = wincode::deserialize(&bytes).unwrap();
        });
}

fn generate_cert() -> Cert {
    let (sks, val_info) = generate_validators(100);

    let hash = GENESIS_BLOCK_HASH;
    let votes = sks
        .iter()
        .enumerate()
        .map(|(v, sk)| Vote::new_notar(Slot::new(0), hash.clone(), sk, v as ValidatorId))
        .collect::<Vec<_>>();
    let notar_cert = NotarCert::try_new(&votes, &val_info).unwrap();
    Cert::Notar(notar_cert)
}

#[divan::bench]
fn serialize_cert(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| ConsensusMessage::Cert(generate_cert()))
        .bench_values(|msg: ConsensusMessage| wincode::serialize(&msg).unwrap());
}

#[divan::bench]
fn deserialize_cert(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let msg = ConsensusMessage::Cert(generate_cert());
            wincode::serialize(&msg).unwrap()
        })
        .bench_values(|bytes: Vec<u8>| {
            let _msg: ConsensusMessage = wincode::deserialize(&bytes).unwrap();
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
            RegularShredder::default()
                .shred(slice, &sk)
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
fn serialize_slice_into(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(MAX_DATA_PER_SLICE))
        .with_inputs(|| {
            let mut rng = rand::rng();
            let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
            let sk = signature::SecretKey::new(&mut rng);
            let shreds = RegularShredder::default()
                .shred(slice, &sk)
                .unwrap()
                .into_iter()
                .map(|v| v.into_shred())
                .collect::<Vec<_>>();
            let buf = vec![0; 1500];
            (buf, shreds)
        })
        .bench_values(|(mut buf, shreds): (Vec<u8>, Vec<Shred>)| {
            for shred in shreds {
                wincode::serialize_into(&mut buf, &shred).expect("serialization should not panic");
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
            let shreds = RegularShredder::default().shred(slice, &sk).unwrap();
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

pub fn generate_validators(num_validators: u64) -> (Vec<SecretKey>, Vec<ValidatorInfo>) {
    let mut rng = rand::rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut validators = Vec::new();
    for i in 0..num_validators {
        sks.push(signature::SecretKey::new(&mut rng));
        voting_sks.push(SecretKey::new(&mut rng));
        validators.push(ValidatorInfo {
            id: i,
            stake: 1,
            pubkey: sks[i as usize].to_pk(),
            voting_pubkey: voting_sks[i as usize].to_pk(),
            all2all_address: localhost_ip_sockaddr(0),
            disseminator_address: localhost_ip_sockaddr(0),
            repair_request_address: localhost_ip_sockaddr(0),
            repair_response_address: localhost_ip_sockaddr(0),
        });
    }
    (voting_sks, validators)
}
