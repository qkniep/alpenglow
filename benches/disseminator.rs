// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use alpenglow::ValidatorInfo;
use alpenglow::consensus::EpochInfo;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Turbine;
use alpenglow::network::UdpNetwork;
use alpenglow::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
use alpenglow::types::slice::create_slice_with_invalid_txs;
use divan::counter::ItemsCount;

fn main() {
    // run registered benchmarks.
    // TODO: enable once divan supports tokio
    // divan::main();
}

#[divan::bench]
fn turbine_tree(bencher: divan::Bencher) {
    bencher
        .counter(ItemsCount::new(1_usize))
        .with_inputs(|| {
            let net1 = UdpNetwork::new_with_any_port();
            let net2 = UdpNetwork::new_with_any_port();
            let mut rng = rand::rng();
            let addr = alpenglow::network::dontcare_sockaddr();
            let validators: Vec<_> = (0..2)
                .map(|i| ValidatorInfo {
                    id: i,
                    stake: 1,
                    pubkey: SecretKey::new(&mut rng).to_pk(),
                    voting_pubkey: alpenglow::crypto::aggsig::SecretKey::new(&mut rng).to_pk(),
                    all2all_address: addr,
                    disseminator_address: addr,
                    repair_request_address: addr,
                    repair_response_address: addr,
                })
                .collect();
            let epoch_info = Arc::new(EpochInfo::new(0, validators));
            let turbine1 = Turbine::new(net1, epoch_info.clone());
            let turbine2 = Turbine::new(net2, epoch_info);

            let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);
            let mut rng = rand::rng();
            let sk = SecretKey::new(&mut rng);
            let shreds = RegularShredder::default().shred(slice, &sk).unwrap();
            let shred = shreds[shreds.len() - 1].clone();

            (shred, turbine1, turbine2)
        })
        .bench_values(|(shred, turbine1, _turbine2)| {
            futures::executor::block_on(turbine1.send_shred_to_root(&shred)).unwrap()
        });
}
