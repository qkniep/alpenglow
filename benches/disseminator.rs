// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::Slot;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Turbine;
use alpenglow::network::UdpNetwork;
use alpenglow::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
use alpenglow::slice::Slice;
use divan::counter::ItemsCount;
use rand::RngCore;

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
            let turbine1 = Turbine::new(0, Vec::new(), net1);
            let turbine2 = Turbine::new(1, Vec::new(), net2);

            let mut rng = rand::rng();
            let mut slice_data = vec![0; MAX_DATA_PER_SLICE];
            rng.fill_bytes(&mut slice_data);
            let slice = Slice {
                slot: Slot::new(0),
                slice_index: 0,
                is_last: true,
                merkle_root: None,
                parent: None,
                data: slice_data,
            };
            let sk = SecretKey::new(&mut rng);
            let mut shreds = RegularShredder::shred(slice, &sk).unwrap();
            let shred = shreds.pop().unwrap();

            (shred, turbine1, turbine2)
        })
        .bench_values(|(shred, turbine1, _turbine2)| {
            futures::executor::block_on(turbine1.send_shred_to_root(&shred)).unwrap()
        });
}
