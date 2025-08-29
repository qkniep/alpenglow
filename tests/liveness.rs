// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;
use std::sync::Arc;
use std::time::Duration;

use alpenglow::all2all::TrivialAll2All;
use alpenglow::consensus::EpochInfo;
use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Rotor;
use alpenglow::disseminator::rotor::StakeWeightedSampler;
use alpenglow::network::{UdpNetwork, localhost_ip_sockaddr};
use alpenglow::types::Slot;
use alpenglow::{Alpenglow, ValidatorInfo};
use log::debug;
use rand::prelude::*;

#[tokio::test]
#[ignore]
async fn only_correct_nodes() {
    liveness_test(6, 0).await;
}

#[tokio::test]
#[ignore]
async fn single_crash() {
    liveness_test(11, 1).await;
}

#[tokio::test]
#[ignore]
async fn max_fast_crashes() {
    liveness_test(11, 2).await;
}

#[tokio::test]
#[ignore]
async fn too_many_fast_crashes() {
    liveness_test(11, 3).await;
}

#[tokio::test]
#[ignore]
async fn max_crashes() {
    liveness_test(11, 4).await;
}

#[tokio::test]
#[ignore]
async fn three_nodes() {
    liveness_test(3, 0).await;
}

#[tokio::test]
#[ignore]
async fn three_nodes_crash() {
    liveness_test(3, 1).await;
}

// TODO: implement transient failure test
//
// #[tokio::test]
// async fn transient_failure() {
//     liveness_test(11, 1).await;
// }

type TestNode =
    Alpenglow<TrivialAll2All<UdpNetwork>, Rotor<UdpNetwork, StakeWeightedSampler>, UdpNetwork>;

fn create_test_nodes(count: u64) -> Vec<TestNode> {
    // open sockets with arbitrary ports
    let mut networks = VecDeque::new();
    for _ in 0..4 * count {
        networks.push_back(UdpNetwork::new_with_any_port());
    }

    // prepare validator info for all nodes
    let mut rng = rand::rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut validators = Vec::new();
    for id in 0..count {
        sks.push(SecretKey::new(&mut rng));
        voting_sks.push(aggsig::SecretKey::new(&mut rng));
        let a2a_port = networks[4 * id as usize].port();
        let dis_port = networks[4 * id as usize + 1].port();
        let rep_port = networks[4 * id as usize + 2].port();
        validators.push(ValidatorInfo {
            id,
            stake: 1,
            pubkey: sks[id as usize].to_pk(),
            voting_pubkey: voting_sks[id as usize].to_pk(),
            all2all_address: localhost_ip_sockaddr(a2a_port),
            disseminator_address: localhost_ip_sockaddr(dis_port),
            repair_address: localhost_ip_sockaddr(rep_port),
        });
    }

    // turn validator info into actual nodes
    validators
        .iter()
        .map(|v| {
            let epoch_info = Arc::new(EpochInfo::new(v.id, validators.clone()));
            let all2all = TrivialAll2All::new(validators.clone(), networks.pop_front().unwrap());
            let disseminator = Rotor::new(networks.pop_front().unwrap(), epoch_info.clone());
            let repair_network = networks.pop_front().unwrap();
            let txs_receiver = networks.pop_front().unwrap();
            Alpenglow::new(
                sks[v.id as usize].clone(),
                voting_sks[v.id as usize].clone(),
                all2all,
                disseminator,
                repair_network,
                epoch_info,
                txs_receiver,
            )
        })
        .collect()
}

async fn liveness_test(num_nodes: usize, num_crashes: usize) {
    liveness_test_internal(num_nodes, num_crashes, true).await
}

async fn liveness_test_internal(num_nodes: usize, num_crashes: usize, should_succeed: bool) {
    // start `num_nodes` nodes
    let nodes = create_test_nodes(num_nodes as u64);
    let mut node_cancel_tokens = Vec::new();
    let mut pools = Vec::new();
    for node in nodes {
        pools.push(node.get_pool());
        node_cancel_tokens.push(node.get_cancel_token());
        tokio::spawn(node.run());
    }

    // spawn a thread checking pool for progress
    let cancel_tokens = node_cancel_tokens.clone();
    let mut liveness_tester = tokio::spawn(async move {
        let mut finalized = vec![Slot::new(0); pools.len()];
        for t in 1.. {
            tokio::time::sleep(Duration::from_secs(10)).await;
            for (i, pool) in pools.iter().enumerate() {
                if cancel_tokens[i].is_cancelled() {
                    continue;
                }
                let new_finalized = pool.read().await.finalized_slot();
                if new_finalized <= finalized[i] {
                    panic!("no progress on node {} after {} s", i, 10 * t);
                }
                finalized[i] = new_finalized;
            }
        }
    });

    // let `num_crashes` nodes crash after random delays
    let mut rng = rand::rng();
    let to_kill = (0..num_nodes).choose_multiple(&mut rng, num_crashes);
    for id in to_kill {
        let millis = rng.random_range(0..10_000);
        let delay = tokio::time::Duration::from_millis(millis);
        tokio::time::sleep(delay).await;
        debug!("crashing node {}", id);
        node_cancel_tokens[id].cancel();
    }

    // let it run for a while
    let res = tokio::select! {
        () = tokio::time::sleep(Duration::from_secs(60)) => {
            liveness_tester.abort();
            liveness_tester.await
        }
        res = &mut liveness_tester => res,
    };

    // check result of liveness test
    assert_eq!(res.unwrap_err().is_cancelled(), should_succeed);

    // kill other nodes
    for token in node_cancel_tokens {
        token.cancel();
    }
}
