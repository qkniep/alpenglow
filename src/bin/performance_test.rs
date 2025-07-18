// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};

use alpenglow::all2all::TrivialAll2All;
use alpenglow::consensus::EpochInfo;
use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Rotor;
use alpenglow::disseminator::rotor::StakeWeightedSampler;
use alpenglow::network::simulated::SimulatedNetworkCore;
use alpenglow::network::{SimulatedNetwork, UdpNetwork};
use alpenglow::{Alpenglow, ValidatorInfo};
use color_eyre::Result;
use log::info;
use logforth::append;
use logforth::filter::EnvFilter;

#[tokio::main]
async fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    // enable `logforth` logging
    logforth::builder()
        .dispatch(|d| {
            d.filter(EnvFilter::from_default_env())
                .append(append::Stderr::default())
        })
        .apply();

    latency_test(11).await;

    Ok(())
}

type TestNode = Alpenglow<
    TrivialAll2All<SimulatedNetwork>,
    Rotor<SimulatedNetwork, StakeWeightedSampler>,
    UdpNetwork,
    UdpNetwork,
>;

async fn create_test_nodes(count: u64) -> Vec<TestNode> {
    // open sockets with arbitrary ports
    let core = Arc::new(SimulatedNetworkCore::default().with_packet_loss(0.0));
    let mut networks = VecDeque::new();
    let mut udp_networks = VecDeque::new();
    for i in 0..3 * count {
        if i % 3 == 2 {
            udp_networks.push_back(UdpNetwork::new_with_any_port());
        } else {
            networks.push_back(core.join_unlimited(i).await);
        }
    }
    for a in 0..count {
        for b in 0..count {
            if a < 6 && b < 6 {
                core.set_latency(3 * a, 3 * b, Duration::from_millis(20))
                    .await;
                core.set_latency(3 * a + 1, 3 * b + 1, Duration::from_millis(20))
                    .await;
            } else if (6..10).contains(&a) && (6..10).contains(&b) {
                core.set_latency(3 * a, 3 * b, Duration::from_millis(60))
                    .await;
                core.set_latency(3 * a + 1, 3 * b + 1, Duration::from_millis(60))
                    .await;
            } else {
                core.set_latency(3 * a, 3 * b, Duration::from_millis(100))
                    .await;
                core.set_latency(3 * a + 1, 3 * b + 1, Duration::from_millis(100))
                    .await;
            }
        }
    }

    // prepare validator info for all nodes
    let mut rng = rand::rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut validators = Vec::new();
    for id in 0..count {
        sks.push(SecretKey::new(&mut rng));
        voting_sks.push(aggsig::SecretKey::new(&mut rng));
        let a2a_port = 3 * id;
        let dis_port = 3 * id + 1;
        let rep_port = udp_networks[id as usize].port();
        validators.push(ValidatorInfo {
            id,
            stake: 1,
            pubkey: sks[id as usize].to_pk(),
            voting_pubkey: voting_sks[id as usize].to_pk(),
            all2all_address: format!("{a2a_port}"),
            disseminator_address: format!("{dis_port}"),
            repair_address: format!("127.0.0.1:{rep_port}"),
        });
    }

    // turn validator info into actual nodes
    validators
        .iter()
        .map(|v| {
            let epoch_info = Arc::new(EpochInfo::new(v.id, validators.clone()));
            let all2all = TrivialAll2All::new(validators.clone(), networks.pop_front().unwrap());
            let disseminator = Rotor::new(networks.pop_front().unwrap(), epoch_info.clone());
            let repair_network = udp_networks.pop_front().unwrap();
            let txs_receiver = udp_networks.pop_front().unwrap();
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

async fn latency_test(num_nodes: usize) {
    // start `num_nodes` nodes
    let nodes = create_test_nodes(num_nodes as u64).await;
    let mut node_cancel_tokens = Vec::new();
    let mut pools = Vec::new();
    for node in nodes {
        pools.push(node.get_pool());
        node_cancel_tokens.push(node.get_cancel_token());
        tokio::spawn(node.run());
    }

    // spawn a thread checking pool for progress
    let cancel_tokens = node_cancel_tokens.clone();
    let liveness_tester = tokio::spawn(async move {
        let mut finalized = vec![0; pools.len()];
        let mut times = vec![Instant::now(); pools.len()];
        loop {
            tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
            for (i, pool) in pools.iter().enumerate() {
                if cancel_tokens[i].is_cancelled() {
                    continue;
                }
                let new_finalized = pool.read().await.finalized_slot();
                if new_finalized > finalized[i] {
                    info!(
                        "node {} finalized new block {} after {:.2} ms",
                        i,
                        new_finalized,
                        times[i].elapsed().as_secs_f64() * 1000.0
                    );
                    finalized[i] = new_finalized;
                    times[i] = Instant::now();
                }
            }
        }
    });

    // let it run for a while
    let delay = tokio::time::Duration::from_secs(60);
    tokio::time::sleep(delay).await;

    liveness_tester.abort();
    assert!(liveness_tester.await.unwrap_err().is_cancelled());

    // kill other nodes
    for token in node_cancel_tokens {
        token.cancel();
    }
}
