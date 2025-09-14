// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};

use alpenglow::all2all::TrivialAll2All;
use alpenglow::consensus::{ConsensusMessage, EpochInfo};
use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Rotor;
use alpenglow::disseminator::rotor::StakeWeightedSampler;
use alpenglow::network::simulated::SimulatedNetworkCore;
use alpenglow::network::{SimulatedNetwork, UdpNetwork, localhost_ip_sockaddr};
use alpenglow::shredder::Shred;
use alpenglow::types::Slot;
use alpenglow::{Alpenglow, Transaction, ValidatorInfo, logging};
use color_eyre::Result;
use log::info;

#[tokio::main]
async fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    logging::enable_logforth_stderr();

    latency_test(11).await;

    Ok(())
}

type TestNode = Alpenglow<
    TrivialAll2All<SimulatedNetwork<ConsensusMessage, ConsensusMessage>>,
    Rotor<SimulatedNetwork<Shred, Shred>, StakeWeightedSampler>,
    UdpNetwork<Transaction, Transaction>,
>;

async fn create_test_nodes(count: u64) -> Vec<TestNode> {
    // open sockets with arbitrary ports
    let mut tx_receivers = (0..count)
        .map(|_| UdpNetwork::new_with_any_port())
        .collect::<VecDeque<_>>();
    let mut repair_networks = (0..count)
        .map(|_| UdpNetwork::new_with_any_port())
        .collect::<VecDeque<_>>();
    let mut repair_request_networks = (0..count)
        .map(|_| UdpNetwork::new_with_any_port())
        .collect::<VecDeque<_>>();

    // first `count` networks are for all2all and the next `count` networks are for disseminator
    let core = Arc::new(SimulatedNetworkCore::default().with_packet_loss(0.0));
    let mut all2all_networks = VecDeque::new();
    let mut disseminator_networks = VecDeque::new();
    for i in 0..count {
        all2all_networks.push_back(core.join_unlimited(i).await);
        disseminator_networks.push_back(core.join_unlimited(i + count).await);
    }

    for a in 0..count {
        for b in 0..count {
            if a < 6 && b < 6 {
                core.set_latency(a, b, Duration::from_millis(20)).await;
                core.set_latency(a + count, b + count, Duration::from_millis(20))
                    .await;
            } else if (6..10).contains(&a) && (6..10).contains(&b) {
                core.set_latency(a, b, Duration::from_millis(60)).await;
                core.set_latency(a + count, b + count, Duration::from_millis(60))
                    .await;
            } else {
                core.set_latency(a, b, Duration::from_millis(100)).await;
                core.set_latency(a + count, b + count, Duration::from_millis(100))
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
        let all2all_address = localhost_ip_sockaddr((id).try_into().unwrap());
        let disseminator_address = localhost_ip_sockaddr((id + count).try_into().unwrap());
        let repair_request_address = localhost_ip_sockaddr(repair_networks[id as usize].port());
        let repair_response_address = localhost_ip_sockaddr(repair_networks[id as usize].port());
        validators.push(ValidatorInfo {
            id,
            stake: 1,
            pubkey: sks[id as usize].to_pk(),
            voting_pubkey: voting_sks[id as usize].to_pk(),
            all2all_address,
            disseminator_address,
            repair_request_address,
            repair_response_address,
        });
    }

    // turn validator info into actual nodes
    validators
        .iter()
        .map(|v| {
            let epoch_info = Arc::new(EpochInfo::new(v.id, validators.clone()));
            let all2all =
                TrivialAll2All::new(validators.clone(), all2all_networks.pop_front().unwrap());
            let disseminator = Rotor::new(
                disseminator_networks.pop_front().unwrap(),
                epoch_info.clone(),
            );
            let repair_network = repair_networks.pop_front().unwrap();
            let repair_request_network = repair_request_networks.pop_front().unwrap();
            let txs_receiver = tx_receivers.pop_front().unwrap();
            Alpenglow::new(
                sks[v.id as usize].clone(),
                voting_sks[v.id as usize].clone(),
                all2all,
                disseminator,
                repair_network,
                repair_request_network,
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
        let mut finalized = vec![Slot::new(0); pools.len()];
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
