// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;
use std::time::{Duration, Instant};

use alpenglow::all2all::TrivialAll2All;
use alpenglow::consensus::{ConsensusMessage, EpochInfo, ValidatorEpochInfo};
use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Rotor;
use alpenglow::disseminator::rotor::{IidQuorumSampler, StakeWeightedSampler};
use alpenglow::network::simulated::SimulatedNetworkCore;
use alpenglow::network::{SimulatedNetwork, UdpNetwork, localhost_ip_sockaddr};
use alpenglow::shredder::Shred;
use alpenglow::types::Slot;
use alpenglow::{Alpenglow, Stake, Transaction, ValidatorIndex, ValidatorInfo, logging};
use anyhow::Result;
use clap::Parser;
use log::info;

/// Alpenglow performance test with simulated network.
#[derive(Debug, Parser)]
#[command(version, about)]
struct Args {
    /// Duration of the performance test in seconds.
    #[arg(long, default_value_t = 60)]
    duration_secs: u64,
}

#[tokio::main]
#[hotpath::main]
async fn main() -> Result<()> {
    let args = Args::parse();
    logging::enable_logforth();

    latency_test(11, args.duration_secs).await;

    Ok(())
}

type TestNode = Alpenglow<
    TrivialAll2All<SimulatedNetwork<ConsensusMessage, ConsensusMessage>>,
    Rotor<SimulatedNetwork<Shred, Shred>, IidQuorumSampler<StakeWeightedSampler>>,
    UdpNetwork<Transaction, Transaction>,
>;

async fn create_test_nodes(count: u64) -> Vec<TestNode> {
    // open one set of networks per validator:
    // (all2all, disseminator, repair_requester, repair_responder, txs_receiver)
    let core = Arc::new(SimulatedNetworkCore::default().with_packet_loss(0.0));
    let mut networks = Vec::with_capacity(count as usize);
    for i in 0..count {
        let all2all = core.join_unlimited(ValidatorIndex::new(i)).await;
        let disseminator = core.join_unlimited(ValidatorIndex::new(i + count)).await;
        networks.push((
            all2all,
            disseminator,
            UdpNetwork::new_with_any_port(),
            UdpNetwork::new_with_any_port(),
            UdpNetwork::new_with_any_port(),
        ));
    }

    for a in 0..count {
        for b in 0..count {
            if a < 6 && b < 6 {
                core.set_latency(
                    ValidatorIndex::new(a),
                    ValidatorIndex::new(b),
                    Duration::from_millis(20),
                )
                .await;
                core.set_latency(
                    ValidatorIndex::new(a + count),
                    ValidatorIndex::new(b + count),
                    Duration::from_millis(20),
                )
                .await;
            } else if (6..10).contains(&a) && (6..10).contains(&b) {
                core.set_latency(
                    ValidatorIndex::new(a),
                    ValidatorIndex::new(b),
                    Duration::from_millis(60),
                )
                .await;
                core.set_latency(
                    ValidatorIndex::new(a + count),
                    ValidatorIndex::new(b + count),
                    Duration::from_millis(60),
                )
                .await;
            } else {
                core.set_latency(
                    ValidatorIndex::new(a),
                    ValidatorIndex::new(b),
                    Duration::from_millis(100),
                )
                .await;
                core.set_latency(
                    ValidatorIndex::new(a + count),
                    ValidatorIndex::new(b + count),
                    Duration::from_millis(100),
                )
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
        let all2all_address =
            localhost_ip_sockaddr((id).try_into().expect("node count fits in u16 port range"));
        let disseminator_address = localhost_ip_sockaddr(
            (id + count)
                .try_into()
                .expect("node count fits in u16 port range"),
        );
        let (_, _, repair_req, repair_res, _) = &networks[id as usize];
        let repair_requester_address = localhost_ip_sockaddr(repair_req.port());
        let repair_responder_address = localhost_ip_sockaddr(repair_res.port());
        validators.push(ValidatorInfo {
            id: ValidatorIndex::new(id),
            stake: Stake::new(1),
            pubkey: sks[id as usize].to_pk(),
            voting_pubkey: voting_sks[id as usize].to_pk(),
            all2all_address,
            disseminator_address,
            repair_requester_address,
            repair_responder_address,
        });
    }

    // turn validator info into actual nodes
    let shared_epoch = EpochInfo::new(validators.clone());
    validators
        .iter()
        .zip(networks)
        .map(|(v, networks)| {
            let (all2all, disseminator, repair_requester, repair_responder, txs_receiver) =
                networks;
            let epoch_info = Arc::new(ValidatorEpochInfo::new(v.id, shared_epoch.clone()));
            let all2all = TrivialAll2All::new(validators.clone(), all2all);
            let disseminator = Rotor::new(disseminator, epoch_info.clone());
            Alpenglow::new(
                sks[v.id.as_usize()].clone(),
                voting_sks[v.id.as_usize()].clone(),
                all2all,
                disseminator,
                repair_requester,
                repair_responder,
                epoch_info,
                txs_receiver,
            )
        })
        .collect()
}

async fn latency_test(num_nodes: usize, duration_secs: u64) {
    // start `num_nodes` nodes
    let nodes = create_test_nodes(num_nodes as u64).await;
    let mut node_cancel_tokens = Vec::new();
    let mut finalized_watches = Vec::new();
    for node in nodes {
        finalized_watches.push(node.finalized_slot());
        node_cancel_tokens.push(node.get_cancel_token());
        tokio::spawn(node.run());
    }

    // spawn a thread checking finalization progress
    let cancel_tokens = node_cancel_tokens.clone();
    let liveness_tester = tokio::spawn(async move {
        let mut finalized = vec![Slot::new(0); finalized_watches.len()];
        let mut times = vec![Instant::now(); finalized_watches.len()];
        loop {
            tokio::time::sleep(Duration::from_millis(1)).await;
            for (i, watch) in finalized_watches.iter().enumerate() {
                if cancel_tokens[i].is_cancelled() {
                    continue;
                }
                let new_finalized = *watch.borrow();
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
    tokio::time::sleep(Duration::from_secs(duration_secs)).await;

    liveness_tester.abort();
    assert!(liveness_tester.await.unwrap_err().is_cancelled());

    // kill other nodes
    for token in node_cancel_tokens {
        token.cancel();
    }
}
