// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant};

use alpenglow::all2all::TrivialAll2All;
use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Rotor;
use alpenglow::disseminator::rotor::StakeWeightedSampler;
use alpenglow::network::simulated::SimulatedNetworkCore;
use alpenglow::network::simulated::ping_data::{find_closest_ping_server, get_ping};
use alpenglow::network::simulated::stake_distribution::VALIDATOR_DATA;
use alpenglow::network::{SimulatedNetwork, UdpNetwork};
use alpenglow::repair::Repair;
use alpenglow::{Alpenglow, Stake, ValidatorId, ValidatorInfo};
use color_eyre::Result;
use log::{info, warn};
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

    // turn ValidatorData into ValidatorInfo
    let mut validators = Vec::new();
    for v in VALIDATOR_DATA.iter() {
        if !(v.is_active && v.delinquent == Some(false)) {
            continue;
        }
        let stake = v.active_stake.unwrap_or(0);
        if stake > 0 {
            let sk = SecretKey::new(&mut rand::rng());
            let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
            validators.push(ValidatorInfo {
                id: validators.len() as ValidatorId,
                stake,
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: String::new(),
                disseminator_address: String::new(),
                repair_address: String::new(),
            });
        }
    }

    // assign closest ping servers to validators
    let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
    let mut validators_with_ping_data = Vec::new();
    let mut stake_with_ping_server = 0;
    for v in VALIDATOR_DATA.iter() {
        let stake = v.active_stake.unwrap_or(0);
        if !(v.is_active && v.delinquent == Some(false)) || stake == 0 {
            continue;
        }
        let (Some(lat), Some(lon)) = (&v.latitude, &v.longitude) else {
            continue;
        };
        let ping_server = find_closest_ping_server(lat.parse().unwrap(), lon.parse().unwrap());
        stake_with_ping_server += stake;
        let sk = SecretKey::new(&mut rand::rng());
        let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
        validators_with_ping_data.push((
            ValidatorInfo {
                id: validators_with_ping_data.len() as ValidatorId,
                stake,
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: String::new(),
                disseminator_address: String::new(),
                repair_address: String::new(),
            },
            ping_server,
        ));
    }
    warn!(
        "discarding {:.2}% of validators w/o ping server",
        100.0 - stake_with_ping_server as f64 * 100.0 / total_stake as f64
    );

    // determine pings of validator pairs
    let mut nodes_without_ping = HashSet::new();
    for (v1, p1) in &validators_with_ping_data {
        for (v2, p2) in &validators_with_ping_data {
            if get_ping(p1.id, p2.id).is_none() {
                nodes_without_ping.insert(v1.id);
                nodes_without_ping.insert(v2.id);
            }
        }
    }
    warn!(
        "discarding {:.2}% of nodes w/o ping",
        nodes_without_ping.len() as f64 * 100.0 / validators_with_ping_data.len() as f64
    );
    warn!("{} validators without ping data", nodes_without_ping.len());
    validators_with_ping_data.retain(|(v, _)| !nodes_without_ping.contains(&v.id));
    info!(
        "{} validators with ping data",
        validators_with_ping_data.len()
    );

    validators_with_ping_data
        .iter_mut()
        .enumerate()
        .for_each(|(i, v)| {
            v.0.id = i as ValidatorId;
        });
    let mut validator_to_ping_server = HashMap::new();
    for (v, p) in &validators_with_ping_data {
        validator_to_ping_server.insert(v.id, *p);
    }

    let validators_with_ping_data: Vec<_> =
        validators_with_ping_data.into_iter().map(|v| v.0).collect();
    latency_test(11).await;
    // latency_test(validators_with_ping_data, validator_to_ping_server);

    Ok(())
}

type TestNode =
    Alpenglow<TrivialAll2All<SimulatedNetwork>, Rotor<SimulatedNetwork, StakeWeightedSampler>>;

async fn create_test_nodes(count: u64) -> Vec<TestNode> {
    // open sockets with arbitrary ports
    let core = Arc::new(SimulatedNetworkCore::new().with_packet_loss(0.0));
    let mut networks = VecDeque::new();
    let mut udp_networks = VecDeque::new();
    for i in 0..3 * count {
        if i % 3 == 2 {
            udp_networks.push_back(UdpNetwork::new_with_any_port());
        } else {
            // networks.push_back(core.join(i, 1_000_000, 1_000_000).await);
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
        // let rep_port = 3 * id + 2;
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
            let all2all = TrivialAll2All::new(validators.clone(), networks.pop_front().unwrap());
            let disseminator = Rotor::new(v.id, validators.clone(), networks.pop_front().unwrap());
            let repair = Repair::new(v.id, validators.clone(), udp_networks.pop_front().unwrap());
            Alpenglow::new(
                v.id,
                sks[v.id as usize].clone(),
                voting_sks[v.id as usize].clone(),
                validators.clone(),
                all2all,
                disseminator,
                repair,
            )
        })
        .collect()
}

async fn latency_test(num_nodes: usize) {
    // start `num_nodes` nodes
    let nodes = create_test_nodes(num_nodes as u64).await;
    // let mut node_tasks = Vec::new();
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
