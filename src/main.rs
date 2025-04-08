// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::disseminator::rotor::StakeWeightedSampler;
use color_eyre::Result;
use rand::rng;
use tracing::level_filters::LevelFilter;
use tracing_subscriber::{EnvFilter, prelude::*};

use alpenglow::ValidatorInfo;
use alpenglow::all2all::TrivialAll2All;
use alpenglow::consensus::Alpenglow;
use alpenglow::crypto::aggsig;
use alpenglow::disseminator::Rotor;
use alpenglow::network::UdpNetwork;
use alpenglow::repair::Repair;

#[tokio::main]
async fn main() -> Result<()> {
    color_eyre::install()?;

    // enable `tracing` and `tokio-console`
    // let console_layer = console_subscriber::spawn();
    let filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::DEBUG.into())
        .from_env_lossy();
    tracing_subscriber::registry()
        // .with(console_layer)
        .with(filter)
        .with(
            tracing_subscriber::fmt::layer()
                .compact()
                .without_time()
                .with_target(false),
        )
        .init();

    // spawn local cluster
    let nodes = create_test_nodes(11);
    let mut node_tasks = Vec::new();
    for node in nodes {
        node_tasks.push(tokio::spawn(node.run()));
    }
    futures::future::join_all(node_tasks).await;

    Ok(())
}

type TestNode = Alpenglow<TrivialAll2All<UdpNetwork>, Rotor<UdpNetwork, StakeWeightedSampler>>;

fn create_test_nodes(count: u64) -> Vec<TestNode> {
    // prepare validator info for all nodes
    let mut port = 3000;
    let mut rng = rng();
    let mut sks = Vec::new();
    let mut validators = Vec::new();
    for id in 0..count {
        sks.push(aggsig::SecretKey::new(&mut rng));
        validators.push(ValidatorInfo {
            id,
            stake: 1,
            pubkey: sks[id as usize].to_pk(),
            all2all_address: format!("127.0.0.1:{}", port),
            disseminator_address: format!("127.0.0.1:{}", port + 1),
            repair_address: format!("127.0.0.1:{}", port + 2),
        });
        port += 3;
    }

    // turn validator info into actual nodes
    validators
        .iter()
        .map(|v| {
            let start_port = 3000 + v.id * 3;
            let network = UdpNetwork::new(start_port as u16);
            let all2all = TrivialAll2All::new(validators.clone(), network);
            let network = UdpNetwork::new(start_port as u16 + 1);
            let disseminator = Rotor::new(v.id, validators.clone(), network);
            let network = UdpNetwork::new(start_port as u16 + 2);
            let repair = Repair::new(v.id, validators.clone(), network);
            Alpenglow::new(
                v.id,
                sks[v.id as usize].clone(),
                validators.clone(),
                all2all,
                disseminator,
                repair,
            )
        })
        .collect()
}
