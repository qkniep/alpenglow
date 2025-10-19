// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::borrow::Cow;
use std::fs::File;
use std::io::Read;
use std::net::SocketAddr;
use std::sync::Arc;

use alpenglow::all2all::TrivialAll2All;
use alpenglow::consensus::{Alpenglow, ConsensusMessage, EpochInfo};
use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Rotor;
use alpenglow::disseminator::rotor::StakeWeightedSampler;
use alpenglow::network::UdpNetwork;
use alpenglow::shredder::Shred;
use alpenglow::{Transaction, ValidatorInfo, logging};
use clap::Parser;
use color_eyre::Result;
use color_eyre::eyre::Context;
use fastrace::collector::Config;
use fastrace::prelude::*;
use fastrace_opentelemetry::OpenTelemetryReporter;
use log::warn;
use opentelemetry::{InstrumentationScope, KeyValue};
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use opentelemetry_sdk::Resource;
use rand::rng;
use serde::{Deserialize, Serialize};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ConfigFile {
    id: u64,
    identity_key: SecretKey,
    #[serde(deserialize_with = "aggsig::SecretKey::from_array_of_bytes")]
    voting_key: aggsig::SecretKey,
    port: u16,
    gossip: Vec<ValidatorInfo>,
}

/// Standalone Alpenglow node.
#[derive(Clone, Debug, Parser)]
#[command(version, about, long_about = None)]
struct Args {
    /// Generates configs for a cluster from a file with IPs (one per line).
    #[arg(long)]
    generate_config_files: Option<String>,
    /// Config file name to use.
    #[arg(long)]
    config_name: String,
}

#[tokio::main]
async fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    // parse args & load config from file
    let args = Args::parse();
    if let Some(ip_list) = args.generate_config_files {
        create_node_configs(ip_list, args.config_name).await?;
        return Ok(());
    }
    let mut config = File::open(&args.config_name).context("Config file is required")?;
    let mut config_string = String::new();
    config.read_to_string(&mut config_string)?;
    let config: ConfigFile = toml::from_str(&config_string).context("Can not parse config")?;

    // enable `fastrace` tracing
    let reporter = OpenTelemetryReporter::new(
        SpanExporter::builder()
            .with_tonic()
            .with_endpoint("http://127.0.0.1:4317".to_string())
            .with_protocol(opentelemetry_otlp::Protocol::Grpc)
            .with_timeout(opentelemetry_otlp::OTEL_EXPORTER_OTLP_TIMEOUT_DEFAULT)
            .build()
            .expect("initialize oltp exporter"),
        Cow::Owned(
            Resource::builder()
                .with_attributes([KeyValue::new("service.name", "alpenglow-main")])
                .build(),
        ),
        InstrumentationScope::builder("alpenglow")
            .with_version(env!("CARGO_PKG_VERSION"))
            .build(),
    );
    fastrace::set_reporter(reporter, Config::default());

    logging::enable_logforth();

    let span_context = SpanContext::random();
    let root_span = Span::root(format!("Alpenglow node {}", config.id), span_context);

    // start the node with the provided config
    let node = create_node(config);
    let cancel_token = node.get_cancel_token();
    let node_task = tokio::spawn(node.run().in_span(root_span));

    // wait for shutdown signal (Ctrl + C)
    tokio::signal::ctrl_c().await?;
    warn!("shutting down node");
    cancel_token.cancel();
    node_task.await??;

    fastrace::flush();

    Ok(())
}

type Node = Alpenglow<
    TrivialAll2All<UdpNetwork<ConsensusMessage, ConsensusMessage>>,
    Rotor<UdpNetwork<Shred, Shred>, StakeWeightedSampler>,
    UdpNetwork<Transaction, Transaction>,
>;

fn create_node(config: ConfigFile) -> Node {
    // turn ConfigFile into an actual node
    let epoch_info = Arc::new(EpochInfo::new(config.id, config.gossip.clone()));
    let start_port = config.port;
    let network = UdpNetwork::new(start_port);
    let all2all = TrivialAll2All::new(config.gossip, network);
    let network = UdpNetwork::new(start_port + 1);
    let disseminator = Rotor::new(network, epoch_info.clone());
    let repair_network = UdpNetwork::new(start_port + 2);
    let repair_request_network = UdpNetwork::new(start_port + 3);
    let txs_receiver = UdpNetwork::new(start_port + 4);
    Alpenglow::new(
        config.identity_key,
        config.voting_key,
        all2all,
        disseminator,
        repair_network,
        repair_request_network,
        epoch_info,
        txs_receiver,
    )
}

async fn create_node_configs(
    socket_list_filename: String,
    config_base_filename: String,
) -> color_eyre::Result<()> {
    // prepare ValidatorInfo for all nodes
    let mut rng = rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut ports = Vec::new();
    let mut validators = Vec::new();
    let mut socket_list =
        tokio::io::BufReader::new(tokio::fs::File::open(socket_list_filename).await?).lines();
    for id in 0.. {
        let Some(line) = socket_list.next_line().await? else {
            break;
        };
        let sockaddr = line
            .parse::<SocketAddr>()
            .context("Can not parse socket list")?;
        sks.push(SecretKey::new(&mut rng));
        ports.push(sockaddr.port());
        voting_sks.push(aggsig::SecretKey::new(&mut rng));
        validators.push(ValidatorInfo {
            id,
            stake: 1,
            pubkey: sks[id as usize].to_pk(),
            voting_pubkey: voting_sks[id as usize].to_pk(),
            all2all_address: sockaddr,
            disseminator_address: SocketAddr::new(sockaddr.ip(), sockaddr.port() + 1),
            repair_request_address: SocketAddr::new(sockaddr.ip(), sockaddr.port() + 2),
            repair_response_address: SocketAddr::new(sockaddr.ip(), sockaddr.port() + 3),
        });
    }

    // write config files
    for id in 0..sks.len() as u64 {
        let mut file = tokio::fs::File::create(format!("{config_base_filename}_{id}.toml")).await?;
        let conf = ConfigFile {
            id,
            port: ports[id as usize],
            identity_key: sks[id as usize].clone(),
            voting_key: voting_sks[id as usize].clone(),
            gossip: validators.clone(),
        };

        let serialized = toml::to_string(&conf)?;

        file.write_all(serialized.as_bytes()).await?;
        file.sync_data().await?;
    }
    Ok(())
}
