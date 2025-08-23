// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::net::{SocketAddr, UdpSocket};
use std::time::{Duration, Instant};

use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::network::NetworkMessage;
use alpenglow::{Transaction, ValidatorInfo, logging};
use clap::Parser;
use color_eyre::Result;
use log::info;
use rand::RngCore;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ConfigFile {
    id: u64,
    identity_key: SecretKey,
    #[serde(deserialize_with = "aggsig::SecretKey::from_array_of_bytes")]
    voting_key: aggsig::SecretKey,
    port: u16,
    gossip: Vec<ValidatorInfo>,
}

/// Worklaod generator for benchmarks.
#[derive(Debug, Clone, Parser)]
#[command(version, about, long_about = None)]
struct Args {
    /// Validator addres or receiving transactions.
    #[arg(long)]
    validator: String,
    /// Initial wait time, before sending any transactions.
    #[arg(long)]
    initial_delay_secs: Option<u64>,
    /// Target throughput in transactions per second.
    #[arg(long)]
    transactions_per_second: Option<u64>,
    /// Bytes per transaction.
    #[arg(long)]
    transaction_size: Option<u64>,
}

#[tokio::main]
async fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    logging::enable_logforth();

    // parse args & load config from file
    let args = Args::parse();

    let validator_addr = args.validator;
    let addr: SocketAddr = validator_addr.parse().unwrap();
    let target_tps = args.transactions_per_second.unwrap_or(100);
    let bytes_per_tx = args.transaction_size.unwrap_or(512);

    // let network = UdpNetwork::new_with_any_port();
    let socket = UdpSocket::bind("0.0.0.0:0")?;

    tokio::time::sleep(Duration::from_secs(args.initial_delay_secs.unwrap_or(0))).await;

    let start_time = Instant::now();
    let mut last_report = Instant::now();
    let mut txs_sent = 0;

    let mut rng = rand::rng();
    let mut buf = vec![0; bytes_per_tx as usize];
    socket.set_nonblocking(true).unwrap();

    loop {
        rng.fill_bytes(&mut buf);
        let tx = Transaction(buf.clone());
        let msg = NetworkMessage::Transaction(tx);
        socket.send_to(&msg.to_bytes(), addr)?;
        // network.send(&msg, &validator_addr).await?;
        txs_sent += 1;

        let elapsed = start_time.elapsed().as_secs_f64();
        let expected_elapsed = txs_sent as f64 / target_tps as f64;
        if elapsed < expected_elapsed {
            let delta = expected_elapsed - elapsed;
            tokio::time::sleep(Duration::from_secs_f64(delta)).await;
        }

        if last_report.elapsed().as_secs() > 1 {
            last_report = Instant::now();
            let tps = txs_sent as f64 / elapsed;
            let total_data = bytes_per_tx as f64 * txs_sent as f64 / 1e6;
            let data_rate = total_data / elapsed * 8.0;
            info!(
                "sent {} txs (TPS: {:.1}) | data: {:.1} MB ({:.1} Mb/s)",
                txs_sent, tps, total_data, data_rate
            );
        }
    }
}
