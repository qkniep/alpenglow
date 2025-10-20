// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::net::{SocketAddr, UdpSocket};
use std::thread::sleep;
use std::time::{Duration, Instant};

use alpenglow::{Transaction, logging};
use clap::Parser;
use color_eyre::Result;
use log::info;
use rand::RngCore;

/// Worklaod generator for benchmarks.
#[derive(Debug, Clone, Parser)]
#[command(version, about, long_about = None)]
struct Args {
    /// Validator address or receiving transactions.
    #[arg(long)]
    validator: SocketAddr,
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

fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    logging::enable_logforth();

    // parse args
    let args = Args::parse();
    let validator_addr = args.validator;
    let target_tps = args.transactions_per_second.unwrap_or(100);
    let bytes_per_tx = args.transaction_size.unwrap_or(512);

    // create socket on arbitrary port
    let socket = UdpSocket::bind("0.0.0.0:0")?;
    // prevent blocking forever
    socket.set_write_timeout(Some(Duration::from_secs(1)))?;

    // initial delay
    sleep(Duration::from_secs(args.initial_delay_secs.unwrap_or(0)));

    let start_time = Instant::now();
    let mut last_report = Instant::now();
    let mut txs_sent = 0;

    let mut rng = rand::rng();
    let mut buf = vec![0; bytes_per_tx as usize];

    loop {
        rng.fill_bytes(&mut buf);
        let tx = Transaction(buf.clone());
        let msg_bytes = wincode::serialize(&tx)?;
        socket.send_to(&msg_bytes, validator_addr).unwrap();
        txs_sent += 1;

        let elapsed = start_time.elapsed().as_secs_f64();
        let expected_elapsed = txs_sent as f64 / target_tps as f64;
        if elapsed < expected_elapsed {
            let delta = expected_elapsed - elapsed;
            sleep(Duration::from_secs_f64(delta));
        }

        if last_report.elapsed().as_secs() > 1 {
            last_report = Instant::now();
            let tps = txs_sent as f64 / elapsed;
            let total_data = bytes_per_tx as f64 * txs_sent as f64 / 1e6;
            let data_rate = total_data / elapsed * 8.0;
            info!(
                "sent {txs_sent} txs (TPS: {tps:.1}) | data: {total_data:.1} MB ({data_rate:.1} Mb/s)",
            );
        }
    }
}
