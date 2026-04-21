// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, VecDeque};
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use alpenglow::all2all::TrivialAll2All;
use alpenglow::consensus::{ConsensusMessage, EpochInfo, ValidatorEpochInfo};
use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Rotor;
use alpenglow::disseminator::rotor::{IidQuorumSampler, StakeWeightedSampler};
use alpenglow::network::{UdpNetwork, localhost_ip_sockaddr};
use alpenglow::shredder::Shred;
use alpenglow::types::Slot;
use alpenglow::{Alpenglow, Stake, Transaction, ValidatorId, ValidatorInfo, logging};
use clap::Parser;
use color_eyre::Result;
use csv::Writer;
use log::info;
use rand::prelude::*;
use tokio::sync::mpsc;

/// Alpenglow throughput/latency benchmark: sweeps load levels and outputs a CSV.
#[derive(Debug, Parser)]
#[command(version, about)]
struct Args {
    /// Number of simulated validator nodes.
    #[arg(long, default_value_t = 2)]
    num_nodes: usize,

    /// Duration of the measurement window per load level, in seconds.
    #[arg(long, default_value_t = 30)]
    duration_secs: u64,

    /// Warmup duration per load level, in seconds (events discarded).
    #[arg(long, default_value_t = 5)]
    warmup_secs: u64,

    /// Comma-separated target TPS levels for the sweep.
    #[arg(long, default_value = "100,500,1000,2500,5000,10000,25000,50000")]
    tps_levels: String,

    /// Transaction size in bytes (max 512).
    #[arg(long, default_value_t = 512)]
    tx_size: usize,

    /// Number of distinct nodes to distribute injected load across.
    #[arg(long, default_value_t = 1)]
    load_nodes: usize,

    /// Output CSV file. Defaults to stdout.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Debug)]
struct BenchResult {
    target_tps: u64,
    slot_rate_hz: f64,
    mean_ms: f64,
    p50_ms: f64,
    p95_ms: f64,
    p99_ms: f64,
    samples: usize,
}

#[tokio::main]
#[hotpath::main]
async fn main() -> Result<()> {
    color_eyre::install()?;
    let args = Args::parse();
    logging::enable_logforth();

    let tps_levels: Vec<u64> = args
        .tps_levels
        .split(',')
        .map(|s| s.trim().parse::<u64>().expect("invalid TPS value"))
        .collect();

    let mut results = Vec::new();
    for &tps in &tps_levels {
        info!("=== load level: {tps} TPS ===");
        let result = run_benchmark_level(
            tps,
            args.tx_size,
            args.num_nodes,
            args.load_nodes,
            args.warmup_secs,
            args.duration_secs,
        )
        .await;
        info!(
            "p50={:.1}ms p95={:.1}ms p99={:.1}ms slot_rate={:.2}Hz samples={}",
            result.p50_ms, result.p95_ms, result.p99_ms, result.slot_rate_hz, result.samples
        );
        results.push(result);
    }

    write_csv(&results, args.output.as_deref())?;
    Ok(())
}

async fn run_benchmark_level(
    target_tps: u64,
    tx_size: usize,
    num_nodes: usize,
    load_nodes: usize,
    warmup_secs: u64,
    duration_secs: u64,
) -> BenchResult {
    let (nodes, tx_addrs) = create_test_nodes(num_nodes as u64);

    let baseline = Instant::now();
    let warmup_nanos = warmup_secs * 1_000_000_000;

    // Node monitors send slot-finalization events and per-transaction latency events.
    let (slot_tx, mut slot_rx) = mpsc::unbounded_channel::<(Instant, Slot)>();
    let (lat_tx, mut lat_rx) = mpsc::unbounded_channel::<(u64, u64)>();

    let mut cancel_tokens = Vec::new();
    for node in nodes {
        let token = node.get_cancel_token();
        cancel_tokens.push(token.clone());
        let pool = node.get_pool();
        let blockstore = node.get_blockstore();
        let slot_ev_tx = slot_tx.clone();
        let lat_ev_tx = lat_tx.clone();
        tokio::spawn(node.run());
        tokio::spawn(async move {
            let mut last = Slot::new(0);
            loop {
                if token.is_cancelled() {
                    break;
                }
                tokio::time::sleep(Duration::from_millis(1)).await;
                let new = pool.read().await.finalized_slot();
                if new > last {
                    let fin_instant = Instant::now();
                    let fin_offset = (fin_instant - baseline).as_nanos() as u64;
                    let _ = slot_ev_tx.send((fin_instant, new));
                    if let Some(txs) = blockstore.read().await.transactions_for_slot(new) {
                        for tx in txs {
                            if tx.0.len() >= 8 {
                                let sub_offset = u64::from_le_bytes(tx.0[..8].try_into().unwrap());
                                let _ = lat_ev_tx.send((sub_offset, fin_offset));
                            }
                        }
                    }
                    last = new;
                }
            }
        });
    }

    // Limit load_nodes to available nodes.
    let load_addrs: Vec<SocketAddr> = tx_addrs.into_iter().take(load_nodes.max(1)).collect();
    let injector = tokio::spawn(inject_load(target_tps, tx_size, load_addrs, baseline));

    // Warmup: let the cluster stabilize, then discard all events so far.
    tokio::time::sleep(Duration::from_secs(warmup_secs)).await;
    while slot_rx.try_recv().is_ok() {}
    while lat_rx.try_recv().is_ok() {}

    // Measurement window.
    tokio::time::sleep(Duration::from_secs(duration_secs)).await;

    // Collect all events buffered during measurement window.
    let mut raw_slot_events: Vec<(Instant, Slot)> = Vec::new();
    while let Ok(ev) = slot_rx.try_recv() {
        raw_slot_events.push(ev);
    }
    let mut raw_lat_events: Vec<(u64, u64)> = Vec::new();
    while let Ok(ev) = lat_rx.try_recv() {
        raw_lat_events.push(ev);
    }

    injector.abort();
    for token in cancel_tokens {
        token.cancel();
    }

    // Deduplicate slots: multiple nodes may report same slot. Keep earliest timestamp.
    let mut by_slot: HashMap<Slot, Instant> = HashMap::new();
    for (t, s) in raw_slot_events {
        by_slot
            .entry(s)
            .and_modify(|e| {
                if t < *e {
                    *e = t;
                }
            })
            .or_insert(t);
    }
    let slot_rate = by_slot.len() as f64 / duration_secs as f64;

    // Deduplicate latency events: per unique submission offset keep earliest finalization.
    // Drop transactions whose submission offset predates the warmup window.
    let mut by_sub: HashMap<u64, u64> = HashMap::new();
    for (sub, fin) in raw_lat_events {
        if sub < warmup_nanos {
            continue;
        }
        by_sub
            .entry(sub)
            .and_modify(|e| {
                if fin < *e {
                    *e = fin;
                }
            })
            .or_insert(fin);
    }

    let latencies_ms: Vec<f64> = by_sub
        .into_iter()
        .filter_map(|(sub, fin)| fin.checked_sub(sub).map(|nanos| nanos as f64 / 1_000_000.0))
        .collect();

    compute_bench_result(target_tps, &latencies_ms, slot_rate)
}

fn compute_bench_result(target_tps: u64, latencies_ms: &[f64], slot_rate_hz: f64) -> BenchResult {
    if latencies_ms.is_empty() {
        return BenchResult {
            target_tps,
            slot_rate_hz,
            mean_ms: 0.0,
            p50_ms: 0.0,
            p95_ms: 0.0,
            p99_ms: 0.0,
            samples: 0,
        };
    }

    let mut sorted = latencies_ms.to_vec();
    sorted.sort_by(f64::total_cmp);

    let n = sorted.len();
    let p50 = sorted[(n * 50).saturating_sub(1) / 100];
    let p95 = sorted[(n * 95).saturating_sub(1) / 100];
    let p99 = sorted[(n * 99).saturating_sub(1) / 100];
    let mean = sorted.iter().sum::<f64>() / n as f64;

    BenchResult {
        target_tps,
        slot_rate_hz,
        mean_ms: mean,
        p50_ms: p50,
        p95_ms: p95,
        p99_ms: p99,
        samples: n,
    }
}

async fn inject_load(target_tps: u64, tx_size: usize, addrs: Vec<SocketAddr>, baseline: Instant) {
    if target_tps == 0 || addrs.is_empty() {
        return;
    }

    let socket = tokio::net::UdpSocket::bind("0.0.0.0:0").await.unwrap();
    let mut rng = rand::rngs::StdRng::from_rng(&mut rand::rng());
    // Clamp to [8, 512]: first 8 bytes carry the submission timestamp.
    let tx_size = tx_size.clamp(8, 512);
    let mut buf = vec![0u8; tx_size];

    // Send in bursts timed to 1ms ticks. For low TPS (<1000), burst every N ms.
    let burst_interval_ms = (1000_f64 / target_tps as f64).max(1.0) as u64;
    let txs_per_burst =
        ((target_tps as f64 * burst_interval_ms as f64 / 1000.0).ceil() as u64).max(1);

    let mut interval = tokio::time::interval(Duration::from_millis(burst_interval_ms));
    interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

    let mut addr_idx: usize = 0;
    loop {
        interval.tick().await;
        for _ in 0..txs_per_burst {
            rng.fill_bytes(&mut buf);
            let offset_nanos = (Instant::now() - baseline).as_nanos() as u64;
            buf[..8].copy_from_slice(&offset_nanos.to_le_bytes());
            let tx = Transaction(buf.clone());
            if let Ok(bytes) = wincode::serialize(&tx) {
                let _ = socket.send_to(&bytes, addrs[addr_idx % addrs.len()]).await;
                addr_idx = addr_idx.wrapping_add(1);
            }
        }
    }
}

fn write_csv(results: &[BenchResult], path: Option<&Path>) -> Result<()> {
    let writer: Box<dyn std::io::Write> = match path {
        Some(p) => Box::new(std::fs::File::create(p)?),
        None => Box::new(std::io::stdout()),
    };
    let mut wtr = Writer::from_writer(writer);

    wtr.write_record([
        "target_tps",
        "slot_rate_hz",
        "mean_ms",
        "p50_ms",
        "p95_ms",
        "p99_ms",
        "samples",
    ])?;
    for r in results {
        wtr.write_record([
            r.target_tps.to_string(),
            format!("{:.3}", r.slot_rate_hz),
            format!("{:.2}", r.mean_ms),
            format!("{:.2}", r.p50_ms),
            format!("{:.2}", r.p95_ms),
            format!("{:.2}", r.p99_ms),
            r.samples.to_string(),
        ])?;
    }
    wtr.flush()?;
    Ok(())
}

type TestNode = Alpenglow<
    TrivialAll2All<UdpNetwork<ConsensusMessage, ConsensusMessage>>,
    Rotor<UdpNetwork<Shred, Shred>, IidQuorumSampler<StakeWeightedSampler>>,
    UdpNetwork<Transaction, Transaction>,
>;

fn create_test_nodes(count: u64) -> (Vec<TestNode>, Vec<SocketAddr>) {
    let mut all2all_nets: VecDeque<_> = (0..count)
        .map(|_| UdpNetwork::<ConsensusMessage, ConsensusMessage>::new_with_any_port())
        .collect();
    let mut disseminator_nets: VecDeque<_> = (0..count)
        .map(|_| UdpNetwork::<Shred, Shred>::new_with_any_port())
        .collect();
    let mut repair_nets: VecDeque<_> = (0..count)
        .map(|_| UdpNetwork::new_with_any_port())
        .collect();
    let mut repair_req_nets: VecDeque<_> = (0..count)
        .map(|_| UdpNetwork::new_with_any_port())
        .collect();
    let mut tx_nets: VecDeque<UdpNetwork<Transaction, Transaction>> = (0..count)
        .map(|_| UdpNetwork::new_with_any_port())
        .collect();

    let tx_addrs: Vec<SocketAddr> = tx_nets
        .iter()
        .map(|n| localhost_ip_sockaddr(n.port()))
        .collect();

    let mut rng = rand::rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut validators = Vec::new();
    for id in 0..count as usize {
        sks.push(SecretKey::new(&mut rng));
        voting_sks.push(aggsig::SecretKey::new(&mut rng));
        validators.push(ValidatorInfo {
            id: ValidatorId::new(id as u64),
            stake: Stake::new(1),
            pubkey: sks[id].to_pk(),
            voting_pubkey: voting_sks[id].to_pk(),
            all2all_address: localhost_ip_sockaddr(all2all_nets[id].port()),
            disseminator_address: localhost_ip_sockaddr(disseminator_nets[id].port()),
            repair_request_address: localhost_ip_sockaddr(repair_req_nets[id].port()),
            repair_response_address: localhost_ip_sockaddr(repair_nets[id].port()),
        });
    }

    let shared_epoch = EpochInfo::new(validators.clone());
    let nodes = validators
        .iter()
        .map(|v| {
            let epoch_info = Arc::new(ValidatorEpochInfo::new(v.id, shared_epoch.clone()));
            let all2all =
                TrivialAll2All::new(validators.clone(), all2all_nets.pop_front().unwrap());
            let disseminator =
                Rotor::new(disseminator_nets.pop_front().unwrap(), epoch_info.clone());
            let repair_network = repair_nets.pop_front().unwrap();
            let repair_request_network = repair_req_nets.pop_front().unwrap();
            let txs_receiver = tx_nets.pop_front().unwrap();
            Alpenglow::new(
                sks[v.id.as_index()].clone(),
                voting_sks[v.id.as_index()].clone(),
                all2all,
                disseminator,
                repair_network,
                repair_request_network,
                epoch_info,
                txs_receiver,
            )
        })
        .collect();

    (nodes, tx_addrs)
}
