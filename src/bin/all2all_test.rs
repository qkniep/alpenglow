// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use core::f64;
use std::sync::Arc;
use std::sync::atomic::AtomicUsize;
use std::time::Duration;

use alpenglow::logging;
use clap::Parser;
use color_eyre::Result;
use log::{debug, info};
use time::OffsetDateTime;
use tokio::net::UdpSocket;
use tokio::sync::{Mutex, RwLock};
use tokio::task::JoinSet;
use wincode::{SchemaRead, SchemaWrite};

// TODO: allow for different leader per round
const LEADER: usize = 0;
const BASE_PORT: u16 = 8000;
const ROUNDS: usize = 1000;
const NODES_PER_MACHINE: usize = 1;
const MACHINES: usize = 30;
const MACHINE_IPS: [&str; MACHINES] = [
    "155.138.138.58",
    "209.250.243.9",
    "45.63.40.210",
    "95.179.181.37",
    "78.141.219.197",
    "209.250.255.181",
    "199.247.24.163",
    "45.63.42.105",
    "45.77.138.184",
    "185.92.222.84",
    "95.179.129.189",
    "95.179.158.247",
    "185.92.223.86",
    "108.61.117.221",
    "95.179.135.249",
    "95.179.156.58",
    "209.250.240.143",
    "95.179.187.221",
    "108.61.165.164",
    "95.179.144.106",
    "136.244.99.214",
    "95.179.130.38",
    "108.61.166.146",
    "209.250.244.52",
    "95.179.176.12",
    "45.32.237.105",
    "199.247.30.136",
    "45.32.236.104",
    "136.244.106.65",
    "136.244.99.112",
];
const TOTAL_NODES: usize = MACHINES * NODES_PER_MACHINE;
const MSG_BUFFER_BYTES: usize = 1500;

/// Simple program to greet a person
#[derive(Debug, Parser)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(long)]
    id: usize,
}

#[derive(SchemaRead, SchemaWrite)]
enum Message {
    Ping(PingMsg),
    Pong(PongMsg),
    Block(BlockMsg),
    Vote(VoteMsg),
}

#[derive(SchemaRead, SchemaWrite)]
struct PingMsg {
    machine: usize,
    timestamp_nanos: i128,
}

#[derive(SchemaRead, SchemaWrite)]
struct PongMsg {
    machine: usize,
    timestamp_nanos: i128,
    timestamp_ping_nanos: i128,
}

#[derive(SchemaRead, SchemaWrite)]
struct BlockMsg {
    machine: usize,
    timestamp_nanos: i128,
    round: usize,
}

#[derive(SchemaRead, SchemaWrite)]
struct VoteMsg {
    machine: usize,
    timestamp_nanos: i128,
    block_timestamp: i128,
    round: usize,
    signature: [u8; 64],
    hash: [u8; 32],
}

#[tokio::main]
async fn main() -> Result<()> {
    let args = Args::parse();

    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    logging::enable_logforth_stderr();

    let machine = Machine::new(args.id);
    machine.run().await?;

    Ok(())
}

struct Machine {
    id: usize,
}

impl Machine {
    const fn new(id: usize) -> Self {
        Self { id }
    }

    async fn run(&self) -> std::io::Result<()> {
        let packets_received = Arc::new(AtomicUsize::new(0));
        let wc_vote_delay = Arc::new(Mutex::new(0.0));
        let sum_vote_delay = Arc::new(Mutex::new(0.0));
        let mut tasks = JoinSet::new();
        let mut sockets = Vec::new();

        let _ = self.ping_test().await;

        // open UDP sockets
        for node in 0..NODES_PER_MACHINE {
            let port = BASE_PORT + u16::try_from(node).unwrap();
            let addr = format!("0.0.0.0:{port}");
            let socket = Arc::new(UdpSocket::bind(&addr).await?);
            sockets.push(socket.clone());
            info!("Node started on {}", socket.local_addr()?);
        }

        // UDP hole punching
        info!("UDP hole punching...");
        for _ in 0..60 {
            tokio::time::sleep(Duration::from_millis(1000)).await;
            for socket in &sockets {
                for id in 0..MACHINES {
                    for d_port in 0..NODES_PER_MACHINE {
                        let ip = get_machine_ip(self.id, id);
                        let port = BASE_PORT + u16::try_from(d_port).unwrap();
                        let rcv_addr = format!("{ip}:{port}");
                        let time = OffsetDateTime::now_utc();
                        let timestamp_nanos = time.unix_timestamp_nanos();
                        let msg = Message::Ping(PingMsg {
                            machine: self.id,
                            timestamp_nanos,
                        });
                        let bytes = wincode::serialize(&msg).unwrap();
                        let _ = socket.send_to(&bytes, rcv_addr).await.unwrap();
                    }
                }
            }
        }

        for (node, socket) in sockets.iter().cloned().enumerate() {
            // listen for and respond to incoming messages
            let pr = packets_received.clone();
            let wcvd = wc_vote_delay.clone();
            let svd = sum_vote_delay.clone();
            let self_id = self.id;
            tasks.spawn(async move {
                let mut round = 0;
                let mut buf = [0; MSG_BUFFER_BYTES];
                loop {
                    let (len, addr) = socket.recv_from(&mut buf).await.unwrap();
                    let msg: Message = wincode::deserialize(&buf[..len]).unwrap();

                    match msg {
                        Message::Vote(vote) => {
                            let timestamp = vote.timestamp_nanos;
                            let vote_time =
                                OffsetDateTime::from_unix_timestamp_nanos(timestamp).unwrap();
                            let rcv_time = OffsetDateTime::now_utc();
                            let delay = (rcv_time - vote_time).as_seconds_f64() * 1000.0;
                            debug!("vote arrived with delay {delay:.1} ms");
                            debug!("{len} bytes received from {addr}");
                            pr.fetch_add(1, std::sync::atomic::Ordering::SeqCst);

                            let block_timestamp = vote.block_timestamp;
                            let block_time =
                                OffsetDateTime::from_unix_timestamp_nanos(block_timestamp).unwrap();
                            let delay = (rcv_time - block_time).as_seconds_f64() * 1000.0;
                            debug!("vote seen {delay:.1} ms after block production");
                            let mut wcvd_guard = wcvd.lock().await;
                            if delay > *wcvd_guard {
                                *wcvd_guard = delay;
                            }
                            drop(wcvd_guard);
                            let mut svd_guard = svd.lock().await;
                            *svd_guard += delay;
                        }

                        Message::Block(block) => {
                            // assert_eq!(block.round, round);
                            debug!("received block for round {round}");

                            // print stats for this round
                            if node == 0 {
                                let packets_expected =
                                    100 * (round + 1) * NODES_PER_MACHINE * TOTAL_NODES;
                                let packets_received = pr.load(std::sync::atomic::Ordering::SeqCst);
                                let packets_lost =
                                    packets_expected.saturating_sub(packets_received);
                                let packet_loss =
                                    100.0 * packets_lost as f64 / packets_expected as f64;
                                info!(
                                    "Packet loss in round {}/{}: {} ({:.1}%)",
                                    round + 1,
                                    ROUNDS,
                                    packets_lost,
                                    packet_loss
                                );

                                info!("WC vote delay: {:.1} ms", *wcvd.lock().await);
                                info!(
                                    "Avg. vote delay: {:.1} ms",
                                    *svd.lock().await / packets_received as f64
                                );
                            }

                            // broadcast vote
                            for _ in 0..100 {
                                for id in 0..MACHINES {
                                    for d_port in 0..NODES_PER_MACHINE {
                                        let port = BASE_PORT + u16::try_from(d_port).unwrap();
                                        let ip = get_machine_ip(self_id, id);
                                        let rcv_addr = format!("{ip}:{port}");
                                        let time = OffsetDateTime::now_utc();
                                        let timestamp_nanos = time.unix_timestamp_nanos();
                                        let msg = Message::Vote(VoteMsg {
                                            machine: self_id,
                                            timestamp_nanos,
                                            block_timestamp: block.timestamp_nanos,
                                            round,
                                            signature: [
                                                1, 6, 9, 15, 18, 29, 30, 33, 37, 47, 51, 53, 54,
                                                56, 73, 80, 81, 93, 94, 95, 102, 104, 106, 107,
                                                109, 111, 115, 117, 120, 134, 136, 141, 148, 150,
                                                152, 153, 165, 173, 181, 182, 183, 186, 203, 207,
                                                208, 210, 211, 218, 219, 221, 223, 224, 225, 228,
                                                229, 231, 232, 242, 246, 248, 251, 252, 254, 255,
                                            ],
                                            hash: [
                                                8, 22, 26, 34, 38, 42, 46, 56, 74, 75, 76, 96, 106,
                                                110, 114, 133, 154, 163, 164, 170, 179, 190, 207,
                                                208, 210, 214, 217, 230, 234, 238, 241, 250,
                                            ],
                                        });
                                        let bytes = wincode::serialize(&msg).unwrap();
                                        let _ = socket.send_to(&bytes, rcv_addr).await.unwrap();
                                        debug!("vote of {len} bytes sent");
                                    }
                                }
                                tokio::time::sleep(Duration::from_millis(1)).await;
                            }
                            round += 1;
                        }

                        _ => {}
                    }
                }
            });

            // leader block production loop
            if self.id * NODES_PER_MACHINE + node == LEADER {
                let self_id = self.id;
                let socket = sockets[node].clone();
                tasks.spawn(async move {
                    info!("Leader waiting for 30s...");
                    tokio::time::sleep(Duration::from_secs(30)).await;

                    info!("Leader block production started!");
                    for round in 0..ROUNDS {
                        tokio::time::sleep(Duration::from_millis(400)).await;

                        let time = OffsetDateTime::now_utc();
                        let timestamp_nanos = time.unix_timestamp_nanos();
                        let msg = Message::Block(BlockMsg {
                            machine: self_id,
                            timestamp_nanos,
                            round,
                        });
                        let bytes = wincode::serialize(&msg).unwrap();

                        for id in 0..MACHINES {
                            for d_port in 0..NODES_PER_MACHINE {
                                let port = BASE_PORT + u16::try_from(d_port).unwrap();
                                let ip = get_machine_ip(self_id, id);
                                let rcv_addr = format!("{ip}:{port}");
                                debug!("sending block to {rcv_addr}");
                                let _ = socket.send_to(&bytes, rcv_addr).await.unwrap();
                            }
                        }
                    }
                });
            }
        }

        let _ = tasks.join_all().await;

        Ok(())
    }

    /// Determine minimum ping between self and other machines.
    async fn ping_test(&self) -> Vec<f64> {
        info!("Performing ping test...");
        let pings = Arc::new(RwLock::new(vec![f64::INFINITY; MACHINES]));

        let addr = format!("0.0.0.0:{}", BASE_PORT - 1);
        let socket = Arc::new(UdpSocket::bind(&addr).await.unwrap());

        let listener = {
            let socket = socket.clone();
            let pings = pings.clone();
            let self_id = self.id;
            tokio::task::spawn(async move {
                let mut buf = [0; MSG_BUFFER_BYTES];
                while let Ok((len, addr)) = socket.recv_from(&mut buf).await {
                    let msg: Message = wincode::deserialize(&buf[..len]).unwrap();
                    match msg {
                        Message::Ping(ping) => {
                            let ip = MACHINE_IPS[ping.machine];
                            let ping_addr = format!("{}:{}", ip, BASE_PORT - 1);
                            let time = OffsetDateTime::now_utc();
                            let timestamp_nanos = time.unix_timestamp_nanos();
                            let response = Message::Pong(PongMsg {
                                machine: self_id,
                                timestamp_nanos,
                                timestamp_ping_nanos: ping.timestamp_nanos,
                            });
                            let bytes = wincode::serialize(&response).unwrap();
                            let _ = socket.send_to(&bytes, ping_addr).await.unwrap();
                        }
                        Message::Pong(pong) => {
                            let timestamp1 = pong.timestamp_ping_nanos;
                            let time1 =
                                OffsetDateTime::from_unix_timestamp_nanos(timestamp1).unwrap();
                            let timestamp2 = pong.timestamp_nanos;
                            let time2 =
                                OffsetDateTime::from_unix_timestamp_nanos(timestamp2).unwrap();
                            let now = OffsetDateTime::now_utc();
                            let rtt = (now - time1).as_seconds_f64() * 1000.0;
                            let ping_time = rtt / 2.0;
                            let p1 = (time2 - time1).as_seconds_f64() * 1000.0;
                            let p2 = (now - time2).as_seconds_f64() * 1000.0;
                            debug!(
                                "ping of {ping_time:.1} ms ({p1:.2} + {p2:.2})observed for {addr}"
                            );
                            if ping_time < pings.read().await[pong.machine] {
                                pings.write().await[pong.machine] = ping_time;
                            }
                        }
                        _ => {}
                    }
                }
            })
        };

        let sender = {
            let pings = pings.clone();
            let self_id = self.id;
            tokio::task::spawn(async move {
                for round in 0.. {
                    tokio::time::sleep(Duration::from_millis(500)).await;
                    for id in 0..MACHINES {
                        for _ in 0..3 {
                            tokio::time::sleep(Duration::from_millis(10)).await;
                            let ip = get_machine_ip(self_id, id);
                            let rcv_addr = format!("{}:{}", ip, BASE_PORT - 1);
                            let time = OffsetDateTime::now_utc();
                            let timestamp_nanos = time.unix_timestamp_nanos();
                            let msg = Message::Ping(PingMsg {
                                machine: self_id,
                                timestamp_nanos,
                            });
                            let bytes = wincode::serialize(&msg).unwrap();
                            let _ = socket.send_to(&bytes, rcv_addr).await.unwrap();
                        }
                    }

                    let machines_missing = pings
                        .read()
                        .await
                        .iter()
                        .filter(|p| p.is_infinite())
                        .count();
                    if round > 10 && machines_missing == 0 {
                        break;
                    }
                    info!("{machines_missing} machines missing");
                }
                tokio::time::sleep(Duration::from_millis(2000)).await;
            })
        };

        tokio::select! {
            _ = sender => {},
            _ = listener => unreachable!(),
        }

        // print determined pings
        for id in 0..MACHINES {
            let ping = pings.read().await[id];
            let ip = get_machine_ip(self.id, id);
            info!("Ping to {ip}: {ping:.1} ms");
        }

        pings.read().await.clone()
    }
}

const fn get_machine_ip(self_id: usize, other_id: usize) -> &'static str {
    if other_id == self_id {
        "127.0.0.1"
    } else {
        MACHINE_IPS[other_id]
    }
}
