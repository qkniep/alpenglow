// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated network interface.
//!
//! This module provides a in implementation of a simulated network interface,
//! which may be used for local testing and simulations.
//! It works by having [`SimulatedNetwork`] instances communicate with eachother
//! via an underlying [`SimulatedNetworkCore`], which links them together.
//! The network core handles channels for sending packets from one node to another.
//! These channels are artificially limited in bandwidth through token buckets.
//! The core also delays delivery of packets, simulating network latency, and
//! supports jitter as well as packet loss.
//!
//! Further, this module exposes real-world data via its sub-modules:
//! - [`ping_data`] for latencies between Solana mainnet validators.
//! - [`stake_distribution`] for working with the Solana mainnet stake distribution.

mod core;
pub mod ping_data;
pub mod stake_distribution;
mod token_bucket;

use std::marker::PhantomData;
use std::net::SocketAddr;
use std::sync::Arc;

use async_trait::async_trait;
use futures::future::join_all;
use log::warn;
use tokio::sync::{Mutex, RwLock, mpsc};
use wincode::{SchemaRead, SchemaWrite};

pub use self::core::SimulatedNetworkCore;
use self::token_bucket::TokenBucket;
use super::Network;
use crate::ValidatorId;
use crate::network::MTU_BYTES;

/// A simulated network interface for local testing and simulations.
pub struct SimulatedNetwork<S, R> {
    /// ID of the validator this network interface belongs to.
    id: ValidatorId,
    /// Reference to the simulated network core this interface is attached to.
    network_core: Arc<SimulatedNetworkCore>,
    /// Receiver for incoming messages.
    receiver: Mutex<mpsc::Receiver<Vec<u8>>>,
    /// Optional rate limiter.
    limiter: Option<RwLock<TokenBucket>>,
    _msg_types: PhantomData<(S, R)>,
}

impl<S, R> SimulatedNetwork<S, R> {
    async fn send_byte_vec(&self, bytes: Vec<u8>, to: ValidatorId) -> std::io::Result<()> {
        if let Some(limiter) = &self.limiter {
            limiter.write().await.wait_for(bytes.len()).await;
        }
        self.network_core.send(bytes, self.id, to).await;
        Ok(())
    }

    async fn send_serialized(&self, bytes: Vec<u8>, addr: SocketAddr) -> std::io::Result<()> {
        assert!(bytes.len() <= MTU_BYTES, "each message should fit in MTU");
        let validator_id = addr.port().into();
        self.send_byte_vec(bytes, validator_id).await?;
        Ok(())
    }
}

#[async_trait]
impl<S, R> Network for SimulatedNetwork<S, R>
where
    S: SchemaWrite<Src = S> + Send + Sync,
    R: for<'de> SchemaRead<'de, Dst = R> + Send + Sync,
{
    type Recv = R;
    type Send = S;

    async fn send_to_many(
        &self,
        msg: &S,
        addrs: impl Iterator<Item = SocketAddr> + Send,
    ) -> std::io::Result<()> {
        let bytes = wincode::serialize(msg).unwrap();
        let tasks = addrs.map(|addr| {
            let bytes = bytes.clone();
            async move { self.send_serialized(bytes, addr).await }
        });
        for res in join_all(tasks).await {
            let () = res?;
        }
        Ok(())
    }

    async fn send(&self, msg: &S, addr: SocketAddr) -> std::io::Result<()> {
        let bytes = wincode::serialize(msg).unwrap();
        self.send_serialized(bytes, addr).await
    }

    async fn receive(&self) -> std::io::Result<R> {
        loop {
            let Some(buf) = self.receiver.lock().await.recv().await else {
                return Err(std::io::Error::other("channel closed"));
            };
            let msg = match wincode::deserialize(&buf) {
                Ok(r) => r,
                Err(err) => {
                    warn!("deserializing failed with {err:?}");
                    continue;
                }
            };
            return Ok(msg);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use crate::Slot;
    use crate::crypto::signature::SecretKey;
    use crate::network::localhost_ip_sockaddr;
    use crate::shredder::{
        DATA_SHREDS, MAX_DATA_PER_SLICE, RegularShredder, Shred, Shredder, TOTAL_SHREDS,
    };
    use crate::test_utils::Ping;
    use crate::types::slice::create_slice_payload_with_invalid_txs;
    use crate::types::{Slice, SliceHeader, SliceIndex};

    #[tokio::test]
    async fn basic() {
        // set up network with two nodes
        let core = Arc::new(SimulatedNetworkCore::default().with_packet_loss(0.0));
        let net1 = core.join(0, 8192, 8192).await;
        let net2 = core.join(1, 8192, 8192).await;
        let msg = Ping::default();

        // one direction
        net1.send(&msg, localhost_ip_sockaddr(1)).await.unwrap();
        let received: Ping = net2.receive().await.expect("didn't receive message");
        if received.0 != msg.0 {
            panic!("received wrong message");
        }

        // other direction
        net2.send(&msg, localhost_ip_sockaddr(0)).await.unwrap();
        let received: Ping = net1.receive().await.expect("didn't receive message");
        if received.0 != msg.0 {
            panic!("received wrong message");
        }
    }

    #[tokio::test]
    async fn low_bandwidth() {
        // set up network with two nodes
        let core = Arc::new(
            SimulatedNetworkCore::default()
                .with_jitter(0.0)
                .with_packet_loss(0.0),
        );
        let net1: SimulatedNetwork<Shred, Shred> = core.join(0, 32_768, 32_768).await; // 32 KiB/s
        let net2: SimulatedNetwork<Shred, Shred> = core.join(1, 32_768, 32_768).await; // 32 KiB/s

        // create 2 slices
        let mut shredder = RegularShredder::default();
        let mut rng = rand::rng();
        let sk = SecretKey::new(&mut rng);
        let mut shreds = Vec::new();
        let final_slice_index = SliceIndex::new_unchecked(1);
        for slice_index in final_slice_index.until() {
            let payload = create_slice_payload_with_invalid_txs(None, MAX_DATA_PER_SLICE);
            let header = SliceHeader {
                slot: Slot::new(0),
                slice_index,
                is_last: slice_index == final_slice_index,
            };
            let slice = Slice::from_parts(header, payload, None);
            let slice_shreds = shredder.shred(slice, &sk).unwrap();
            shreds.extend(slice_shreds);
        }

        let t_latency = 2.0 * MAX_DATA_PER_SLICE as f64 / 32_768.0;
        let p_latency = 0.1;
        let expansion_ratio = (TOTAL_SHREDS as f64) / (DATA_SHREDS as f64);
        let min = p_latency + t_latency * expansion_ratio; // accoutn for erasure coding
        let max = p_latency + t_latency * expansion_ratio * 1.41; // +36% metadata overhead, +5% margin

        // background task: receive shreds and measure latency
        let receiver = tokio::spawn(async move {
            let mut shreds_received = 0;
            let now = Instant::now();
            while let Ok(_shred) = net2.receive().await {
                shreds_received += 1;
                if shreds_received == 2 * TOTAL_SHREDS {
                    return now.elapsed().as_secs_f64();
                }
            }
            panic!("not all shreds received");
        });

        for shred in shreds {
            net1.send(&shred, localhost_ip_sockaddr(1)).await.unwrap();
        }

        let latency = tokio::join!(receiver).0.unwrap();
        assert!(latency > min);
        assert!(latency < max);
    }

    #[tokio::test]
    #[ignore]
    async fn high_bandwidth() {
        // set up network with two nodes
        let core = Arc::new(
            SimulatedNetworkCore::default()
                .with_jitter(0.0)
                .with_packet_loss(0.0),
        );
        let net1: SimulatedNetwork<Shred, Shred> = core.join(0, 104_857_600, 104_857_600).await; // 100 MiB/s
        let net2: SimulatedNetwork<Shred, Shred> = core.join(1, 104_857_600, 104_857_600).await; // 100 MiB/s

        // create a full block (1024 slices)
        let mut shredder = RegularShredder::default();
        let mut rng = rand::rng();
        let sk = SecretKey::new(&mut rng);
        let mut shreds = Vec::new();
        let final_slice_index = SliceIndex::new_unchecked(1023);
        for slice_index in final_slice_index.until() {
            let payload = create_slice_payload_with_invalid_txs(None, MAX_DATA_PER_SLICE);
            let header = SliceHeader {
                slot: Slot::new(0),
                slice_index,
                is_last: slice_index == final_slice_index,
            };
            let slice = Slice::from_parts(header, payload, None);
            let slice_shreds = shredder.shred(slice, &sk).unwrap();
            shreds.extend(slice_shreds);
        }

        let t_latency = 1024.0 * MAX_DATA_PER_SLICE as f64 / 100.0 / 1024.0 / 1024.0;
        let p_latency = 0.1;
        let expansion_ratio = (TOTAL_SHREDS as f64) / (DATA_SHREDS as f64);
        let min = p_latency + t_latency * expansion_ratio; // account for erasure coding
        let max = p_latency + t_latency * expansion_ratio * 1.41; // +36% metadata overhead, +5% margin

        // background task: receive shreds and measure latency
        let receiver = tokio::spawn(async move {
            let mut shreds_received = 0;
            let now = Instant::now();
            while let Ok(_shred) = net2.receive().await {
                shreds_received += 1;
                if shreds_received == 1024 * TOTAL_SHREDS {
                    return now.elapsed().as_secs_f64();
                }
            }
            panic!("not all shreds received");
        });

        for shred in shreds {
            net1.send(&shred, localhost_ip_sockaddr(1)).await.unwrap();
        }

        let latency = tokio::join!(receiver).0.unwrap();
        assert!(latency > min);
        assert!(latency < max);
    }

    #[tokio::test]
    #[ignore]
    async fn unlimited_bandwidth() {
        // set up network with two nodes
        let core = Arc::new(
            SimulatedNetworkCore::default()
                .with_jitter(0.0)
                .with_packet_loss(0.0),
        );
        let net1: SimulatedNetwork<Shred, Shred> = core.join_unlimited(0).await;
        let net2: SimulatedNetwork<Shred, Shred> = core.join_unlimited(1).await;

        // create a full block (1024 slices)
        let mut shredder = RegularShredder::default();
        let mut rng = rand::rng();
        let sk = SecretKey::new(&mut rng);
        let mut shreds = Vec::new();
        let final_slice_index = SliceIndex::new_unchecked(1023);
        for slice_index in final_slice_index.until() {
            let payload = create_slice_payload_with_invalid_txs(None, MAX_DATA_PER_SLICE);
            let header = SliceHeader {
                slot: Slot::new(0),
                slice_index,
                is_last: slice_index == final_slice_index,
            };
            let slice = Slice::from_parts(header, payload, None);
            let slice_shreds = shredder.shred(slice, &sk).unwrap();
            shreds.extend(slice_shreds);
        }

        // achieving at least 256 MiB/s
        let t_latency = 1024.0 * MAX_DATA_PER_SLICE as f64 / 256.0 / 1024.0 / 1024.0;
        let p_latency = 0.1;
        let expansion_ratio = (TOTAL_SHREDS as f64) / (DATA_SHREDS as f64);
        let max = p_latency + t_latency * expansion_ratio * 1.41; // account for erasure coding + 36% metadata overhead + 5% margin

        // background task: receive shreds and measure latency
        let receiver = tokio::spawn(async move {
            let mut shreds_received = 0;
            let now = Instant::now();
            while let Ok(_shred) = net2.receive().await {
                shreds_received += 1;
                if shreds_received == 1024 * TOTAL_SHREDS {
                    return now.elapsed().as_secs_f64();
                }
            }
            panic!("not all shreds received");
        });

        for shred in shreds {
            net1.send(&shred, localhost_ip_sockaddr(1)).await.unwrap();
        }

        let latency = tokio::join!(receiver).0.unwrap();
        assert!(latency < max);
    }
}
