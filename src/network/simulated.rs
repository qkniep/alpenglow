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

use std::sync::Arc;

use log::warn;
use tokio::sync::{Mutex, RwLock, mpsc};

use crate::ValidatorId;

use super::{Network, NetworkError, NetworkMessage};

pub use core::SimulatedNetworkCore;
use token_bucket::TokenBucket;

/// A simulated network interface for local testing and simulations.
///
/// # Examples
// TODO: add examples
pub struct SimulatedNetwork {
    /// ID of the validator this network interface belongs to.
    id: ValidatorId,
    /// Reference to the simulated network core this interface is attached to.
    network_core: Arc<SimulatedNetworkCore>,
    /// Receiver for incoming messages.
    receiver: Mutex<mpsc::Receiver<Vec<u8>>>,
    /// Optional rate limiter.
    limiter: Option<RwLock<TokenBucket>>,
}

impl SimulatedNetwork {
    async fn send_byte_vec(
        &self,
        bytes: Vec<u8>,
        to: impl AsRef<str> + Send,
    ) -> Result<(), NetworkError> {
        let to_addr = Self::parse_addr(to)?;
        if let Some(limiter) = &self.limiter {
            limiter.write().await.wait_for(bytes.len()).await;
        }
        self.network_core.send(bytes, self.id, to_addr).await;
        Ok(())
    }
}

impl Network for SimulatedNetwork {
    type Address = ValidatorId;

    async fn send(
        &self,
        message: &NetworkMessage,
        to: impl AsRef<str> + Send,
    ) -> Result<(), NetworkError> {
        let bytes = message.to_bytes();
        self.send_byte_vec(bytes, to).await
    }

    async fn send_serialized(
        &self,
        bytes: &[u8],
        to: impl AsRef<str> + Send,
    ) -> Result<(), NetworkError> {
        self.send_byte_vec(bytes.to_vec(), to).await
    }

    async fn receive(&self) -> Result<NetworkMessage, NetworkError> {
        loop {
            let Some(bytes) = self.receiver.lock().await.recv().await else {
                let io_error = std::io::Error::other("channel closed");
                return Err(NetworkError::BadSocket(io_error));
            };
            match NetworkMessage::from_bytes(&bytes) {
                Ok(msg) => return Ok(msg),
                Err(NetworkError::Deserialization(_)) => warn!("failed deserializing message"),
                Err(err) => return Err(err),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::Slot;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{
        DATA_SHREDS, MAX_DATA_PER_SLICE, RegularShredder, Shredder, TOTAL_SHREDS,
    };
    use crate::slice::{Slice, SliceHeader, create_slice_payload_with_invalid_txs};
    use crate::slice_index::SliceIndex;

    use std::time::Instant;

    #[tokio::test]
    async fn basic() {
        // set up network with two nodes
        let core = Arc::new(SimulatedNetworkCore::default().with_packet_loss(0.0));
        let net1 = core.join(0, 8192, 8192).await;
        let net2 = core.join(1, 8192, 8192).await;
        let msg = NetworkMessage::Ping;

        // one direction
        net1.send(&msg, "1").await.unwrap();
        if !matches!(net2.receive().await, Ok(NetworkMessage::Ping)) {
            panic!("received wrong message");
        }

        // other direction
        net2.send(&msg, "0").await.unwrap();
        if !matches!(net1.receive().await, Ok(NetworkMessage::Ping)) {
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
        let net1 = core.join(0, 32_768, 32_768).await; // 32 KiB/s
        let net2 = core.join(1, 32_768, 32_768).await; // 32 KiB/s

        // create 2 slices
        let mut rng = rand::rng();
        let sk = SecretKey::new(&mut rng);
        let mut shreds = Vec::new();
        for i in 0..2 {
            let payload = create_slice_payload_with_invalid_txs(None, MAX_DATA_PER_SLICE);
            let header = SliceHeader {
                slot: Slot::new(0),
                slice_index: SliceIndex::new_unchecked(i),
                is_last: i == 1,
            };
            let slice = Slice::from_parts(header, payload, None);
            let slice_shreds = RegularShredder::shred(slice, &sk).unwrap();
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
            while let Ok(msg) = net2.receive().await {
                if matches!(msg, NetworkMessage::Shred(_)) {
                    shreds_received += 1;
                    if shreds_received == 2 * TOTAL_SHREDS {
                        return now.elapsed().as_secs_f64();
                    }
                }
            }
            panic!("not all shreds received");
        });

        for shred in shreds {
            let msg = NetworkMessage::Shred(shred);
            net1.send(&msg, "1").await.unwrap();
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
        let net1 = core.join(0, 104_857_600, 104_857_600).await; // 100 MiB/s
        let net2 = core.join(1, 104_857_600, 104_857_600).await; // 100 MiB/s

        // create 1000 slices
        let mut rng = rand::rng();
        let sk = SecretKey::new(&mut rng);
        let mut shreds = Vec::new();
        for i in 0..1000 {
            let payload = create_slice_payload_with_invalid_txs(None, MAX_DATA_PER_SLICE);
            let header = SliceHeader {
                slot: Slot::new(0),
                slice_index: SliceIndex::new_unchecked(i),
                is_last: i == 999,
            };
            let slice = Slice::from_parts(header, payload, None);
            let slice_shreds = RegularShredder::shred(slice, &sk).unwrap();
            shreds.extend(slice_shreds);
        }

        let t_latency = 1000.0 * MAX_DATA_PER_SLICE as f64 / 100.0 / 1024.0 / 1024.0;
        let p_latency = 0.1;
        let expansion_ratio = (TOTAL_SHREDS as f64) / (DATA_SHREDS as f64);
        let min = p_latency + t_latency * expansion_ratio; // account for erasure coding
        let max = p_latency + t_latency * expansion_ratio * 1.41; // +36% metadata overhead, +5% margin

        // background task: receive shreds and measure latency
        let receiver = tokio::spawn(async move {
            let mut shreds_received = 0;
            let now = Instant::now();
            while let Ok(msg) = net2.receive().await {
                if matches!(msg, NetworkMessage::Shred(_)) {
                    shreds_received += 1;
                    if shreds_received == 1000 * TOTAL_SHREDS {
                        return now.elapsed().as_secs_f64();
                    }
                }
            }
            panic!("not all shreds received");
        });

        for shred in shreds {
            let msg = NetworkMessage::Shred(shred);
            net1.send(&msg, "1").await.unwrap();
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
        let net1 = core.join_unlimited(0).await;
        let net2 = core.join_unlimited(1).await;

        // create 10,000 slices
        let mut rng = rand::rng();
        let sk = SecretKey::new(&mut rng);
        let mut shreds = Vec::new();
        for i in 0..10_000 {
            let payload = create_slice_payload_with_invalid_txs(None, MAX_DATA_PER_SLICE);
            let header = SliceHeader {
                slot: Slot::new(0),
                slice_index: SliceIndex::new_unchecked(i),
                is_last: i == 9999,
            };
            let slice = Slice::from_parts(header, payload, None);
            let slice_shreds = RegularShredder::shred(slice, &sk).unwrap();
            shreds.extend(slice_shreds);
        }

        // achieving at least 256 MiB/s
        let t_latency = 10_000.0 * MAX_DATA_PER_SLICE as f64 / 256.0 / 1024.0 / 1024.0;
        let p_latency = 0.1;
        let expansion_ratio = (TOTAL_SHREDS as f64) / (DATA_SHREDS as f64);
        let max = p_latency + t_latency * expansion_ratio * 1.41; // account for erasure coding + 36% metadata overhead + 5% margin

        // background task: receive shreds and measure latency
        let receiver = tokio::spawn(async move {
            let mut shreds_received = 0;
            let now = Instant::now();
            while let Ok(msg) = net2.receive().await {
                if matches!(msg, NetworkMessage::Shred(_)) {
                    shreds_received += 1;
                    if shreds_received == 10_000 * TOTAL_SHREDS {
                        return now.elapsed().as_secs_f64();
                    }
                }
            }
            panic!("not all shreds received");
        });

        for shred in shreds {
            let msg = NetworkMessage::Shred(shred);
            net1.send(&msg, "1").await.unwrap();
        }

        let latency = tokio::join!(receiver).0.unwrap();
        assert!(latency < max);
    }
}
