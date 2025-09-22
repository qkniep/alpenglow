// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! An abstraction layer for networking.
//!
//! The [`Network`] trait provides a common interface for networking operations.
//! Messages are abstracted as [`NetworkMessage`], instead of e.g. raw bytes.
//!
//! Specific implementations for different underlying network stacks are provided:
//! - [`UdpNetwork`] abstracts a simple UDP socket
//! - [`TcpNetwork`] handles TCP connections under the hood
//! - [`SimulatedNetwork`] provides a simulated network for local testing
//!
//! # Examples
//!
//! ```
//! use alpenglow::network::{Network, NetworkMessage};
//!
//! async fn send_ping_receive_pong(network: impl Network) {
//!     let msg = NetworkMessage::Ping;
//!     network.send(&msg, "127.0.0.1:1337").await.unwrap();
//!     let received = network.receive().await.unwrap();
//!     assert!(matches!(received, NetworkMessage::Pong));
//! }
//! ```

pub mod simulated;
mod tcp;
mod udp;

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use async_trait::async_trait;

pub use self::simulated::SimulatedNetwork;
pub use self::tcp::TcpNetwork;
pub use self::udp::UdpNetwork;
use crate::Transaction;
use crate::consensus::ConsensusMessage;
use crate::repair::{RepairRequest, RepairResponse};
use crate::shredder::Shred;

/// Maximum payload size of a UDP packet.
pub const MTU_BYTES: usize = 1500;

pub const BINCODE_CONFIG: bincode::config::Configuration = bincode::config::standard();

/// Abstraction of a network interface for sending and receiving messages.
#[async_trait]
pub trait Network: Send + Sync {
    type Send;
    type Recv;

    /// Sends the `message` to all the addresses in `addrs`.
    ///
    /// Note that a possible strategy for the implementators is to send to one address after another.
    /// In this strategy, it is possible that if sending to one address fails, the implementator gives up sending to the remaining addresses.
    //
    // NOTE: Consider return a `Vec<Result<()>>` to indicate per address failures.
    async fn send(
        &self,
        message: &Self::Send,
        addrs: impl Iterator<Item = SocketAddr> + Send,
    ) -> std::io::Result<()>;

    // TODO: implement brodcast at `Network` level?

    async fn receive(&self) -> std::io::Result<Self::Recv>;
}

/// A marker trait that constrains [`Network`] to send and receive [`Shred`]
pub trait ShredNetwork: Network<Recv = Shred, Send = Shred> {}
impl ShredNetwork for UdpNetwork<Shred, Shred> {}
impl ShredNetwork for SimulatedNetwork<Shred, Shred> {}

/// A marker trait that constrains [`Network`] to receive [`Transaction`]
pub trait TransactionNetwork: Network<Recv = Transaction> {}
impl TransactionNetwork for UdpNetwork<Transaction, Transaction> {}
impl TransactionNetwork for SimulatedNetwork<Transaction, Transaction> {}

/// A marker trait that constrains [`Network`] to send and receive [`ConsensusMessage`]
pub trait ConsensusNetwork: Network<Recv = ConsensusMessage, Send = ConsensusMessage> {}
impl ConsensusNetwork for UdpNetwork<ConsensusMessage, ConsensusMessage> {}
impl ConsensusNetwork for SimulatedNetwork<ConsensusMessage, ConsensusMessage> {}

/// A marker trait that constrains [`Network`] to send [`RepairResponse`] and receive [`RepairRequest`]
pub trait RepairRequestNetwork: Network<Recv = RepairRequest, Send = RepairResponse> {}
impl RepairRequestNetwork for UdpNetwork<RepairResponse, RepairRequest> {}
impl RepairRequestNetwork for SimulatedNetwork<RepairResponse, RepairRequest> {}

/// A marker trait that constrains [`Network`] to send [`RepairRequest`] and receive [`RepairResponse`]
pub trait RepairNetwork: Network<Recv = RepairResponse, Send = RepairRequest> {}
impl RepairNetwork for UdpNetwork<RepairRequest, RepairResponse> {}
impl RepairNetwork for SimulatedNetwork<RepairRequest, RepairResponse> {}

/// Returns a [`SocketAddr`] bound to the localhost IPv4 and given port.
///
/// NOTE: port 0 is generally reserved and used to get the OS to assign a port.
/// Using this function with port=0 on actual networks might lead to unexpected behaviour.
/// TODO: prevent being able to call this function with port = 0.
pub fn localhost_ip_sockaddr(port: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), port)
}

/// Returns a [`SocketAddr`] that could be bound any arbitrary IP and port.
///
/// This is present here to enable sharing of code between testing and benchmarking.
/// This should not be used in production.
pub fn dontcare_sockaddr() -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 1234)
}
