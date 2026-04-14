// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! An abstraction layer for networking.
//!
//! The [`Network`] trait provides a common interface for networking operations.
//! When implementing [`Network`], the implementor determines the types:
//! - [`Network::Send`]: The type of messages to be sent.
//! - [`Network::Recv`]: The type of messages to be received.
//!
//! Specific implementations for different underlying network stacks are provided:
//! - [`UdpNetwork`] abstracts a simple UDP socket
//! - [`TcpNetwork`] handles TCP connections under the hood
//! - [`SimulatedNetwork`] provides a simulated network for local testing
//!
//! # Examples
//!
//! ```rust
//! use alpenglow::network::{Network, localhost_ip_sockaddr};
//!
//! async fn send_ping_receive_pong(network: impl Network<Send = String, Recv = String>) {
//!     let msg = "ping".to_string();
//!     network.send(&msg, localhost_ip_sockaddr(1337)).await.unwrap();
//!     let received = network.receive().await.unwrap();
//!     assert_eq!(&received, "pong");
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

/// Abstraction of a network interface for sending and receiving messages.
#[async_trait]
pub trait Network: Send + Sync {
    type Send;
    type Recv;

    /// Sends the `message` to all the addresses in `addrs`.
    ///
    /// Note that a possible strategy for the implementators is to send to one address after another.
    /// In this strategy, it is possible that if sending to one address fails, the implementator gives up sending to the remaining addresses.
    /// This means that the function is not atomic, if it fails, some messages may still have been sent.
    //
    // NOTE: Consider return a `Vec<Result<()>>` to indicate per address failures.
    async fn send_to_many(
        &self,
        message: &Self::Send,
        addrs: impl Iterator<Item = SocketAddr> + Send,
    ) -> std::io::Result<()>;

    /// Sends the `message` to `addr`.
    async fn send(&self, message: &Self::Send, addr: SocketAddr) -> std::io::Result<()>;

    // TODO: implement brodcast at `Network` level?

    async fn receive(&self) -> std::io::Result<Self::Recv>;
}

/// A marker trait that constrains [`Network`] to send and receive [`Shred`]
pub trait ShredNetwork: Network<Recv = Shred, Send = Shred> {}
impl<N> ShredNetwork for N where N: Network<Recv = Shred, Send = Shred> {}

/// A marker trait that constrains [`Network`] to receive [`Transaction`]
pub trait TransactionNetwork: Network<Recv = Transaction> {}
impl<N> TransactionNetwork for N where N: Network<Recv = Transaction> {}

/// A marker trait that constrains [`Network`] to send and receive [`ConsensusMessage`]
pub trait ConsensusNetwork: Network<Recv = ConsensusMessage, Send = ConsensusMessage> {}
impl<N> ConsensusNetwork for N where N: Network<Recv = ConsensusMessage, Send = ConsensusMessage> {}

/// A marker trait that constrains [`Network`] to send [`RepairResponse`] and receive [`RepairRequest`]
pub trait RepairRequestNetwork: Network<Recv = RepairRequest, Send = RepairResponse> {}
impl<N> RepairRequestNetwork for N where N: Network<Recv = RepairRequest, Send = RepairResponse> {}

/// A marker trait that constrains [`Network`] to send [`RepairRequest`] and receive [`RepairResponse`]
pub trait RepairNetwork: Network<Recv = RepairResponse, Send = RepairRequest> {}
impl<N> RepairNetwork for N where N: Network<Recv = RepairResponse, Send = RepairRequest> {}

/// Returns a [`SocketAddr`] bound to the localhost IPv4 and given port.
///
/// NOTE: port 0 is generally reserved and used to get the OS to assign a port.
/// Using this function with port=0 on actual networks might lead to unexpected behaviour.
// TODO: prevent being able to call this function with port = 0.
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
