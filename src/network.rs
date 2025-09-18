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

/// Maximum payload size of a UDP packet.
pub const MTU_BYTES: usize = 1500;

pub const BINCODE_CONFIG: bincode::config::Configuration = bincode::config::standard();

/// Abstraction of a network interface for sending and receiving messages.
#[async_trait]
pub trait Network: Send + Sync {
    type Send;
    type Recv;

    async fn send(&self, message: &Self::Send, to: SocketAddr) -> std::io::Result<()>;

    async fn send_serialized(&self, bytes: &[u8], to: SocketAddr) -> std::io::Result<()>;

    // TODO: implement brodcast at `Network` level?

    async fn receive(&self) -> std::io::Result<Self::Recv>;
}

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
