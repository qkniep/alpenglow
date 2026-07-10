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
mod udp;

use std::io;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use wincode::config::Configuration;
use wincode::{ReadResult, SchemaRead};

pub use self::simulated::SimulatedNetwork;
pub use self::udp::UdpNetwork;
use crate::Transaction;
use crate::consensus::ConsensusMessage;
use crate::repair::{RepairRequest, RepairResponse};
use crate::shredder::Shred;

/// Maximum payload size of a UDP packet.
pub const MTU_BYTES: usize = 1500;

/// Configuration for [`wincode`] decoding a single off-the-wire message.
///
/// Identical to the [default](wincode::config::DefaultConfig),
/// except preallocation is capped at [`MTU_BYTES`] instead of wincode's 4 MiB default.
/// Used by [`deserialize`].
pub type NetworkMessageConfig = Configuration<true, MTU_BYTES>;

/// Deserializes a single message received off the network.
///
/// Every message in our protocols fits in one [`MTU_BYTES`] datagram,
/// so unlike a plain [`wincode::deserialize`], this:
/// - caps preallocation at [`MTU_BYTES`] (wincode defaults to 4 MiB), and
/// - requires the bytes to be fully consumed, rejecting trailing garbage.
pub fn deserialize<'de, T>(bytes: &'de [u8]) -> ReadResult<T>
where
    T: SchemaRead<'de, NetworkMessageConfig, Dst = T>,
{
    wincode::config::deserialize_exact(bytes, NetworkMessageConfig::new())
}

/// Abstraction of a network interface for sending and receiving messages.
pub trait Network: Send + Sync {
    type Send;
    type Recv;

    /// Sends the `message` to `addr`.
    ///
    /// # Errors
    ///
    /// Returns an [`io::Error`] if the underlying network operation fails.
    fn send(
        &self,
        message: &Self::Send,
        addr: SocketAddr,
    ) -> impl Future<Output = io::Result<()>> + Send;

    /// Sends the `message` to all the addresses in `addrs`, best-effort.
    ///
    /// Every address is attempted even if some sends fail.
    /// Therefore the function is not atomic:
    /// On error, some messages may still have been sent (and others not).
    /// A failure of the underlying network itself may abort the remaining sends early.
    ///
    /// # Errors
    ///
    /// Returns only the *first* [`io::Error`] encountered if any.
    fn send_to_many(
        &self,
        message: &Self::Send,
        addrs: impl IntoIterator<Item = SocketAddr> + Send,
    ) -> impl Future<Output = io::Result<()>> + Send;

    /// Receives a message from the network.
    ///
    /// Waits until the next message is received.
    /// Messages that fail to deserialize are dropped and waiting continues.
    ///
    /// # Errors
    ///
    /// Returns an [`io::Error`] if the underlying network operation fails.
    fn receive(&self) -> impl Future<Output = io::Result<Self::Recv>> + Send;
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

/// A marker trait for the repair requester side: drives repairs by sending
/// [`RepairRequest`] and receiving [`RepairResponse`].
pub trait RepairRequesterNetwork: Network<Recv = RepairResponse, Send = RepairRequest> {}
impl<N> RepairRequesterNetwork for N where N: Network<Recv = RepairResponse, Send = RepairRequest> {}

/// A marker trait for the repair responder side: answers incoming requests by
/// receiving [`RepairRequest`] and sending [`RepairResponse`].
pub trait RepairResponderNetwork: Network<Recv = RepairRequest, Send = RepairResponse> {}
impl<N> RepairResponderNetwork for N where N: Network<Recv = RepairRequest, Send = RepairResponse> {}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deserialize_requires_exact() {
        let bytes = wincode::serialize(&42u64).unwrap();
        assert_eq!(deserialize::<u64>(&bytes).unwrap(), 42);

        let mut with_trailing = bytes;
        with_trailing.push(0);
        assert!(deserialize::<u64>(&with_trailing).is_err());
    }
}
