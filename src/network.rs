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

#[cfg(feature = "quic")]
pub mod quic;
pub mod simulated;
mod udp;

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use async_trait::async_trait;
use wincode::config::Configuration;
use wincode::{ReadResult, SchemaRead};

#[cfg(feature = "quic")]
pub use self::quic::QuicNetwork;
pub use self::simulated::SimulatedNetwork;
pub use self::udp::UdpNetwork;
use crate::consensus::ConsensusMessage;
use crate::repair::{RepairRequest, RepairResponse};
use crate::shredder::Shred;
use crate::{Transaction, ValidatorIndex};

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

/// Identity of the peer a message was received from.
///
/// Transports that cryptographically authenticate their peers (e.g. a future
/// QUIC transport) resolve this to a concrete [`ValidatorIndex`] via
/// [`validator`](PeerId::validator). Transports that cannot attribute traffic
/// to an identity (UDP, simulated) report [`Unauthenticated`], for which
/// [`validator`](PeerId::validator) is always `None`.
pub trait PeerId: Clone + Send + Sync + 'static {
    /// Returns the authenticated validator this peer proved itself to be, or
    /// `None` if the transport does not authenticate its peers.
    fn validator(&self) -> Option<ValidatorIndex> {
        None
    }
}

/// Peer identity reported by transports that do not authenticate their peers.
///
/// Its [`PeerId::validator`] is always `None`, so a message received over such
/// a transport carries no attributable, spoof-proof origin.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Unauthenticated;

impl PeerId for Unauthenticated {}

/// Abstraction of a network interface for sending and receiving messages.
#[async_trait]
pub trait Network: Send + Sync {
    type Send;
    type Recv;
    /// Identity of the peer a received message came from.
    type Peer: PeerId;

    /// Sends the `message` to all the addresses in `addrs`.
    ///
    /// Note that a possible strategy for the implementers is to send to one address after another.
    /// In this strategy, it is possible that if sending to one address fails, the implementer gives up sending to the remaining addresses.
    /// This means that the function is not atomic, if it fails, some messages may still have been sent.
    //
    // NOTE: Consider return a `Vec<Result<()>>` to indicate per address failures.
    async fn send_to_many(
        &self,
        message: &Self::Send,
        addrs: impl IntoIterator<Item = SocketAddr> + Send,
    ) -> std::io::Result<()>;

    /// Sends the `message` to `addr`.
    async fn send(&self, message: &Self::Send, addr: SocketAddr) -> std::io::Result<()>;

    // TODO: implement broadcast at `Network` level?

    /// Receives the next message together with the identity of the peer that
    /// sent it.
    ///
    /// The peer is [`Unauthenticated`] for transports that do not authenticate
    /// their peers. Callers that do not need the origin can use
    /// [`receive`](Network::receive) instead.
    async fn receive_from(&self) -> std::io::Result<(Self::Peer, Self::Recv)>;

    /// Receives the next message, discarding the sender's identity.
    ///
    /// Convenience wrapper over [`receive_from`](Network::receive_from) for the
    /// common case where the origin is not needed.
    async fn receive(&self) -> std::io::Result<Self::Recv> {
        let (_peer, msg) = self.receive_from().await?;
        Ok(msg)
    }

    /// Refuses further traffic from `peer`.
    ///
    /// Lets the caller shun a peer that provably misbehaved (e.g. sent an
    /// invalid signature). The default is a no-op for transports that cannot
    /// attribute or block traffic by identity (UDP, simulated).
    fn ban(&self, _peer: &Self::Peer) {}
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
