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
use serde::{Deserialize, Serialize};

pub use self::simulated::SimulatedNetwork;
pub use self::tcp::TcpNetwork;
pub use self::udp::UdpNetwork;
use crate::Transaction;
use crate::consensus::{Cert, Vote};
use crate::shredder::Shred;

/// Maximum payload size of a UDP packet.
pub const MTU_BYTES: usize = 1500;

pub const BINCODE_CONFIG: bincode::config::Configuration = bincode::config::standard();

/// Network message type.
///
/// Everything that the Alpenglow validator will send over the network is a `NetworkMessage`.
// TODO: zero-copy deserialization
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum NetworkMessage {
    Ping,
    Pong,
    Shred(Shred),
    Vote(Vote),
    Cert(Cert),
    // FIXME: txs should not be seen on the same connection as other network msgs.
    // This should not be part of this enum.
    Transaction(Transaction),
}

impl NetworkMessage {
    /// Tries to deserialize a `NetworkMessage` from bytes using [`bincode`].
    ///
    /// # Errors
    ///
    /// Returns [`bincode::error::DecodeError`] if bincode decoding fails.
    /// This includes the case where `bytes` exceed the limit of [`MTU_BYTES`].
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, bincode::error::DecodeError> {
        if bytes.len() > MTU_BYTES {
            return Err(bincode::error::DecodeError::LimitExceeded);
        }
        // FIXME add limits similar to https://github.com/anza-xyz/agave/blob/8a77fc39fda83fc528bf032c7cbff6063aafb5c5/core/src/banking_stage/latest_validator_vote_packet.rs#L54
        let (msg, bytes_read) = bincode::serde::decode_from_slice(bytes, BINCODE_CONFIG)?;
        if bytes_read != bytes.len() {
            return Err(bincode::error::DecodeError::UnexpectedEnd {
                additional: bytes.len() - bytes_read,
            });
        }
        Ok(msg)
    }

    /// Serializes this message into owned bytes using [`bincode`].
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let bytes = bincode::serde::encode_to_vec(self, BINCODE_CONFIG)
            .expect("serialization should not panic");
        assert!(bytes.len() <= MTU_BYTES, "each message should fit in MTU");
        bytes
    }

    /// Serializes this message into an existing buffer using [`bincode`].
    ///
    /// # Returns
    ///
    /// Number of bytes used in `buf`.
    ///
    /// # Panics
    ///
    /// Panics if encoding returns an error, including if `buf` was not big enough.
    /// Panics if encoding used more than [`MTU_BYTES`].
    pub fn to_slice(&self, buf: &mut [u8]) -> usize {
        let res = bincode::serde::encode_into_slice(self, buf, BINCODE_CONFIG);
        match res {
            Ok(written) => {
                assert!(written <= MTU_BYTES, "each message should fit in MTU");
                written
            }
            Err(err) => panic!("serialization failed with {err:?}"),
        }
    }
}

impl From<Shred> for NetworkMessage {
    fn from(shred: Shred) -> Self {
        Self::Shred(shred)
    }
}

impl From<Vote> for NetworkMessage {
    fn from(vote: Vote) -> Self {
        Self::Vote(vote)
    }
}

impl From<Cert> for NetworkMessage {
    fn from(cert: Cert) -> Self {
        Self::Cert(cert)
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MAX_TRANSACTION_SIZE;

    #[tokio::test]
    async fn basic() {
        let msg = NetworkMessage::Ping;
        let bytes = msg.to_bytes();
        let deserialized = NetworkMessage::from_bytes(&bytes).unwrap();
        assert!(matches!(deserialized, NetworkMessage::Ping));

        let msg = NetworkMessage::Pong;
        let bytes = msg.to_bytes();
        let deserialized = NetworkMessage::from_bytes(&bytes).unwrap();
        assert!(matches!(deserialized, NetworkMessage::Pong));
    }

    #[tokio::test]
    async fn serialize_reuse_buffer() {
        let mut buf = [0u8; MTU_BYTES];
        for _ in 0..10 {
            let msg = NetworkMessage::Ping;
            let num_bytes = msg.to_slice(&mut buf);
            let deserialized = NetworkMessage::from_bytes(&buf[..num_bytes]).unwrap();
            assert!(matches!(deserialized, NetworkMessage::Ping));
        }
    }

    #[tokio::test]
    async fn deserialize_too_large() {
        let bytes = vec![0u8; MTU_BYTES + 1];
        assert!(NetworkMessage::from_bytes(&bytes).is_err());

        let bytes = vec![0u8; 10 * MTU_BYTES];
        assert!(NetworkMessage::from_bytes(&bytes).is_err());
    }

    #[tokio::test]
    #[should_panic]
    async fn serialize_buffer_too_small() {
        let mut buf = [0u8; 1];
        let msg = NetworkMessage::Transaction(Transaction(vec![1; MAX_TRANSACTION_SIZE]));
        // this should panic
        msg.to_slice(&mut buf);
    }
}
