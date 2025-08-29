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

use std::net::IpAddr;
use std::str::FromStr;

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub use self::simulated::SimulatedNetwork;
pub use self::tcp::TcpNetwork;
pub use self::udp::UdpNetwork;
use crate::Transaction;
use crate::consensus::{Cert, Vote};
use crate::repair::RepairMessage;
use crate::shredder::Shred;

/// Maximum payload size of a UDP packet.
pub const MTU_BYTES: usize = 1500;

const BINCODE_CONFIG: bincode::config::Configuration = bincode::config::standard();

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
    Repair(RepairMessage),
    // FIXME: txs should not be seen on the same connection as other network msgs.
    // This should not be part of this enum.
    Transaction(Transaction),
}

impl NetworkMessage {
    /// Tries to deserialize a `NetworkMessage` from bytes using [`bincode`].
    ///
    /// # Errors
    ///
    /// Returns [`NetworkError::Deserialization`] if bincode decoding fails.
    /// This includes the case where `bytes` exceed the limit of [`MTU_BYTES`].
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, NetworkError> {
        if bytes.len() > MTU_BYTES {
            return Err(NetworkError::Deserialization(
                bincode::error::DecodeError::LimitExceeded,
            ));
        }
        // FIXME add limits similar to https://github.com/anza-xyz/agave/blob/8a77fc39fda83fc528bf032c7cbff6063aafb5c5/core/src/banking_stage/latest_validator_vote_packet.rs#L54
        let (msg, _) = bincode::serde::decode_from_slice(bytes, BINCODE_CONFIG)?;
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
    /// # Errors
    ///
    /// Returns [`NetworkError::Serialization`] if bincode encoding fails.
    /// This includes the case where `buf` is to small to fit this message.
    pub fn to_slice(&self, buf: &mut [u8]) -> Result<usize, NetworkError> {
        let res = bincode::serde::encode_into_slice(self, buf, BINCODE_CONFIG);
        match res {
            Ok(written) => {
                assert!(written <= MTU_BYTES, "each message should fit in MTU");
                Ok(written)
            }
            Err(bincode::error::EncodeError::UnexpectedEnd) => Err(NetworkError::Serialization(
                bincode::error::EncodeError::UnexpectedEnd,
            )),
            _ => panic!("unexpected serialization error"),
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

impl From<RepairMessage> for NetworkMessage {
    fn from(repair: RepairMessage) -> Self {
        Self::Repair(repair)
    }
}

/// Error type for network operations.
#[derive(Debug, Error)]
pub enum NetworkError {
    #[error("unexpected message type for this socket")]
    UnexpectedMessageType,
    #[error("malformed address")]
    MalformedAddress,
    #[error("serialization error")]
    Serialization(#[from] bincode::error::EncodeError),
    #[error("deserialization error")]
    Deserialization(#[from] bincode::error::DecodeError),
    #[error("bad socket state")]
    BadSocket(#[from] std::io::Error),
    #[error("unknown network error")]
    Unknown,
}

/// Abstraction of a network interface for sending and receiving messages.
#[async_trait]
pub trait Network: Send + Sync {
    type Address: Send;

    async fn send(&self, message: &NetworkMessage, to: IpAddr) -> Result<(), NetworkError>;

    async fn send_serialized(&self, bytes: &[u8], to: IpAddr) -> Result<(), NetworkError>;

    // TODO: implement brodcast at `Network` level?

    async fn receive(&self) -> Result<NetworkMessage, NetworkError>;

    fn parse_addr(str: impl AsRef<str>) -> Result<Self::Address, NetworkError>
    where
        Self::Address: FromStr,
    {
        str.as_ref()
            .parse()
            .map_err(|_| NetworkError::MalformedAddress)
    }
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
            let num_bytes = msg.to_slice(&mut buf).unwrap();
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
    async fn serialize_buffer_too_small() {
        let mut buf = [0u8; 1];
        let msg = NetworkMessage::Transaction(Transaction(vec![1; MAX_TRANSACTION_SIZE]));
        assert!(msg.to_slice(&mut buf).is_err());
    }
}
