// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! UDP network interface.
//!
//! This module provides an implementation of the [`Network`] trait for UDP sockets.
//! It is essentially a wrapper around [`tokio::net::UdpSocket`].

use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

use async_trait::async_trait;
use log::warn;
use tokio::net::UdpSocket;

use super::{MTU_BYTES, Network, NetworkError, NetworkMessage};

/// Number of bytes used as buffer for any incoming packet.
///
/// This should be enough to receive and deserialize any `NetworkMessage`,
/// since messages we send in our protocols should fit in one MTU size packet.
const RECEIVE_BUFFER_SIZE: usize = MTU_BYTES;

/// Implementation of network abstraction over a simple UDP socket.
pub struct UdpNetwork {
    socket: UdpSocket,
}

impl UdpNetwork {
    /// Creates a new `UdpNetwork` instance bound to the given `port`.
    ///
    /// # Panics
    ///
    /// Panics if the UDP `port` is already in use.
    #[must_use]
    pub fn new(port: u16) -> Self {
        let addr = SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), port);
        let socket = futures::executor::block_on(UdpSocket::bind(addr)).unwrap();
        Self { socket }
    }

    /// Creates a new `UdpNetwork` instance bound to an arbitrary port.
    /// The port is assigned by the OS.
    #[must_use]
    pub fn new_with_any_port() -> Self {
        Self::new(0)
    }

    /// Returns the UDP port number the network is bound to.
    pub fn port(&self) -> u16 {
        self.socket.local_addr().unwrap().port()
    }
}

#[async_trait]
impl Network for UdpNetwork {
    async fn send(&self, message: &NetworkMessage, to: SocketAddr) -> Result<(), NetworkError> {
        let bytes = message.to_bytes();
        self.send_serialized(&bytes, to).await
    }

    async fn send_serialized(&self, bytes: &[u8], to: SocketAddr) -> Result<(), NetworkError> {
        self.socket.send_to(bytes, to).await?;
        Ok(())
    }

    async fn receive(&self) -> Result<NetworkMessage, NetworkError> {
        let mut buf = [0; RECEIVE_BUFFER_SIZE];
        loop {
            let len = self.socket.recv(&mut buf).await?;
            match NetworkMessage::from_bytes(&buf[..len]) {
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
    use crate::network::localhost_ip_sockaddr;

    #[tokio::test]
    async fn ping() {
        let socket1 = UdpNetwork::new_with_any_port();
        let socket2 = UdpNetwork::new_with_any_port();
        let addr1 = localhost_ip_sockaddr(socket1.port());

        // regular send()
        socket2.send(&NetworkMessage::Ping, addr1).await.unwrap();
        let msg = socket1.receive().await.unwrap();
        assert!(matches!(msg, NetworkMessage::Ping));

        // send_serialized()
        let bytes = NetworkMessage::Ping.to_bytes();
        socket2.send_serialized(&bytes, addr1).await.unwrap();
        let msg = socket1.receive().await.unwrap();
        assert!(matches!(msg, NetworkMessage::Ping));
    }

    #[tokio::test]
    async fn ping_pong() {
        let socket1 = UdpNetwork::new_with_any_port();
        let socket2 = UdpNetwork::new_with_any_port();
        let addr1 = localhost_ip_sockaddr(socket1.port());
        let addr2 = localhost_ip_sockaddr(socket2.port());

        socket1.send(&NetworkMessage::Ping, addr2).await.unwrap();
        let msg = socket2.receive().await.unwrap();
        assert!(matches!(msg, NetworkMessage::Ping));
        socket2.send(&NetworkMessage::Pong, addr1).await.unwrap();
        let msg = socket1.receive().await.unwrap();
        assert!(matches!(msg, NetworkMessage::Pong));
    }
}
