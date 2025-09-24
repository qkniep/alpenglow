// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! UDP network interface.
//!
//! This module provides an implementation of the [`Network`] trait for UDP sockets.
//! It is essentially a wrapper around [`tokio::net::UdpSocket`].

use std::marker::PhantomData;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

use async_trait::async_trait;
use futures::future::join_all;
use log::warn;
use serde::Serialize;
use serde::de::DeserializeOwned;
use tokio::net::UdpSocket;

use super::MTU_BYTES;
use crate::network::{BINCODE_CONFIG, Network};

/// Number of bytes used as buffer for any incoming packet.
///
/// This should be enough to receive and deserialize any `NetworkMessage`,
/// since messages we send in our protocols should fit in one MTU size packet.
const RECEIVE_BUFFER_SIZE: usize = MTU_BYTES;

/// Implementation of network abstraction over a simple UDP socket.
pub struct UdpNetwork<S, R> {
    socket: UdpSocket,
    _msg_types: PhantomData<(S, R)>,
}

impl<S, R> UdpNetwork<S, R> {
    /// Creates a new `UdpNetwork` instance bound to the given `port`.
    ///
    /// # Panics
    ///
    /// Panics if the UDP `port` is already in use.
    #[must_use]
    pub fn new(port: u16) -> Self {
        let addr = SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), port);
        let socket = futures::executor::block_on(UdpSocket::bind(addr)).unwrap();
        Self {
            socket,
            _msg_types: PhantomData,
        }
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

    async fn send_serialized(&self, bytes: &[u8], addr: SocketAddr) -> std::io::Result<()> {
        assert!(bytes.len() <= MTU_BYTES, "each message should fit in MTU");
        let bytes_sent = self.socket.send_to(bytes, addr).await?;
        assert_eq!(bytes.len(), bytes_sent);
        Ok(())
    }
}

#[async_trait]
impl<S, R> Network for UdpNetwork<S, R>
where
    S: Serialize + Send + Sync,
    R: DeserializeOwned + Send + Sync,
{
    type Recv = R;
    type Send = S;

    async fn send_to_many(
        &self,
        msg: &S,
        addrs: impl Iterator<Item = SocketAddr> + Send,
    ) -> std::io::Result<()> {
        let bytes = &bincode::serde::encode_to_vec(msg, BINCODE_CONFIG).unwrap();
        let tasks = addrs.map(async move |addr| self.send_serialized(bytes, addr).await);
        for res in join_all(tasks).await {
            let () = res?;
        }
        Ok(())
    }

    async fn send(&self, msg: &Self::Send, addr: SocketAddr) -> std::io::Result<()> {
        let bytes = &bincode::serde::encode_to_vec(msg, BINCODE_CONFIG).unwrap();
        self.send_serialized(bytes, addr).await
    }

    async fn receive(&self) -> std::io::Result<R> {
        let mut buf = [0; RECEIVE_BUFFER_SIZE];
        loop {
            let bytes_recved = self.socket.recv(&mut buf).await?;
            let (msg, bytes_used) = match bincode::serde::decode_from_slice(&buf, BINCODE_CONFIG) {
                Ok(r) => r,
                Err(err) => {
                    warn!("deserializing failed with {err:?}");
                    continue;
                }
            };
            if bytes_used != bytes_recved {
                warn!(
                    "deserialization used {bytes_used} bytes; expected to use {}",
                    buf.len()
                );
                continue;
            }
            return Ok(msg);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::network::localhost_ip_sockaddr;
    use crate::test_utils::{Ping, Pong};

    #[tokio::test]
    async fn ping() {
        let socket1: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();
        let socket2: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();
        let addr1 = localhost_ip_sockaddr(socket1.port());

        // regular send()
        socket2.send(&Ping, addr1).await.unwrap();
        let msg = socket1.receive().await.unwrap();
        assert!(matches!(msg, Ping));
    }

    #[tokio::test]
    async fn ping_pong() {
        let socket1 = UdpNetwork::new_with_any_port();
        let socket2 = UdpNetwork::new_with_any_port();
        let addr1 = localhost_ip_sockaddr(socket1.port());
        let addr2 = localhost_ip_sockaddr(socket2.port());

        socket1.send(&Ping, addr2).await.unwrap();
        let msg = socket2.receive().await.unwrap();
        assert!(matches!(msg, Ping));
        socket2.send(&Pong, addr1).await.unwrap();
        let msg = socket1.receive().await.unwrap();
        assert!(matches!(msg, Pong));
    }
}
