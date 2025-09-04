// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! TCP network interface.
//!
//! This module provides an implementation of the [`Network`] trait for TCP.
//! It uses [`tokio::net::TcpListener`] and [`tokio::net::TcpStream`] under the hood.

use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

use async_trait::async_trait;
use futures::SinkExt;
use tokio::net::TcpListener;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::sync::{Mutex, RwLock, mpsc};
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};

use super::{Network, NetworkMessage};
use crate::network::{NetworkReceiveError, NetworkSendError};

type StreamReader = FramedRead<OwnedReadHalf, LengthDelimitedCodec>;
type StreamWriter = FramedWrite<OwnedWriteHalf, LengthDelimitedCodec>;

/// Implementation of network abstraction over TCP connections.
// WARN: this is incomplete!
pub struct TcpNetwork {
    listener: TcpListener,
    readers: RwLock<Vec<Mutex<StreamReader>>>,
    writers: RwLock<Vec<Mutex<StreamWriter>>>,
}

impl TcpNetwork {
    /// Creates a new `TcpNetwork` instance bound to the given `port`.
    ///
    /// # Panics
    ///
    /// Panics if the TCP `port` is already in use.
    #[must_use]
    pub fn new(port: u16) -> Self {
        let addr = SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), port);
        let listener = futures::executor::block_on(TcpListener::bind(addr)).unwrap();
        let (_tx, _rx) = mpsc::channel::<NetworkMessage>(1024);
        Self {
            listener,
            readers: RwLock::new(Vec::new()),
            writers: RwLock::new(Vec::new()),
        }
    }

    /// Creates a new `TcpNetwork` instance bound to an arbitrary port.
    ///
    /// The port is arbitrarily assigned by the OS.
    #[must_use]
    pub fn new_with_any_port() -> Self {
        Self::new(0)
    }

    /// Returns the TCP port number the network is bound to.
    ///
    /// This port is used by all streams and to listen for incoming connections.
    pub fn port(&self) -> u16 {
        self.listener.local_addr().unwrap().port()
    }
}

#[async_trait]
impl Network for TcpNetwork {
    async fn send(&self, message: &NetworkMessage, to: SocketAddr) -> Result<(), NetworkSendError> {
        let bytes = message.to_bytes();
        self.send_serialized(&bytes, to).await
    }

    async fn send_serialized(&self, bytes: &[u8], _to: SocketAddr) -> Result<(), NetworkSendError> {
        // TODO: use correct socket
        let writer = &self.writers.read().await[0];
        writer.lock().await.send(bytes.to_vec().into()).await?;
        Ok(())
    }

    async fn receive_net_msg(&self) -> Result<NetworkMessage, NetworkReceiveError> {
        loop {
            tokio::select! {
                // accept new incoming connections
                Ok((stream, _)) = self.listener.accept() => {
                    let (read_half, write_half) = stream.into_split();
                    let read_framed = FramedRead::new(
                        read_half,
                        LengthDelimitedCodec::builder()
                            .length_field_length(2)
                            .big_endian()
                            .new_codec(),
                    );
                    let write_framed = FramedWrite::new(
                        write_half,
                        LengthDelimitedCodec::builder()
                            .length_field_length(2)
                            .big_endian()
                            .new_codec(),
                    );
                    self.readers.write().await.push(Mutex::new(read_framed));
                    self.writers.write().await.push(Mutex::new(write_framed));
                },

                // TODO: read from all readers
                // Some(Ok(msg)) = readers[0].lock().await.next() => {
                //     match NetworkMessage::from_bytes(&msg) {
                //         Ok(msg) => return Ok(msg),
                //         Err(NetworkReceiveError:Deserialization(_)) => warn!("failed deserializing message"),
                //         Err(err) => return Err(err),
                //     }
                // },
            }
        }
    }
}
