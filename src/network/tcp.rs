// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::net::{Ipv4Addr, SocketAddrV4};

use futures::{SinkExt, StreamExt};
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::Mutex;
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};
use tracing::warn;

use crate::ValidatorId;

use super::{Network, NetworkError, NetworkMessage};

/// Implementation of network abstraction over a simple TCP socket.
// WARN: this is incomplete!
pub struct TcpNetwork {
    listener: TcpListener,
    sockets: Vec<Mutex<TcpStream>>,
    readers: Mutex<Vec<FramedRead<OwnedReadHalf, LengthDelimitedCodec>>>,
    writers: Mutex<Vec<FramedWrite<OwnedWriteHalf, LengthDelimitedCodec>>>,
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
        Self {
            listener,
            sockets: Vec::new(),
            readers: Mutex::new(Vec::new()),
            writers: Mutex::new(Vec::new()),
        }
    }

    /// Creates a new `TcpNetwork` instance bound to an arbitrary port.
    /// The port is assigned by the OS.
    #[must_use]
    pub fn new_with_any_port() -> Self {
        Self::new(0)
    }
}

impl Network for TcpNetwork {
    type Address = ValidatorId;

    async fn send(
        &self,
        message: &NetworkMessage,
        to: impl AsRef<str> + Send,
    ) -> Result<(), NetworkError> {
        let bytes = message.to_bytes();
        self.send_serialized(&bytes, to).await
    }

    async fn send_serialized(
        &self,
        bytes: &[u8],
        to: impl AsRef<str> + Send,
    ) -> Result<(), NetworkError> {
        // TODO: use correct socket
        self.writers.lock().await[0]
            .send(bytes.to_vec().into())
            .await?;
        Ok(())
    }

    async fn receive(&self) -> Result<NetworkMessage, NetworkError> {
        let mut readers = self.readers.lock().await;
        loop {
            tokio::select! {
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
                    readers.push(read_framed);
                    self.writers.lock().await.push(write_framed);
                },

                Some(Ok(msg)) = readers[0].next() => {
                    match NetworkMessage::from_bytes(&msg) {
                        Ok(msg) => return Ok(msg),
                        Err(NetworkError::Deserialization(_)) => warn!("failed deserializing message"),
                        Err(err) => return Err(err),
                    }
                },
            }
        }
    }
}

// TODO: re-enable tests once fixed

// #[cfg(test)]
// mod tests {
//     use super::*;
//
//     #[tokio::test]
//     async fn ping() {
//         let socket1 = TcpNetwork::new(12345);
//         let socket2 = TcpNetwork::new(23456);
//         let addr1 = format!("127.0.0.1:{}", 12345);
//         socket2.send(&NetworkMessage::Ping, addr1).await.unwrap();
//         if !matches!(socket1.receive().await, Ok(NetworkMessage::Ping)) {
//             panic!("received wrong message");
//         }
//     }
// }
