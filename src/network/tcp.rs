// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! TCP network interface.
//!
//! This module provides an implementation of the [`Network`] trait for TCP.
//! It uses [`tokio::net::TcpListener`] and [`tokio::net::TcpStream`] under the hood.

use std::marker::PhantomData;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

use async_trait::async_trait;
use futures::SinkExt;
use futures::future::join_all;
use tokio::net::TcpListener;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::sync::{Mutex, RwLock, mpsc};
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};
use wincode::{SchemaRead, SchemaWrite};

use super::Network;
use crate::network::MTU_BYTES;

type StreamReader = FramedRead<OwnedReadHalf, LengthDelimitedCodec>;
type StreamWriter = FramedWrite<OwnedWriteHalf, LengthDelimitedCodec>;

/// Implementation of network abstraction over TCP connections.
// WARN: this is incomplete!
pub struct TcpNetwork<S, R> {
    listener: TcpListener,
    readers: RwLock<Vec<Mutex<StreamReader>>>,
    writers: RwLock<Vec<Mutex<StreamWriter>>>,
    _msg_types: PhantomData<(S, R)>,
}

#[allow(dead_code)]
enum TcpMessage<S, R> {
    Sender(S),
    Receiver(R),
}

impl<S, R> TcpNetwork<S, R> {
    /// Creates a new `TcpNetwork` instance bound to the given `port`.
    ///
    /// # Panics
    ///
    /// Panics if the TCP `port` is already in use.
    #[must_use]
    pub fn new(port: u16) -> Self {
        let addr = SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), port);
        let listener = futures::executor::block_on(TcpListener::bind(addr)).unwrap();
        let (_tx, _rx) = mpsc::channel::<TcpMessage<S, R>>(1024);
        Self {
            listener,
            readers: RwLock::new(Vec::new()),
            writers: RwLock::new(Vec::new()),
            _msg_types: PhantomData,
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

    async fn send_serialized(&self, bytes: &[u8], _addr: SocketAddr) -> std::io::Result<()> {
        assert!(bytes.len() <= MTU_BYTES, "each message should fit in MTU");
        // TODO: use correct socket
        let writer = &self.writers.read().await[0];
        writer.lock().await.send(bytes.to_vec().into()).await?;
        Ok(())
    }
}

#[async_trait]
impl<S, R> Network for TcpNetwork<S, R>
where
    S: SchemaWrite<Src = S> + Send + Sync,
    R: for<'de> SchemaRead<'de, Dst = R> + Send + Sync,
{
    type Recv = R;
    type Send = S;

    async fn send_to_many(
        &self,
        msg: &S,
        addrs: impl Iterator<Item = SocketAddr> + Send,
    ) -> std::io::Result<()> {
        let bytes = &wincode::serialize(msg).unwrap();
        let tasks = addrs.map(async move |addr| self.send_serialized(bytes, addr).await);
        for res in join_all(tasks).await {
            let () = res?;
        }
        Ok(())
    }

    async fn send(&self, msg: &Self::Send, addr: SocketAddr) -> std::io::Result<()> {
        let bytes = wincode::serialize(msg).unwrap();
        self.send_serialized(&bytes, addr).await
    }

    async fn receive(&self) -> std::io::Result<R> {
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
