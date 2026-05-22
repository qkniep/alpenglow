// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! UDP network interface.
//!
//! This module provides an implementation of the [`Network`] trait for UDP sockets.
//! It is essentially a wrapper around [`tokio::net::UdpSocket`].
//!
//! On Linux, `send_to_many` uses the `sendmmsg(2)` syscall to emit a fanout
//! batch with a single kernel transition; other platforms fall back to issuing
//! one `sendto` per destination.

use std::marker::PhantomData;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

use async_trait::async_trait;
use futures::future::join_all;
use log::warn;
use tokio::net::UdpSocket;
use wincode::config::DefaultConfig;
use wincode::{SchemaRead, SchemaWrite};

use super::MTU_BYTES;
use crate::network::Network;

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
        let addr = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, port);
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
    S: SchemaWrite<DefaultConfig, Src = S> + Send + Sync,
    R: for<'de> SchemaRead<'de, DefaultConfig, Dst = R> + Send + Sync,
{
    type Recv = R;
    type Send = S;

    async fn send_to_many(
        &self,
        msg: &S,
        addrs: impl Iterator<Item = SocketAddr> + Send,
    ) -> std::io::Result<()> {
        let bytes = wincode::serialize(msg).unwrap();
        assert!(bytes.len() <= MTU_BYTES, "each message should fit in MTU");

        #[cfg(target_os = "linux")]
        {
            let addrs: Vec<SocketAddr> = addrs.collect();
            sendmmsg::send_to_many_linux(&self.socket, &bytes, &addrs).await
        }

        #[cfg(not(target_os = "linux"))]
        {
            let tasks = addrs.map(async |addr| self.send_serialized(&bytes, addr).await);
            for res in join_all(tasks).await {
                let () = res?;
            }
            Ok(())
        }
    }

    async fn send(&self, msg: &Self::Send, addr: SocketAddr) -> std::io::Result<()> {
        let bytes = &wincode::serialize(msg).unwrap();
        self.send_serialized(bytes, addr).await
    }

    async fn receive(&self) -> std::io::Result<R> {
        let mut buf = [0; RECEIVE_BUFFER_SIZE];
        loop {
            let _bytes_recved = self.socket.recv(&mut buf).await?;
            let msg = match wincode::deserialize(&buf) {
                Ok(r) => r,
                Err(err) => {
                    warn!("deserializing failed with {err:?}");
                    continue;
                }
            };
            return Ok(msg);
        }
    }
}

/// Linux-only `sendmmsg(2)` fast path for fanout sends.
///
/// Issues one `sendmmsg` syscall per chunk of up to `UIO_MAXIOV` destinations,
/// with every entry's `iovec` pointing at the same serialized payload — so the
/// kernel reads from one userspace buffer and emits N independent UDP packets.
/// This replaces N `sendto` syscalls (and N tokio wakers) with one syscall per
/// 1024-packet chunk.
#[cfg(target_os = "linux")]
mod sendmmsg {
    use std::io;
    use std::net::SocketAddr;
    use std::os::fd::AsRawFd;

    use socket2::SockAddr;
    use tokio::io::Interest;
    use tokio::net::UdpSocket;

    /// Maximum messages per `sendmmsg` syscall. Linux caps `vlen` at `UIO_MAXIOV`
    /// (1024); larger fanouts are chunked across multiple syscalls.
    const MAX_BATCH: usize = 1024;

    pub(super) async fn send_to_many_linux(
        socket: &UdpSocket,
        payload: &[u8],
        addrs: &[SocketAddr],
    ) -> io::Result<()> {
        if addrs.is_empty() {
            return Ok(());
        }

        let n = addrs.len();
        // socket2 builds a correctly-laid-out sockaddr_storage + length for v4/v6.
        let sockaddrs: Vec<SockAddr> = addrs.iter().map(|a| SockAddr::from(*a)).collect();

        // One iovec per message, all pointing at the shared payload buffer. The
        // kernel only reads from these, so the aliased pointers are sound.
        let mut iovecs: Vec<libc::iovec> = (0..n)
            .map(|_| libc::iovec {
                iov_base: payload.as_ptr() as *mut libc::c_void,
                iov_len: payload.len(),
            })
            .collect();

        // Build mmsghdr entries linking each msg_hdr to its sockaddr + iovec.
        // We use raw pointers into `sockaddrs` and `iovecs` rather than `&mut`
        // borrows so the array can be re-indexed across retry iterations
        // without re-borrowing.
        let iov_ptr = iovecs.as_mut_ptr();
        let mut msgs: Vec<libc::mmsghdr> = (0..n)
            .map(|i| {
                let mut msg_hdr: libc::msghdr = unsafe { std::mem::zeroed() };
                msg_hdr.msg_name = sockaddrs[i].as_ptr() as *mut libc::c_void;
                msg_hdr.msg_namelen = sockaddrs[i].len();
                msg_hdr.msg_iov = unsafe { iov_ptr.add(i) };
                msg_hdr.msg_iovlen = 1;
                libc::mmsghdr { msg_hdr, msg_len: 0 }
            })
            .collect();

        let fd = socket.as_raw_fd();
        let mut sent = 0;
        while sent < n {
            socket.writable().await?;
            let chunk_len = (n - sent).min(MAX_BATCH);
            let chunk = &mut msgs[sent..sent + chunk_len];
            let res = socket.try_io(Interest::WRITABLE, || {
                // SAFETY: `fd` is owned by `socket` and live for the duration of
                // this call. `chunk` is a valid `&mut [mmsghdr]`; each entry's
                // `msg_name`/`msg_iov` point into `sockaddrs`/`iovecs`, which
                // outlive the call. The kernel only reads from these.
                let r = unsafe {
                    libc::sendmmsg(
                        fd,
                        chunk.as_mut_ptr(),
                        chunk.len() as libc::c_uint,
                        0,
                    )
                };
                if r < 0 {
                    Err(io::Error::last_os_error())
                } else {
                    Ok(r as usize)
                }
            });
            match res {
                Ok(n_sent) => sent += n_sent,
                // tokio decided the fd isn't actually writable; go back to wait.
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => continue,
                // Interrupted before any messages sent; retry the same chunk.
                Err(e) if e.raw_os_error() == Some(libc::EINTR) => continue,
                Err(e) => return Err(e),
            }
        }
        Ok(())
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
        socket2.send(&Ping::default(), addr1).await.unwrap();
        let msg = socket1.receive().await.unwrap();
        assert_eq!(msg.0, Ping::default().0);
    }

    #[tokio::test]
    async fn ping_pong() {
        let socket1 = UdpNetwork::new_with_any_port();
        let socket2 = UdpNetwork::new_with_any_port();
        let addr1 = localhost_ip_sockaddr(socket1.port());
        let addr2 = localhost_ip_sockaddr(socket2.port());

        socket1.send(&Ping::default(), addr2).await.unwrap();
        let msg: Ping = socket2.receive().await.unwrap();
        assert_eq!(msg.0, Ping::default().0);
        socket2.send(&Pong(msg.0), addr1).await.unwrap();
        let msg: Pong = socket1.receive().await.unwrap();
        assert_eq!(msg.0, Ping::default().0);
    }

    /// `send_to_many` must deliver the payload to every destination.
    ///
    /// Exercises the Linux `sendmmsg` fast path and the portable fallback.
    #[tokio::test]
    async fn send_to_many_fanout() {
        const N: usize = 32;
        let sender: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();

        let mut receivers: Vec<UdpNetwork<Ping, Ping>> = Vec::with_capacity(N);
        let mut addrs: Vec<SocketAddr> = Vec::with_capacity(N);
        for _ in 0..N {
            let r: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();
            addrs.push(localhost_ip_sockaddr(r.port()));
            receivers.push(r);
        }

        let payload = Ping([0xab; 32]);
        sender
            .send_to_many(&payload, addrs.iter().copied())
            .await
            .unwrap();

        for r in &receivers {
            let got = tokio::time::timeout(std::time::Duration::from_secs(2), r.receive())
                .await
                .expect("receiver should get a packet")
                .unwrap();
            assert_eq!(got.0, payload.0);
        }
    }
}
