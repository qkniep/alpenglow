// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! UDP network interface.
//!
//! This module provides an implementation of the [`Network`] trait for UDP sockets.
//! It is essentially a wrapper around [`tokio::net::UdpSocket`].
//!
//! On Linux, `send_to_many` batches a fanout into one `sendmmsg(2)` syscall,
//! and `receive` uses `recvmmsg(2)` to drain a batch of queued datagrams per syscall
//! (buffering the surplus for later calls).
//! Other platforms fall back to one `sendto`/`recv` per packet.

use std::collections::VecDeque;
use std::io;
use std::marker::PhantomData;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

use async_trait::async_trait;
use log::warn;
use parking_lot::Mutex;
use socket2::SockRef;
use tokio::net::UdpSocket;
use wincode::config::DefaultConfig;
use wincode::{SchemaRead, SchemaWrite};

use super::{MTU_BYTES, NetworkMessageConfig};
use crate::network::Network;
use crate::serialize;

/// Number of bytes used as buffer for any incoming packet.
///
/// This should be enough to receive and deserialize any `NetworkMessage`,
/// since messages we send in our protocols should fit in one MTU size packet.
const RECEIVE_BUFFER_SIZE: usize = MTU_BYTES;

/// Kernel-side send/receive buffer size requested per socket.
///
/// The Linux default of ~200 KB is too small to hold even one full broadcast,
/// so a high-fanout `send_to_many` fills the send buffer mid-`sendmmsg`,
/// forcing `EAGAIN` round-trips that erase the syscall amortization.
/// An all2all fanout tops out at 2048 packets (the protocol's max validator count),
/// ~3 MB at MTU; per-`skb` kernel bookkeeping roughly doubles the accounted footprint,
/// so 8 MB queues a whole broadcast with headroom.
const SOCKET_BUFFER_BYTES: usize = 8 * 1024 * 1024;

/// Number of datagrams drained per `recvmmsg(2)` syscall on Linux.
///
/// `receive` reads up to this many queued datagrams in one kernel transition,
/// hands out the first, and buffers the rest.
/// So a burst of `RECV_BATCH` packets costs one syscall instead of one per packet.
/// The scratch buffers backing this are ~`RECV_BATCH * MTU_BYTES` (here ~48 KB)
/// per socket, allocated once at construction.
#[cfg(target_os = "linux")]
const RECV_BATCH: usize = 32;

/// Implementation of network abstraction over a simple UDP socket.
pub struct UdpNetwork<S, R> {
    socket: UdpSocket,
    port: u16,
    /// Buffer of previously drained datagrams from an earlier `recvmmsg` batch.
    /// Filled in arrival order (first is the oldest) and popped from the front.
    recv_queue: Mutex<VecDeque<R>>,
    /// Reusable per-slot receive buffers for the Linux `recvmmsg` fast path.
    /// Allocated once so a batch drain never re-zeroes ~`RECV_BATCH` MTUs of
    /// scratch on every refill; the kernel overwrites the bytes it fills.
    #[cfg(target_os = "linux")]
    recv_scratch: Mutex<Vec<[u8; RECEIVE_BUFFER_SIZE]>>,
    _msg_types: PhantomData<S>,
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
        let socket = futures::executor::block_on(UdpSocket::bind(addr))
            .expect("binding UDP socket should succeed; is the port already in use?");
        let sock_ref = SockRef::from(&socket);

        // `port` might be 0 above, which has the OS assign a free one
        let port = socket
            .local_addr()
            .expect("bound socket should have a local address")
            .port();

        // try to enlarge the kernel-side send/receive buffer
        if let Err(e) = sock_ref.set_send_buffer_size(SOCKET_BUFFER_BYTES) {
            warn!("could not enlarge UDP send buffer: {e}; using the OS default");
        }
        if let Err(e) = sock_ref.set_recv_buffer_size(SOCKET_BUFFER_BYTES) {
            warn!("could not enlarge UDP recv buffer: {e}; using the OS default");
        }
        warn_if_buffer_capped("send", "net.core.wmem_max", sock_ref.send_buffer_size());
        warn_if_buffer_capped("recv", "net.core.rmem_max", sock_ref.recv_buffer_size());

        Self {
            socket,
            port,
            recv_queue: Mutex::new(VecDeque::new()),
            #[cfg(target_os = "linux")]
            recv_scratch: Mutex::new(vec![[0u8; RECEIVE_BUFFER_SIZE]; RECV_BATCH]),
            _msg_types: PhantomData,
        }
    }

    /// Creates a new `UdpNetwork` instance bound to an arbitrary port.
    ///
    /// The port is assigned by the OS.
    #[must_use]
    pub fn new_with_any_port() -> Self {
        Self::new(0)
    }

    /// Returns the UDP port number the network is bound to.
    pub fn port(&self) -> u16 {
        self.port
    }

    async fn send_serialized(&self, bytes: &[u8], addr: SocketAddr) -> io::Result<()> {
        assert!(bytes.len() <= MTU_BYTES, "each message should fit in MTU");
        let bytes_sent = self.socket.send_to(bytes, addr).await?;
        assert_eq!(bytes.len(), bytes_sent);
        Ok(())
    }
}

impl<S, R> UdpNetwork<S, R>
where
    R: for<'de> SchemaRead<'de, NetworkMessageConfig, Dst = R> + Send + Sync,
{
    /// Receives one batch of datagrams from the socket and decodes each into an
    /// `R`, returned in arrival order.
    ///
    /// Datagrams that fail to deserialize are logged and dropped, so the batch
    /// may be shorter than the number read — and empty when the socket was only
    /// spuriously readable or every datagram was malformed, in which case the
    /// caller should simply wait again.
    ///
    /// On Linux this drains up to [`RECV_BATCH`] queued datagrams with a single
    /// `recvmmsg(2)`; on other platforms it reads one datagram per `recv`.
    async fn recv_batch(&self) -> io::Result<VecDeque<R>> {
        #[cfg(target_os = "linux")]
        {
            loop {
                // Wait for readiness with no lock held, so the (potentially
                // long) wait never blocks a concurrent drain of the queue.
                self.socket.readable().await?;

                // `recv_into` is synchronous; the scratch guard is taken only
                // after the await above and never held across one, keeping this
                // future `Send` as `async_trait` requires.
                let mut scratch = self.recv_scratch.lock();
                let lens = match recvmmsg::recv_into(&self.socket, scratch.as_mut_slice()) {
                    Ok(lens) => lens,
                    // tokio reported readable but the queue drained first; re-arm.
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        drop(scratch);
                        continue;
                    }
                    // Interrupted before any datagram was read; retry the wait.
                    Err(e) if e.raw_os_error() == Some(libc::EINTR) => {
                        drop(scratch);
                        continue;
                    }
                    Err(e) => return Err(e),
                };

                let mut batch = VecDeque::with_capacity(lens.len());
                for (i, &len) in lens.iter().enumerate() {
                    match crate::network::deserialize(&scratch[i][..len]) {
                        Ok(msg) => batch.push_back(msg),
                        Err(err) => warn!("deserializing failed with {err}"),
                    }
                }
                return Ok(batch);
            }
        }

        #[cfg(not(target_os = "linux"))]
        {
            let mut buf = [0; RECEIVE_BUFFER_SIZE];
            let len = self.socket.recv(&mut buf).await?;
            let mut batch = VecDeque::new();
            match crate::network::deserialize(&buf[..len]) {
                Ok(msg) => batch.push_back(msg),
                Err(err) => warn!("deserializing failed with {err}"),
            }
            Ok(batch)
        }
    }
}

#[async_trait]
impl<S, R> Network for UdpNetwork<S, R>
where
    S: SchemaWrite<DefaultConfig, Src = S> + Send + Sync,
    R: for<'de> SchemaRead<'de, NetworkMessageConfig, Dst = R> + Send + Sync,
{
    type Recv = R;
    type Send = S;

    async fn send_to_many(
        &self,
        msg: &S,
        addrs: impl IntoIterator<Item = SocketAddr> + Send,
    ) -> io::Result<()> {
        let addrs: Vec<SocketAddr> = addrs.into_iter().collect();
        if addrs.is_empty() {
            return Ok(());
        }

        let bytes = serialize(msg);
        assert!(bytes.len() <= MTU_BYTES, "each message should fit in MTU");

        // single-destination shortcut
        // `sendmmsg(vlen=1)` would have `mmsghdr` setup overhead `sendto` doesn't pay
        if let [addr] = addrs.as_slice() {
            return self.send_serialized(&bytes, *addr).await;
        }

        #[cfg(target_os = "linux")]
        {
            sendmmsg::send_to_many_linux(&self.socket, &bytes, &addrs).await
        }

        // Sequential `try_send_to`, one shared `writable().await` per EAGAIN.
        // The kernel serializes UDP sends on one socket, so the old
        // `join_all`-of-sendtos only added N futures and N waker round-trips.
        #[cfg(not(target_os = "linux"))]
        {
            for addr in addrs {
                loop {
                    match self.socket.try_send_to(&bytes, addr) {
                        Ok(_) => break,
                        Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                            self.socket.writable().await?;
                        }
                        Err(e) => return Err(e),
                    }
                }
            }
            Ok(())
        }
    }

    async fn send(&self, msg: &Self::Send, addr: SocketAddr) -> io::Result<()> {
        let bytes = &serialize(msg);
        self.send_serialized(bytes, addr).await
    }

    async fn receive(&self) -> io::Result<R> {
        loop {
            // Fast path: hand out a datagram drained by an earlier batch. The
            // lock is released before the `await` below — never held across it.
            let queued = self.recv_queue.lock().pop_front();
            if let Some(msg) = queued {
                return Ok(msg);
            }

            // Queue empty: pull a fresh batch from the socket, return its first
            // message, and stash the rest for subsequent calls. An empty batch
            // (spurious wakeup or all-malformed) just loops back to wait again.
            let mut batch = self.recv_batch().await?;
            if let Some(first) = batch.pop_front() {
                if !batch.is_empty() {
                    self.recv_queue.lock().append(&mut batch);
                }
                return Ok(first);
            }
        }
    }
}

/// Normalizes a raw socket-buffer `getsockopt` readback to its effective size.
///
/// Linux reports back twice the granted size,
/// where the extra half is kernel `sk_buff` bookkeeping.
/// Other platforms report the effective size directly.
fn effective_buffer_size(raw: usize) -> usize {
    if cfg!(target_os = "linux") {
        raw / 2
    } else {
        raw
    }
}

/// Warns if the kernel granted a socket buffer smaller than [`SOCKET_BUFFER_BYTES`].
///
/// The size is normalized via [`effective_buffer_size`] first.
fn warn_if_buffer_capped(kind: &str, sysctl: &str, granted: io::Result<usize>) {
    match granted {
        Ok(raw) => {
            let effective = effective_buffer_size(raw);
            if effective < SOCKET_BUFFER_BYTES {
                warn!(
                    "UDP {kind} buffer capped at {effective} B (want {SOCKET_BUFFER_BYTES} B); raise {sysctl} to avoid sendmmsg backpressure"
                );
            }
        }
        Err(err) => warn!("could not read back UDP {kind} buffer size: {err}"),
    }
}

/// Linux-only `sendmmsg(2)` fast path for fanout sends.
///
/// Issues one `sendmmsg` syscall per chunk of up to `UIO_MAXIOV` destinations,
/// every entry's `iovec` pointing at the same serialized payload.
/// So the kernel reads one userspace buffer and emits N independent UDP packets.
/// This replaces N `sendto` syscalls (and N tokio wakers)
/// with just one `sendmmsg` syscall per 1024-packet chunk.
#[cfg(target_os = "linux")]
mod sendmmsg {
    use std::io;
    use std::net::SocketAddr;
    use std::os::fd::AsRawFd;

    use socket2::SockAddr;
    use tokio::io::Interest;
    use tokio::net::UdpSocket;

    /// Maximum messages per `sendmmsg` syscall.
    ///
    /// This matches how Linux caps `vlen` at `UIO_MAXIOV` (1024);
    /// larger fanouts are chunked across multiple syscalls.
    const MAX_BATCH: usize = libc::UIO_MAXIOV as usize;

    /// Sends `payload` to every address in `addrs`, returning once all are queued.
    ///
    /// Empty `addrs` is a no-op; short writes and `EINTR` are retried internally.
    /// Assumes `payload` fits in one MTU (the caller needs to check this).
    pub(super) async fn send_to_many_linux(
        socket: &UdpSocket,
        payload: &[u8],
        addrs: &[SocketAddr],
    ) -> io::Result<()> {
        if addrs.is_empty() {
            return Ok(());
        }

        // `SockAddr` is `Send`, so the addresses are converted once here and held
        // across the `writable().await` below; socket2 lays out the `sockaddr_storage`
        // and length correctly for v4/v6. The raw-pointer `iovec`/`mmsghdr` arrays
        // aren't `Send`, so they're rebuilt inside the syscall closure on each call.
        let sockaddrs: Vec<SockAddr> = addrs.iter().map(|a| SockAddr::from(*a)).collect();
        let n = sockaddrs.len();
        let fd = socket.as_raw_fd();

        let mut sent = 0;
        while sent < n {
            socket.writable().await?;
            let chunk_len = (n - sent).min(MAX_BATCH);

            let res = socket.try_io(Interest::WRITABLE, || {
                // All `mmsghdr` entries share a single `iovec` pointing at the
                // serialized payload: The kernel only reads it, so aliasing is
                // sound and we save N*sizeof(iovec) of setup work per call.
                let mut shared_iov = libc::iovec {
                    iov_base: payload.as_ptr() as *mut libc::c_void,
                    iov_len: payload.len(),
                };
                let iov_ptr: *mut libc::iovec = &mut shared_iov;

                let mut msgs: Vec<libc::mmsghdr> = (0..chunk_len)
                    .map(|i| {
                        let sa = &sockaddrs[sent + i];
                        // SAFETY: `msghdr` is plain POD; zeroing leaves all optional fields
                        // (msg_control, msg_flags, ...) in their documented "absent" state.
                        let mut msg_hdr: libc::msghdr = unsafe { std::mem::zeroed() };
                        msg_hdr.msg_name = sa.as_ptr() as *mut libc::c_void;
                        msg_hdr.msg_namelen = sa.len();
                        msg_hdr.msg_iov = iov_ptr;
                        msg_hdr.msg_iovlen = 1;
                        libc::mmsghdr {
                            msg_hdr,
                            msg_len: 0,
                        }
                    })
                    .collect();

                // SAFETY: `fd` is owned by `socket` and outlives the call. `msgs` is a
                // uniquely-owned, initialized `mmsghdr` slice the kernel writes each `msg_len`
                // back into; every entry's `msg_name`/`msg_iov` borrow `sockaddrs` (outer fn)
                // and `shared_iov` (this frame), alive for the call and only read by the kernel.
                let r =
                    unsafe { libc::sendmmsg(fd, msgs.as_mut_ptr(), msgs.len() as libc::c_uint, 0) };
                if r < 0 {
                    Err(io::Error::last_os_error())
                } else {
                    Ok(r as usize)
                }
            });
            match res {
                Ok(n_sent) => sent += n_sent,
                // tokio decided the fd isn't actually writable; go back to wait
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => continue,
                // interrupted before any messages sent; retry the same chunk
                Err(e) if e.raw_os_error() == Some(libc::EINTR) => continue,
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
}

/// Linux-only `recvmmsg(2)` fast path for batched receives.
///
/// Drains every datagram currently queued on the socket (up to the number of
/// `buffers` provided) with a single `recvmmsg` syscall, replacing N `recvfrom`
/// syscalls (and N tokio wakers) with one. The caller serializes access and
/// must have observed readability first.
#[cfg(target_os = "linux")]
mod recvmmsg {
    use std::io;
    use std::os::fd::AsRawFd;

    use tokio::io::Interest;
    use tokio::net::UdpSocket;

    use super::RECEIVE_BUFFER_SIZE;

    /// Drains queued datagrams from `socket` into `buffers`, returning the byte
    /// length of each datagram received (one entry per packet, arrival order).
    ///
    /// The fd is non-blocking, so `recvmmsg` reads as many datagrams as are
    /// already queued — up to `buffers.len()` — and returns immediately rather
    /// than waiting for the batch to fill. If nothing is queued (a spurious
    /// readiness, or a racing reader drained it) the underlying `EAGAIN`
    /// surfaces as `WouldBlock` for the caller to re-arm on.
    pub(super) fn recv_into(
        socket: &UdpSocket,
        buffers: &mut [[u8; RECEIVE_BUFFER_SIZE]],
    ) -> io::Result<Vec<usize>> {
        let vlen = buffers.len();
        let fd = socket.as_raw_fd();

        socket.try_io(Interest::READABLE, || {
            // One `iovec` per slot, each pointing at that slot's buffer. The
            // backing `iovecs` Vec must outlive the syscall: every `mmsghdr`
            // holds a raw pointer into it.
            let mut iovecs: Vec<libc::iovec> = buffers
                .iter_mut()
                .map(|b| libc::iovec {
                    iov_base: b.as_mut_ptr().cast::<libc::c_void>(),
                    iov_len: RECEIVE_BUFFER_SIZE,
                })
                .collect();

            let mut msgs: Vec<libc::mmsghdr> = iovecs
                .iter_mut()
                .map(|iov| {
                    // SAFETY: `msghdr` is plain POD; zeroing leaves `msg_name`
                    // NULL (so the kernel skips source-address capture, which we
                    // discard anyway) and every other optional field in its
                    // documented "absent" state.
                    let mut msg_hdr: libc::msghdr = unsafe { std::mem::zeroed() };
                    msg_hdr.msg_iov = iov as *mut libc::iovec;
                    msg_hdr.msg_iovlen = 1;
                    libc::mmsghdr {
                        msg_hdr,
                        msg_len: 0,
                    }
                })
                .collect();

            // SAFETY: `fd` is owned by `socket` and live for this call.
            // `msgs.as_mut_ptr()` is a valid pointer to `vlen` initialized
            // `mmsghdr`s; each entry's `msg_iov` points into `iovecs` (alive on
            // this stack frame) whose `iov_base` points into `buffers` (alive
            // for the caller). The kernel writes received bytes into those
            // buffers and the per-datagram length into each `msg_len`.
            let r = unsafe {
                libc::recvmmsg(
                    fd,
                    msgs.as_mut_ptr(),
                    vlen as libc::c_uint,
                    0,
                    std::ptr::null_mut(),
                )
            };
            if r < 0 {
                return Err(io::Error::last_os_error());
            }

            Ok(msgs[..r as usize]
                .iter()
                .map(|m| m.msg_len as usize)
                .collect())
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::time::Duration;

    use tokio::time::timeout;

    use super::*;
    use crate::network::localhost_ip_sockaddr;
    use crate::test_utils::{Ping, Pong};

    #[tokio::test]
    async fn ping() {
        let socket1: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();
        let socket2: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();
        let addr1 = localhost_ip_sockaddr(socket1.port());

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

    #[tokio::test]
    async fn send_to_many_empty_skips_serialization() {
        // construct a message that's larger than MTU (serialization would fail)
        let sender: UdpNetwork<Vec<u8>, Vec<u8>> = UdpNetwork::new_with_any_port();
        let oversized = vec![0u8; MTU_BYTES + 100];
        // this should skip serialization and not panic
        sender.send_to_many(&oversized, []).await.unwrap();
    }

    #[tokio::test]
    async fn send_to_many_single_addr() {
        let sender: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();
        let receiver: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();
        let addr = localhost_ip_sockaddr(receiver.port());

        let payload = Ping([0xcd; 32]);
        sender
            .send_to_many(&payload, std::iter::once(addr))
            .await
            .unwrap();

        // message should arrive
        let got = timeout(Duration::from_secs(2), receiver.receive())
            .await
            .expect("receiver should get a packet")
            .unwrap();
        assert_eq!(got.0, payload.0);
    }

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

        // all messages should arrive
        for r in &receivers {
            let got = timeout(Duration::from_secs(2), r.receive())
                .await
                .expect("receiver should get a packet")
                .unwrap();
            assert_eq!(got.0, payload.0);
        }
    }

    #[tokio::test]
    async fn receive_many_batched() {
        // `N > RECV_BATCH` so the Linux `recvmmsg` path needs more than one batch
        const N: usize = 100;
        #[cfg(target_os = "linux")]
        const _: () = assert!(N > RECV_BATCH);
        let receiver: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();
        let recv_addr = localhost_ip_sockaddr(receiver.port());
        let sender: UdpNetwork<Ping, Ping> = UdpNetwork::new_with_any_port();

        // send datagrams carrying unique IDs
        for i in 0..N {
            let mut payload = [0u8; 32];
            payload[0] = i as u8;
            sender.send(&Ping(payload), recv_addr).await.unwrap();
        }

        // `receive` must deliver every datagram when many arrive back-to-back,
        // regardless of how they were chunked across syscalls.
        let mut seen = HashSet::new();
        for _ in 0..N {
            let got = timeout(Duration::from_secs(5), receiver.receive())
                .await
                .expect("receiver should get every packet")
                .unwrap();
            assert!(
                seen.insert(got.0[0]),
                "datagram {} delivered twice",
                got.0[0]
            );
        }
        for i in 0..N {
            assert!(
                seen.contains(&(i as u8)),
                "datagram {i} was never delivered"
            );
        }
    }
}
