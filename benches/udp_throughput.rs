// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

#![expect(clippy::unwrap_used, reason = "benchmarks panic on setup failure")]

//! Microbenchmarks for the `UdpNetwork` socket path.
//!
//! These measure per-call cost on the egress and ingress paths,
//! giving socket-layer changes unambiguous before/after numbers.
//! The egress fanout path now batches via `sendmmsg` on Linux
//! (see `UdpNetwork::send_to_many`);
//! the ingress path is still one `recvfrom` per call —
//! the natural next target for a `recvmmsg` batch.
//!
//! Two dimensions are swept:
//!
//! - **Payload size** (`Msg32` … `Msg1400`): splits fixed per-packet
//!   syscall/waker cost from variable kernel memcpy cost.
//!   1400 B is near-MTU and approximates a serialized shred.
//! - **Fanout K** (1, 4, 16, 64): how `send_to_many` scales when broadcasting.
//!
//! Notes on what is being measured:
//!
//! - All sockets are on the loopback interface.
//!   Loopback skips the NIC driver, GSO/GRO, and hardware offloads,
//!   so absolute pps numbers run higher than real hardware delivers.
//!   The point is the *relative* gain from dropping per-packet syscalls
//!   and waker round-trips, not the absolute ceiling.
//! - Send-side receivers are bound but not drained.
//!   UDP drops at `SO_RCVBUF` overflow without backpressuring the sender,
//!   so the send-side benches aren't distorted by recv-side work.
//! - For the receive bench, a background tokio task pumps packets continuously;
//!   the bench iteration measures one `receive()` call.
//!
//! For stable numbers, pin the bench to a single core and fix CPU frequency:
//!
//! ```text
//! taskset -c 2 cargo bench --bench udp_throughput
//! sudo cpupower frequency-set -g performance   # Linux
//! ```

use std::net::SocketAddr;

use alpenglow::network::{Network, NetworkMessageConfig, UdpNetwork, localhost_ip_sockaddr};
use divan::counter::{BytesCount, ItemsCount};
use tokio::runtime::Runtime;
use wincode::config::DefaultConfig;
use wincode::{SchemaRead, SchemaWrite};

trait BenchMsg:
    Default
    + Clone
    + Send
    + Sync
    + 'static
    + SchemaWrite<DefaultConfig, Src = Self>
    + for<'de> SchemaRead<'de, NetworkMessageConfig, Dst = Self>
{
    const BYTES: u64;
}

macro_rules! declare_msg {
    ($name:ident, $size:expr) => {
        #[derive(Clone, SchemaRead, SchemaWrite)]
        struct $name([u8; $size]);
        impl Default for $name {
            fn default() -> Self {
                Self([0; $size])
            }
        }
        impl BenchMsg for $name {
            const BYTES: u64 = $size;
        }
    };
}

declare_msg!(Msg32, 32);
declare_msg!(Msg256, 256);
declare_msg!(Msg1024, 1024);
// 1400 B leaves headroom under MTU (1500) for wincode framing and headers
declare_msg!(Msg1400, 1400);

fn main() {
    divan::main();
}

fn multi_thread_runtime() -> Runtime {
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()
        .unwrap()
}

/// A sender, its receivers' addresses, and the receivers themselves.
type FanoutSetup<M> = (UdpNetwork<M, M>, Vec<SocketAddr>, Vec<UdpNetwork<M, M>>);

/// Builds a sender and `k` bound-but-undrained receivers on loopback.
///
/// Returns the sender, the receiver addresses, and the receivers themselves.
/// The caller must keep the latter alive so their ports stay bound for the run.
/// Must be called within a tokio runtime context, as `UdpNetwork` binds eagerly.
fn setup_fanout<M: BenchMsg>(k: usize) -> FanoutSetup<M> {
    let sender: UdpNetwork<M, M> = UdpNetwork::new_with_any_port();
    let mut receivers: Vec<UdpNetwork<M, M>> = Vec::with_capacity(k);
    let mut addrs: Vec<SocketAddr> = Vec::with_capacity(k);
    for _ in 0..k {
        let r: UdpNetwork<M, M> = UdpNetwork::new_with_any_port();
        addrs.push(localhost_ip_sockaddr(r.port()));
        receivers.push(r);
    }
    (sender, addrs, receivers)
}

/// One sender, one receiver, single-packet `send` per iteration.
///
/// Baseline cost of one `sendto` plus tokio scheduling, across payload sizes.
/// Receiver is bound but never read; the kernel drops at `SO_RCVBUF` capacity.
#[divan::bench(types = [Msg32, Msg256, Msg1024, Msg1400])]
fn send_one<M: BenchMsg>(bencher: divan::Bencher) {
    let rt = multi_thread_runtime();
    let (sender, recv_addr, _receiver) = rt.block_on(async {
        let sender: UdpNetwork<M, M> = UdpNetwork::new_with_any_port();
        let receiver: UdpNetwork<M, M> = UdpNetwork::new_with_any_port();
        let addr = localhost_ip_sockaddr(receiver.port());
        (sender, addr, receiver)
    });
    let msg = M::default();

    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(M::BYTES))
        .bench_local(|| {
            rt.block_on(async { sender.send(&msg, recv_addr).await.unwrap() });
        });
}

/// Fanout via `send_to_many` at a realistic shred-sized payload, varying K.
///
/// On Linux this exercises the batched `sendmmsg` path;
/// elsewhere it falls back to a sequential `try_send_to` loop.
/// Reported items/sec is packets/sec
/// (one iteration emits `K` packets of `Msg1400::BYTES` each).
#[divan::bench(consts = [1, 4, 16, 64])]
fn send_to_many_fanout<const K: usize>(bencher: divan::Bencher) {
    let rt = multi_thread_runtime();
    let (sender, addrs, _receivers) = rt.block_on(async { setup_fanout::<Msg1400>(K) });
    let msg = Msg1400::default();

    bencher
        .counter(ItemsCount::new(K))
        .counter(BytesCount::new(Msg1400::BYTES * K as u64))
        .bench_local(|| {
            rt.block_on(async {
                sender
                    .send_to_many(&msg, addrs.iter().copied())
                    .await
                    .unwrap();
            });
        });
}

/// Fanout via `send_to_many` at fixed K=16, varying payload size.
///
/// Shows whether per-packet cost in the fanout path is dominated by
/// syscall overhead (flat across sizes) or kernel memcpy (grows with size).
#[divan::bench(types = [Msg32, Msg256, Msg1024, Msg1400])]
fn send_to_many_sized<M: BenchMsg>(bencher: divan::Bencher) {
    const K: usize = 16;
    let rt = multi_thread_runtime();
    let (sender, addrs, _receivers) = rt.block_on(async { setup_fanout::<M>(K) });
    let msg = M::default();

    bencher
        .counter(ItemsCount::new(K))
        .counter(BytesCount::new(M::BYTES * K as u64))
        .bench_local(|| {
            rt.block_on(async {
                sender
                    .send_to_many(&msg, addrs.iter().copied())
                    .await
                    .unwrap();
            });
        });
}

/// One `receive` per iteration; a background task pumps packets continuously.
///
/// Measures the recv-side cost: per-packet `recvfrom` plus waker overhead.
#[divan::bench(types = [Msg32, Msg256, Msg1024, Msg1400])]
fn receive_one<M: BenchMsg>(bencher: divan::Bencher) {
    let rt = multi_thread_runtime();
    let (receiver, _sender_task) = rt.block_on(async {
        let receiver: UdpNetwork<M, M> = UdpNetwork::new_with_any_port();
        let recv_addr = localhost_ip_sockaddr(receiver.port());
        let sender: UdpNetwork<M, M> = UdpNetwork::new_with_any_port();
        let handle = tokio::spawn(async move {
            let msg = M::default();
            while sender.send(&msg, recv_addr).await.is_ok() {}
        });
        (receiver, handle)
    });

    bencher
        .counter(ItemsCount::new(1_usize))
        .counter(BytesCount::new(M::BYTES))
        .bench_local(|| {
            rt.block_on(async {
                let _: M = receiver.receive().await.unwrap();
            });
        });
}
