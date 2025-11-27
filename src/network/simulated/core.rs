// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BinaryHeap, HashMap};
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::{Duration, Instant};

use log::warn;
use rand::Rng;
use tokio::sync::{Mutex, RwLock, mpsc};

use super::SimulatedNetwork;
use super::token_bucket::TokenBucket;
use crate::ValidatorId;

struct SimulatedPacket {
    _from: ValidatorId,
    to: ValidatorId,
    payload: Vec<u8>,
    deliver_at: Instant,
}

// Needed to turn BinaryHeap into min-heap
impl Ord for SimulatedPacket {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.deliver_at.cmp(&self.deliver_at)
    }
}
impl PartialOrd for SimulatedPacket {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq for SimulatedPacket {
    fn eq(&self, other: &Self) -> bool {
        self.deliver_at == other.deliver_at
    }
}
impl Eq for SimulatedPacket {}

/// Simulated network core, where messages are routed between nodes.
///
/// It stores virtual latencies for all links between any pair of nodes.
/// Messages sent by nodes into the network core are then delayed accordingly.
pub struct SimulatedNetworkCore {
    /// Map from node ID to channel for delivering packets.
    nodes: Arc<RwLock<HashMap<ValidatorId, mpsc::Sender<SimulatedPacket>>>>,
    /// Latency between each pair of nodes.
    latencies: RwLock<HashMap<(ValidatorId, ValidatorId), Duration>>,
    /// Fallback latency to use for any link that is not configured.
    default_latency: Duration,
    /// Maximum jitter to apply to each packet in milliseconds.
    per_packet_jitter_ms: f64,
    /// Any packet is lost with this probability.
    per_packet_loss_probability: f64,
    /// Priority queue of packets that are waiting to be delivered.
    pending: Arc<Mutex<BinaryHeap<SimulatedPacket>>>,
}

impl SimulatedNetworkCore {
    /// Creates a new network core with the given latency and packet loss parameters.
    pub fn new(latency_ms: u64, jitter_ms: f64, packet_loss: f64) -> Self {
        let pending = Arc::new(Mutex::new(BinaryHeap::<SimulatedPacket>::new()));
        let nodes = Arc::new(RwLock::new(HashMap::<
            ValidatorId,
            mpsc::Sender<SimulatedPacket>,
        >::new()));

        let p = pending.clone();
        let n = nodes.clone();
        tokio::spawn(async move {
            loop {
                let mut guard = p.lock().await;
                if let Some(msg) = guard.peek()
                    && msg.deliver_at <= Instant::now()
                {
                    let msg = guard.pop().unwrap();
                    let n_guard = n.read().await;
                    let channel = n_guard.get(&msg.to).unwrap();
                    if let Err(_e) = channel.send(msg).await {
                        #[cfg(test)]
                        println!("sending failed. Ignoring");
                        warn!("sending failed. Ignoring");
                    }
                }
            }
        });

        Self {
            nodes,
            latencies: RwLock::new(HashMap::new()),
            default_latency: Duration::from_millis(latency_ms),
            per_packet_jitter_ms: jitter_ms,
            per_packet_loss_probability: packet_loss,
            pending,
        }
    }

    /// Turns this instance into a new instance with a different default latency.
    #[must_use]
    pub const fn with_default_latency(mut self, latency: Duration) -> Self {
        self.default_latency = latency;
        self
    }

    /// Turns this instance into a new instance with a different latency jitter.
    #[must_use]
    pub const fn with_jitter(mut self, jitter: f64) -> Self {
        self.per_packet_jitter_ms = jitter;
        self
    }

    /// Turns this instance into a new instance with a different packet loss rate.
    #[must_use]
    pub const fn with_packet_loss(mut self, probability: f64) -> Self {
        self.per_packet_loss_probability = probability;
        self
    }

    /// Adds a node *without* bandwidth limits to the simulated network.
    ///
    /// The node is registered in the network core with channels.
    /// Returns a [`SimulatedNetwork`] interface for the node.
    /// A new task is spawned that handles the delayed delivery of any messages
    /// targeting that node.
    ///
    /// For limited bandwidth, use [`Self::join`] instead.
    pub async fn join_unlimited<S, R>(self: &Arc<Self>, id: ValidatorId) -> SimulatedNetwork<S, R> {
        // pending -> background
        let (pb_tx, mut pb_rx) = mpsc::channel(65536);
        // background -> receiver
        let (br_tx, br_rx) = mpsc::channel(65536);
        self.nodes.write().await.insert(id, pb_tx);

        let receiver = Mutex::new(br_rx);
        let network_core = Arc::clone(self);

        // background task: receive and push to buffer
        tokio::spawn(async move {
            while let Some(msg) = pb_rx.recv().await {
                br_tx.send(msg.payload).await.unwrap();
            }
        });

        SimulatedNetwork {
            id,
            network_core,
            receiver,
            limiter: None,
            _msg_types: PhantomData,
        }
    }

    /// Adds a node *with* bandwidth limits to the simulated network.
    ///
    /// The node is registered in the network core with channels.
    /// Returns a [`SimulatedNetwork`] interface for the node.
    /// A new task is spawned that handles the delayed delivery of any messages
    /// targeting that node.
    ///
    /// For unlimited bandwidth, use [`Self::join_unlimited`] instead.
    pub async fn join<S, R>(
        self: &Arc<Self>,
        id: ValidatorId,
        up_bandwidth: usize,
        down_bandwidth: usize,
    ) -> SimulatedNetwork<S, R> {
        // pending -> background
        let (pb_tx, mut pb_rx) = mpsc::channel(1000);
        // background -> receiver
        let (br_tx, br_rx) = mpsc::channel(1000);
        self.nodes.write().await.insert(id, pb_tx);

        let receiver = Mutex::new(br_rx);
        let network_core = Arc::clone(self);

        // background task: receive and push to buffer
        tokio::spawn(async move {
            let dl_bw = down_bandwidth.max(1); // prevent div by zero
            let mut limiter = TokenBucket::new(dl_bw);
            while let Some(msg) = pb_rx.recv().await {
                limiter.wait_for(msg.payload.len()).await;
                br_tx.send(msg.payload).await.unwrap();
            }
        });

        let limiter = RwLock::new(TokenBucket::new(up_bandwidth.max(1)));

        SimulatedNetwork {
            id,
            network_core,
            receiver,
            limiter: Some(limiter),
            _msg_types: PhantomData,
        }
    }

    /// Sets the latency between two nodes.
    ///
    /// The latency is symmetric in both directions.
    /// For asymmetric links, use [`Self::set_asymmetric_latency`] instead.
    pub async fn set_latency(&self, node1: ValidatorId, node2: ValidatorId, latency: Duration) {
        self.latencies.write().await.insert((node1, node2), latency);
        self.latencies.write().await.insert((node2, node1), latency);
    }

    /// Sets the latency from one node to the other.
    ///
    /// The latency is set only in one direction, `from` -> `to`.
    /// For symmetric links, use [`Self::set_latency`] instead.
    pub async fn set_asymmetric_latency(
        &self,
        from: ValidatorId,
        to: ValidatorId,
        latency: Duration,
    ) {
        self.latencies.write().await.insert((from, to), latency);
    }

    /// Sends a simulated message from one node to another.
    ///
    /// This schedules delivery for the message after the correct propagation delay.
    pub async fn send(&self, payload: Vec<u8>, from: ValidatorId, to: ValidatorId) {
        if rand::rng().random_range(0.0..1.0) < self.per_packet_loss_probability {
            return;
        }

        let now = Instant::now();
        let guard = self.latencies.read().await;
        let mut latency = *guard.get(&(from, to)).unwrap_or(&self.default_latency);
        if self.per_packet_jitter_ms > 0.0 {
            let jitter = rand::rng().random_range(0.0..self.per_packet_jitter_ms);
            latency += Duration::from_secs_f64(jitter / 1000.0);
        }
        if from == to {
            latency = Duration::from_millis(0);
        }

        let packet = SimulatedPacket {
            deliver_at: now + latency,
            _from: from,
            to,
            payload,
        };
        let mut guard = self.pending.lock().await;
        guard.push(packet);
    }
}

impl Default for SimulatedNetworkCore {
    fn default() -> Self {
        Self::new(100, 5.0, 0.01)
    }
}

#[cfg(test)]
mod tests {
    use tokio::time::timeout;

    use super::*;
    use crate::network::{Network, localhost_ip_sockaddr};
    use crate::test_utils::{Ping, PingOrPong};

    // test simulated latency accuracy to within +/-5%
    const ACCURACY: f64 = 0.05;

    // When run concurrently with other tests on github, then the test fails.
    // Running sequentially seems to help.
    #[tokio::test]
    #[ignore]
    async fn symmetric() {
        // set up network with two nodes
        let msg = Ping::default();
        let core = Arc::new(
            SimulatedNetworkCore::default()
                .with_jitter(0.0)
                .with_packet_loss(0.0),
        );
        let net1 = core.join_unlimited(0).await;
        let net2 = core.join_unlimited(1).await;
        core.set_latency(0, 1, Duration::from_millis(10)).await;

        // one direction
        net1.send(&msg, localhost_ip_sockaddr(1)).await.unwrap();
        let now = Instant::now();
        let _: Ping = net2.receive().await.unwrap();
        let latency = now.elapsed().as_micros();
        let min = (10_000.0 * (1.0 - ACCURACY)) as u128;
        let max = (10_000.0 * (1.0 + ACCURACY)) as u128;
        assert!(latency > min);
        assert!(latency < max);

        // other direction
        net2.send(&msg, localhost_ip_sockaddr(0)).await.unwrap();
        let now = Instant::now();
        let _: Ping = net1.receive().await.unwrap();
        let latency = now.elapsed().as_micros();
        let min = (10_000.0 * (1.0 - ACCURACY)) as u128;
        let max = (10_000.0 * (1.0 + ACCURACY)) as u128;
        assert!(latency > min);
        assert!(latency < max);
    }

    // When run concurrently with other tests on github, then the test fails.
    // Running sequentially seems to help.
    #[tokio::test]
    #[ignore]
    async fn asymmetric() {
        // set up network with two nodes
        let msg = Ping::default();
        let core = Arc::new(
            SimulatedNetworkCore::default()
                .with_jitter(0.0)
                .with_packet_loss(0.0),
        );
        let net1 = core.join_unlimited(0).await;
        let net2 = core.join_unlimited(1).await;
        core.set_asymmetric_latency(0, 1, Duration::from_millis(10))
            .await;
        core.set_asymmetric_latency(1, 0, Duration::from_millis(100))
            .await;

        // one direction
        net1.send(&msg, localhost_ip_sockaddr(1)).await.unwrap();
        let now = Instant::now();
        let _: Ping = net2.receive().await.unwrap();
        let latency = now.elapsed().as_micros();
        let min = (10_000.0 * (1.0 - ACCURACY)) as u128;
        let max = (10_000.0 * (1.0 + ACCURACY)) as u128;
        assert!(
            latency > min,
            "latency {latency} should be greater than {min}"
        );
        assert!(
            latency < max,
            "latency {latency} should be less than max {max}"
        );

        // other direction
        net2.send(&msg, localhost_ip_sockaddr(0)).await.unwrap();
        let now = Instant::now();
        let _: Ping = net1.receive().await.unwrap();
        let latency = now.elapsed().as_micros();
        let min = (100_000.0 * (1.0 - ACCURACY)) as u128;
        let max = (100_000.0 * (1.0 + ACCURACY)) as u128;
        assert!(latency > min);
        assert!(latency < max);
    }

    #[tokio::test]
    async fn latency_order() {
        // set up network with three nodes
        let core = Arc::new(SimulatedNetworkCore::default().with_packet_loss(0.0));
        let net1: SimulatedNetwork<PingOrPong, PingOrPong> = core.join_unlimited(0).await;
        let net2: SimulatedNetwork<PingOrPong, PingOrPong> = core.join_unlimited(1).await;
        let net3: SimulatedNetwork<PingOrPong, PingOrPong> = core.join_unlimited(2).await;
        let sock0 = localhost_ip_sockaddr(0);
        core.set_latency(0, 1, Duration::from_millis(10)).await;
        core.set_latency(0, 2, Duration::from_millis(20)).await;

        // send ping on faster link
        let msg = PingOrPong::Ping([0; 32]);
        net2.send(&msg, sock0).await.unwrap();
        // send pong on slower link
        let msg = PingOrPong::Pong([0; 32]);
        net3.send(&msg, sock0).await.unwrap();

        // ping should arrive before pong
        let received = net1.receive().await.unwrap();
        assert_eq!(received, PingOrPong::Ping([0; 32]));
        let received = net1.receive().await.unwrap();
        assert_eq!(received, PingOrPong::Pong([0; 32]));

        // queue messages in the other order
        let msg = PingOrPong::Pong([0; 32]);
        net3.send(&msg, sock0).await.unwrap();
        let msg = PingOrPong::Ping([0; 32]);
        net2.send(&msg, sock0).await.unwrap();

        // ping should still arrive before pong
        let received = net1.receive().await.unwrap();
        assert_eq!(received, PingOrPong::Ping([0; 32]));
        let received = net1.receive().await.unwrap();
        assert_eq!(received, PingOrPong::Pong([0; 32]));
    }

    #[tokio::test]
    async fn packet_loss() {
        // set up network with two nodes and 50% packet loss
        let core = Arc::new(SimulatedNetworkCore::default().with_packet_loss(0.5));
        let net1: SimulatedNetwork<Ping, Ping> = core.join_unlimited(0).await;
        let net2: SimulatedNetwork<Ping, Ping> = core.join_unlimited(1).await;

        // send 1000 pings
        let msg = Ping::default();
        for _ in 0..1000 {
            net1.send(&msg, localhost_ip_sockaddr(1)).await.unwrap();
        }

        let mut pings_received = 0;
        let max_time = Duration::from_millis(100);
        while let Ok(Ok(_)) = timeout(max_time, net2.receive()).await {
            pings_received += 1;
        }

        // should receive roughly 50% of pings
        assert!(pings_received > 400);
        assert!(pings_received < 600);
    }
}
