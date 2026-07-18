// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Faithful, discrete-event finalization-latency simulator.
//!
//! Unlike the analytical happy-path model in the `simulations` binary (which
//! computes per-event timings by formula), this simulator runs the *real*
//! `ConsensusCore` on every validator and measures when each one actually
//! finalizes a block. Network delays are supplied as a one-way latency matrix;
//! the engine schedules shred/vote/cert deliveries in a time-ordered event queue
//! and drives each core with the corresponding simulated [`Instant`].
//!
//! This is only possible because the sans-IO core is a pure state machine: time
//! is an argument to `ConsensusCore::handle`, so a whole cluster runs
//! deterministically in one thread with no tokio, sockets, or wall-clock waits.
//!
//! The model is happy-path (full connectivity, no loss, one block on genesis),
//! and dissemination is a single hop from the leader to every validator rather
//! than the multi-hop Rotor tree — so the numbers are a faithful measurement of
//! the *consensus* latency (vote/cert exchange) on top of a simplified
//! dissemination model. Layering real Rotor dissemination on top is future work.

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::sync::Arc;
use std::time::{Duration, Instant};

use super::core::{ConsensusCore, Input, Output};
use super::{ConsensusMessage, EpochInfo, ValidatedCert, ValidatedVote, ValidatorEpochInfo};
use crate::crypto::merkle::{BlockHash, DoubleMerkleTree, GENESIS_BLOCK_HASH};
use crate::crypto::{aggsig, signature};
use crate::network::localhost_ip_sockaddr;
use crate::shredder::{RegularShredder, Shredder, ValidatedShred};
use crate::types::{Slice, SliceHeader, SliceIndex, SlicePayload};
use crate::{BlockId, Slot, Stake, Transaction, ValidatorIndex, ValidatorInfo};

/// Configuration for a single-slot finalization-latency simulation.
pub struct LatencySimConfig {
    /// Stake per validator; its length defines the validator count.
    pub stakes: Vec<Stake>,
    /// One-way network delay between validators: `latencies[sender][receiver]`.
    ///
    /// Must be square with side equal to `stakes.len()`. The diagonal (a
    /// validator to itself) should be zero.
    pub latencies: Vec<Vec<Duration>>,
}

impl LatencySimConfig {
    /// Builds a config with uniform one-way `latency` between distinct validators.
    #[must_use]
    pub fn uniform(num_validators: usize, latency: Duration) -> Self {
        let stakes = vec![Stake::new(1); num_validators];
        let latencies = (0..num_validators)
            .map(|i| {
                (0..num_validators)
                    .map(|j| if i == j { Duration::ZERO } else { latency })
                    .collect()
            })
            .collect();
        Self { stakes, latencies }
    }

    fn num_validators(&self) -> usize {
        self.stakes.len()
    }
}

/// Per-validator time from block production to finalization.
pub struct FinalizationLatency {
    /// `per_node[i]` is the time until validator `i` finalized the block, or
    /// `None` if it never did within the simulation.
    per_node: Vec<Option<Duration>>,
    stakes: Vec<Stake>,
}

impl FinalizationLatency {
    /// Returns `true` iff every validator finalized the block.
    #[must_use]
    pub fn all_finalized(&self) -> bool {
        self.per_node.iter().all(Option::is_some)
    }

    /// The time by which every validator had finalized, if all of them did.
    #[must_use]
    pub fn max(&self) -> Option<Duration> {
        self.per_node
            .iter()
            .copied()
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .max()
    }

    /// The earliest time by which validators holding at least `fraction` of the
    /// total stake had finalized, or `None` if that stake never finalized.
    ///
    /// `fraction` is clamped to `[0, 1]`; e.g. `0.67` gives the time to
    /// two-thirds-stake finalization.
    #[must_use]
    pub fn time_to_stake_fraction(&self, fraction: f64) -> Option<Duration> {
        let total: u64 = self.stakes.iter().map(|s| s.inner()).sum();
        let target = (total as f64 * fraction.clamp(0.0, 1.0)).ceil() as u64;

        let mut finalized: Vec<(Duration, u64)> = self
            .per_node
            .iter()
            .zip(&self.stakes)
            .filter_map(|(time, stake)| time.map(|t| (t, stake.inner())))
            .collect();
        finalized.sort_by_key(|(t, _)| *t);

        let mut acc = 0;
        for (time, stake) in finalized {
            acc += stake;
            if acc >= target {
                return Some(time);
            }
        }
        None
    }

    /// The per-validator finalization times (index = validator).
    #[must_use]
    pub fn per_node(&self) -> &[Option<Duration>] {
        &self.per_node
    }
}

/// Runs one slot of happy-path consensus — one block built on genesis,
/// disseminated to every validator — driven by the real `ConsensusCore` over
/// the configured latencies, and returns when each validator finalizes it.
///
/// # Panics
///
/// Panics if `config.latencies` is not square with side `config.stakes.len()`.
#[must_use]
pub fn simulate_slot_finalization(config: &LatencySimConfig) -> FinalizationLatency {
    let n = config.num_validators();
    assert_eq!(config.latencies.len(), n, "latency matrix must be square");
    assert!(
        config.latencies.iter().all(|row| row.len() == n),
        "latency matrix must be square",
    );

    Simulation::new(config).run()
}

/// A payload scheduled for delivery to a validator at a simulated time.
enum Payload {
    /// A block shred from the dissemination path.
    Shred(ValidatedShred),
    /// A vote or certificate broadcast by another validator.
    Message(ConsensusMessage),
}

/// One entry in the discrete-event queue, ordered by `(time, seq)`.
struct Event {
    time: Duration,
    /// Insertion order, breaking ties deterministically.
    seq: u64,
    target: usize,
    payload: Payload,
}

// Ordered purely by (time, seq); the payload is not part of the ordering.
impl PartialEq for Event {
    fn eq(&self, other: &Self) -> bool {
        self.time == other.time && self.seq == other.seq
    }
}
impl Eq for Event {}
impl PartialOrd for Event {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Event {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse so the `BinaryHeap` (a max-heap) yields the earliest event.
        (other.time, other.seq).cmp(&(self.time, self.seq))
    }
}

/// The running simulation state for [`simulate_slot_finalization`].
struct Simulation<'a> {
    config: &'a LatencySimConfig,
    nodes: Vec<ConsensusCore>,
    epoch_info: EpochInfo,
    /// Maps a simulated `Duration` offset to the `Instant` handed to the core.
    base: Instant,
    queue: BinaryHeap<Event>,
    seq: u64,
    /// First finalization time observed per validator.
    finalized: Vec<Option<Duration>>,
    /// The block-production keys, kept so the leader can shred its block.
    block_sks: Vec<signature::SecretKey>,
}

impl<'a> Simulation<'a> {
    fn new(config: &'a LatencySimConfig) -> Self {
        let n = config.num_validators();
        let (block_sks, voting_sks, epoch_info) = build_validators(&config.stakes);
        let base = Instant::now();
        let nodes = (0..n)
            .map(|id| {
                let vei = Arc::new(ValidatorEpochInfo::new(
                    ValidatorIndex::new(id as u64),
                    epoch_info.clone(),
                ));
                ConsensusCore::new(vei, voting_sks[id].clone(), base)
            })
            .collect();
        Self {
            config,
            nodes,
            epoch_info,
            base,
            queue: BinaryHeap::new(),
            seq: 0,
            finalized: vec![None; n],
            block_sks,
        }
    }

    fn run(mut self) -> FinalizationLatency {
        let n = self.config.num_validators();

        // The leader of the first non-genesis slot produces a block on genesis;
        // slot 1 is not a window start, so notarizing it needs only genesis's
        // (pre-set) notarization, no cross-window parent-ready machinery.
        let slot = Slot::genesis().next();
        let leader = self.epoch_info.leader(slot).id.as_usize();
        let parent = (Slot::genesis(), GENESIS_BLOCK_HASH);
        let (_hash, shreds) = build_block(slot, parent, &self.block_sks[leader]);

        // Disseminate every shred to every validator (single hop from the leader).
        for target in 0..n {
            let delay = self.config.latencies[leader][target];
            for shred in &shreds {
                self.schedule(delay, target, Payload::Shred(shred.clone()));
            }
        }

        while let Some(event) = self.queue.pop() {
            self.process(event);
        }

        FinalizationLatency {
            per_node: self.finalized,
            stakes: self.config.stakes.clone(),
        }
    }

    /// Enqueues `payload` for delivery to `target` at simulated time `time`.
    fn schedule(&mut self, time: Duration, target: usize, payload: Payload) {
        self.queue.push(Event {
            time,
            seq: self.seq,
            target,
            payload,
        });
        self.seq += 1;
    }

    /// Delivers one event to its target validator and reschedules any resulting
    /// broadcasts, recording finalization times.
    fn process(&mut self, event: Event) {
        let now = event.base_plus(self.base);
        let target = event.target;
        let input = match event.payload {
            Payload::Shred(shred) => Some(Input::DisseminatedShred(shred)),
            Payload::Message(msg) => to_input(&self.epoch_info, &msg),
        };
        let Some(input) = input else { return };

        let mut out = Vec::new();
        self.nodes[target].handle(input, now, &mut out);

        let n = self.config.num_validators();
        for output in out {
            match output {
                Output::Broadcast(msg) => {
                    for recipient in 0..n {
                        let delay = self.config.latencies[target][recipient];
                        self.schedule(event.time + delay, recipient, Payload::Message(msg.clone()));
                    }
                }
                Output::Finalized(_) => {
                    // record the first finalization only (the block on genesis)
                    self.finalized[target].get_or_insert(event.time);
                }
                // With full connectivity and no loss, the remaining outputs
                // (repair, parent-ready, commitments) do not affect this
                // single-slot happy-path measurement.
                Output::RequestRepair(_)
                | Output::ParentReady { .. }
                | Output::BlockDisseminated { .. }
                | Output::SliceCommitment { .. } => {}
            }
        }
    }
}

impl Event {
    /// The `Instant` to hand to the core for an event at this simulated time.
    fn base_plus(&self, base: Instant) -> Instant {
        base + self.time
    }
}

/// Validates a broadcast message into a core input against the shared validator
/// set, as the real ingest path would.
fn to_input(epoch_info: &EpochInfo, msg: &ConsensusMessage) -> Option<Input> {
    match msg {
        ConsensusMessage::Vote(vote) => ValidatedVote::try_new(vote.clone(), epoch_info)
            .ok()
            .map(Input::Vote),
        ConsensusMessage::Cert(cert) => ValidatedCert::try_new(cert.clone(), epoch_info)
            .ok()
            .map(Input::Cert),
    }
}

/// Builds a validator set with the given `stakes`, returning per-validator
/// block-production (ed25519) and voting (aggsig) keys plus the [`EpochInfo`].
fn build_validators(
    stakes: &[Stake],
) -> (Vec<signature::SecretKey>, Vec<aggsig::SecretKey>, EpochInfo) {
    let mut rng = rand::rng();
    let mut block_sks = Vec::with_capacity(stakes.len());
    let mut voting_sks = Vec::with_capacity(stakes.len());
    let mut validators = Vec::with_capacity(stakes.len());
    for (id, stake) in stakes.iter().enumerate() {
        let block_sk = signature::SecretKey::new(&mut rng);
        let voting_sk = aggsig::SecretKey::new(&mut rng);
        validators.push(ValidatorInfo {
            id: ValidatorIndex::new(id as u64),
            stake: *stake,
            pubkey: block_sk.to_pk(),
            voting_pubkey: voting_sk.to_pk(),
            all2all_address: localhost_ip_sockaddr(0),
            disseminator_address: localhost_ip_sockaddr(0),
            repair_requester_address: localhost_ip_sockaddr(0),
            repair_responder_address: localhost_ip_sockaddr(0),
        });
        block_sks.push(block_sk);
        voting_sks.push(voting_sk);
    }
    (block_sks, voting_sks, EpochInfo::new(validators))
}

/// Builds a leader's single-slice, transaction-free block on top of `parent`.
fn build_block(
    slot: Slot,
    parent: BlockId,
    block_sk: &signature::SecretKey,
) -> (BlockHash, Vec<ValidatedShred>) {
    let txs: Vec<Transaction> = Vec::new();
    let payload = SlicePayload::new(Some(parent), crate::serialize(&txs));
    let header = SliceHeader {
        slot,
        slice_index: SliceIndex::first(),
        is_last: true,
    };
    let slice = Slice::from_parts(header, payload);
    let shreds = RegularShredder::default()
        .shred(&slice, block_sk)
        .expect("shredding a valid slice cannot fail");
    let tree = DoubleMerkleTree::new(std::iter::once(shreds[0].slice_root()));
    (tree.get_root(), shreds.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The real cores finalize the block on every validator, and finalization
    /// takes at least one round-trip of vote exchange (never instantaneous).
    #[test]
    fn uniform_latency_finalizes_everywhere() {
        let one_way = Duration::from_millis(50);
        let config = LatencySimConfig::uniform(6, one_way);
        let result = simulate_slot_finalization(&config);

        assert!(result.all_finalized(), "every validator should finalize");
        // Fast finalization needs the leader's shreds to arrive (one hop) and
        // an 80%-stake round of notar votes to be gathered (another hop), so the
        // latency is at least two one-way delays.
        let max = result.max().expect("all finalized");
        assert!(
            max >= one_way * 2,
            "finalization at {max:?} is faster than two hops ({:?})",
            one_way * 2,
        );
    }

    /// Zero latency finalizes instantly; two-thirds-stake latency is no later
    /// than full-stake latency.
    #[test]
    fn stake_fraction_is_monotone() {
        let config = LatencySimConfig::uniform(11, Duration::from_millis(30));
        let result = simulate_slot_finalization(&config);

        let two_thirds = result
            .time_to_stake_fraction(0.67)
            .expect("two-thirds should finalize");
        let all = result.max().expect("all finalized");
        assert!(
            two_thirds <= all,
            "two-thirds-stake finalization ({two_thirds:?}) later than full ({all:?})",
        );
    }

    /// A validator far from everyone else finalizes strictly later than the
    /// well-connected majority — the engine reflects real per-node latency.
    #[test]
    fn distant_validator_finalizes_later() {
        let n = 6;
        let near = Duration::from_millis(20);
        let far = Duration::from_millis(400);
        // node 0 is far from everyone; the rest are near each other
        let latencies = (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| {
                        if i == j {
                            Duration::ZERO
                        } else if i == 0 || j == 0 {
                            far
                        } else {
                            near
                        }
                    })
                    .collect()
            })
            .collect();
        let config = LatencySimConfig {
            stakes: vec![Stake::new(1); n],
            latencies,
        };
        let result = simulate_slot_finalization(&config);

        assert!(result.all_finalized());
        let node0 = result.per_node()[0].unwrap();
        let others_max = result.per_node()[1..]
            .iter()
            .map(|t| t.unwrap())
            .max()
            .unwrap();
        assert!(
            node0 > others_max,
            "distant node finalized at {node0:?}, not after the rest ({others_max:?})",
        );
    }
}
