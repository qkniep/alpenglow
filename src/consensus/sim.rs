// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Deterministic, single-threaded multi-node harness for [`ConsensusCore`].
//!
//! Because [`ConsensusCore`] is a pure state machine — inputs in, outputs out,
//! no I/O, no locks, and time supplied as a plain [`Instant`] argument — a whole
//! cluster of nodes can be driven synchronously, with no tokio runtime, no
//! sockets, and no wall-clock waits. Message delivery order and the clock are
//! chosen by the harness, so runs are reproducible and fast (the tests below
//! finalize a block chain and exercise timeout-driven skips in microseconds,
//! where the socket-based `tests/liveness.rs` needs seconds of real time).
//!
//! This is the payoff of the sans-IO refactor: the protocol's core logic can be
//! tested as the state machine the whitepaper describes, rather than through a
//! network of async tasks.

use std::collections::VecDeque;
use std::time::Instant;

use super::core::{ConsensusCore, Input, Output};
use super::{Cert, ConsensusMessage, EpochInfo, ValidatedCert, ValidatedVote, ValidatorEpochInfo};
use crate::crypto::merkle::{BlockHash, DoubleMerkleTree, GENESIS_BLOCK_HASH};
use crate::crypto::{aggsig, signature};
use crate::network::localhost_ip_sockaddr;
use crate::shredder::{RegularShredder, Shredder, ValidatedShred};
use crate::types::{Slice, SliceHeader, SliceIndex, SlicePayload};
use crate::{BlockId, Slot, Stake, Transaction, ValidatorIndex, ValidatorInfo};

/// A deterministic cluster of consensus cores sharing one validator set.
struct Sim {
    /// One consensus core per validator.
    nodes: Vec<ConsensusCore>,
    /// The shared validator set (used to validate messages between nodes).
    epoch_info: EpochInfo,
    /// Per-validator block-production (ed25519) keys, indexed by validator.
    block_sks: Vec<signature::SecretKey>,
    /// Highest finalized slot observed per node, from [`Output::Finalized`].
    finalized: Vec<Slot>,
    /// The harness-controlled clock handed to every [`ConsensusCore::handle`].
    now: Instant,
}

impl Sim {
    /// Builds a cluster of `n` equally-staked validators, each with a fresh core.
    fn new(n: u64) -> Self {
        let mut rng = rand::rng();
        let mut block_sks = Vec::new();
        let mut voting_sks = Vec::new();
        let mut validators = Vec::new();
        for id in 0..n {
            let block_sk = signature::SecretKey::new(&mut rng);
            let voting_sk = aggsig::SecretKey::new(&mut rng);
            validators.push(ValidatorInfo {
                id: ValidatorIndex::new(id),
                stake: Stake::new(1),
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
        let epoch_info = EpochInfo::new(validators);

        let now = Instant::now();
        let nodes = (0..n)
            .map(|id| {
                let vei = std::sync::Arc::new(ValidatorEpochInfo::new(
                    ValidatorIndex::new(id),
                    epoch_info.clone(),
                ));
                ConsensusCore::new(vei, voting_sks[id as usize].clone(), now)
            })
            .collect();

        Self {
            nodes,
            epoch_info,
            block_sks,
            finalized: vec![Slot::genesis(); n as usize],
            now,
        }
    }

    fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Feeds `input` to node `idx`, recording finalization and returning the
    /// consensus messages the node wants broadcast.
    fn handle(&mut self, idx: usize, input: Input) -> Vec<ConsensusMessage> {
        let mut out = Vec::new();
        self.nodes[idx].handle(input, self.now, &mut out);
        let mut broadcasts = Vec::new();
        for output in out {
            match output {
                Output::Broadcast(msg) => broadcasts.push(msg),
                Output::Finalized(slot) => {
                    self.finalized[idx] = self.finalized[idx].max(slot);
                }
                // With full connectivity and no loss, repair is never needed;
                // the remaining outputs are internal signals the harness doesn't
                // model (it drives block production itself).
                Output::RequestRepair(_)
                | Output::ParentReady { .. }
                | Output::BlockDisseminated { .. }
                | Output::SliceCommitment { .. } => {}
            }
        }
        broadcasts
    }

    /// Converts a broadcast message into an input for node `idx`, validating it
    /// against the shared validator set (as the real ingest path would).
    fn to_input(&self, msg: &ConsensusMessage) -> Option<Input> {
        match msg {
            ConsensusMessage::Vote(vote) => ValidatedVote::try_new(vote.clone(), &self.epoch_info)
                .ok()
                .map(Input::Vote),
            ConsensusMessage::Cert(cert) => ValidatedCert::try_new(cert.clone(), &self.epoch_info)
                .ok()
                .map(Input::Cert),
        }
    }

    /// Delivers `seed` messages to every node and keeps delivering whatever they
    /// broadcast until the cluster falls silent.
    ///
    /// Returns every message broadcast during the exchange (for assertions).
    fn deliver_until_quiescent(&mut self, seed: Vec<ConsensusMessage>) -> Vec<ConsensusMessage> {
        let mut queue: VecDeque<ConsensusMessage> = seed.clone().into();
        let mut seen = seed;
        while let Some(msg) = queue.pop_front() {
            for idx in 0..self.num_nodes() {
                let Some(input) = self.to_input(&msg) else {
                    continue;
                };
                for produced in self.handle(idx, input) {
                    seen.push(produced.clone());
                    queue.push_back(produced);
                }
            }
        }
        seen
    }

    /// Produces the leader's single-slice block for `slot` on top of `parent`,
    /// disseminates its shreds to every node, and runs the resulting
    /// vote/cert exchange to completion.
    ///
    /// Returns the produced block's id, to chain as the next slot's parent.
    fn produce_and_finalize(&mut self, slot: Slot, parent: BlockId) -> BlockId {
        let leader = self.epoch_info.leader(slot).id.as_usize();
        let (hash, shreds) = build_block(slot, parent, &self.block_sks[leader]);

        // Disseminate to every node (the leader included: reconstructing from
        // shreds and producing its own slice both yield the same block event).
        let mut seed = Vec::new();
        for idx in 0..self.num_nodes() {
            for shred in &shreds {
                seed.extend(self.handle(idx, Input::DisseminatedShred(shred.clone())));
            }
        }
        self.deliver_until_quiescent(seed);
        (slot, hash)
    }

    /// Advances the harness clock by `duration`.
    fn advance(&mut self, duration: std::time::Duration) {
        self.now += duration;
    }

    /// Fires all due timeouts on every node (as the driver's tick would) and
    /// runs the resulting exchange, returning every message broadcast.
    fn tick_all(&mut self) -> Vec<ConsensusMessage> {
        let mut seed = Vec::new();
        for idx in 0..self.num_nodes() {
            seed.extend(self.handle(idx, Input::Tick));
        }
        self.deliver_until_quiescent(seed)
    }
}

/// Builds a leader's single-slice block for `slot` on top of `parent`.
///
/// The block carries no transactions (consensus does not execute them), which
/// keeps it deterministic. Returns the block hash and its shreds.
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

    /// A chain of blocks disseminated to every node finalizes on all of them —
    /// driven entirely synchronously, with no tokio runtime or real time.
    #[test]
    fn cluster_finalizes_block_chain() {
        let n = 6;
        let mut sim = Sim::new(n);

        // Build a chain within the genesis leader window (slots 1..=3), each
        // block on the previous one, starting from genesis.
        let mut parent = (Slot::genesis(), GENESIS_BLOCK_HASH);
        let mut produced = Vec::new();
        for slot in [Slot::new(1), Slot::new(2), Slot::new(3)] {
            parent = sim.produce_and_finalize(slot, parent.clone());
            produced.push(parent.clone());
        }

        // Every node fast-finalizes the whole chain (100% notar → strong quorum).
        let tip_slot = produced.last().unwrap().0;
        for (idx, finalized) in sim.finalized.iter().enumerate() {
            assert!(
                *finalized >= tip_slot,
                "node {idx} finalized only up to {finalized}, expected >= {tip_slot}",
            );
        }
    }

    /// A silent leader is skipped: once the clock passes the voting timeout, a
    /// tick makes every node vote skip, and a skip certificate forms — all
    /// driven by the harness clock, no sleeping.
    #[test]
    fn silent_leader_is_skipped_after_timeout() {
        let n = 6;
        let mut sim = Sim::new(n);

        // No block is produced for the genesis window. Advance past the base
        // voting timeout (DELTA_TIMEOUT + slack) and fire the due timeouts.
        sim.advance(super::super::DELTA_TIMEOUT + super::super::DELTA_BLOCK * 5);
        let broadcasts = sim.tick_all();

        // The window's slots are skipped, and a skip certificate is produced.
        assert!(
            broadcasts
                .iter()
                .any(|msg| matches!(msg, ConsensusMessage::Cert(Cert::Skip(_)))),
            "expected a skip certificate to form, got {broadcasts:?}",
        );
    }
}
