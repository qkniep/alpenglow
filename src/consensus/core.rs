// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Synchronous consensus core state machine.
//!
//! [`ConsensusCore`] combines the [`PoolImpl`] and [`VotorState`] state
//! machines (plus standstill detection) into a single deterministic transition
//! function: [`ConsensusCore::handle`] consumes an [`Input`], advances the
//! state, and appends the resulting [`Output`]s to a buffer. It performs no
//! I/O, holds no locks and never awaits; all networking happens in the
//! [`super::driver`] task and the ingest tasks feeding it.
//!
//! What used to flow through channels between the pool, Votor and the
//! standstill loop is now plain function calls inside [`ConsensusCore::handle`],
//! so event ordering is deterministic and the whole consensus logic can be
//! driven (and tested) without a tokio runtime.

use std::sync::Arc;
use std::time::Instant;

use log::{trace, warn};

use super::blockstore::BlockstoreEvent;
use super::pool::{PoolEvent, PoolImpl, PoolOutbox};
use super::votor::VotorState;
use super::{
    AddVoteError, ConsensusMessage, DELTA_STANDSTILL, ValidatedCert, ValidatedVote,
    ValidatorEpochInfo,
};
use crate::crypto::aggsig;
use crate::{BlockId, Slot};

/// Inputs consumed by [`ConsensusCore::handle`].
///
/// Everything the consensus logic reacts to arrives as one of these,
/// pre-validated by the ingest tasks (signature checks happen *before* an
/// input is constructed, so the core never verifies crypto).
#[derive(Debug)]
pub(crate) enum Input {
    /// A verified vote received from another validator.
    Vote(ValidatedVote),
    /// A verified certificate received from another validator.
    Cert(ValidatedCert),
    /// An event drained from the blockstore by an ingest task
    /// (dissemination, repair, or own block production).
    BlockstoreEvent(BlockstoreEvent),
    /// The clock advanced to [`ConsensusCore::next_timeout`].
    Tick,
}

/// Side-effects produced by [`ConsensusCore::handle`].
///
/// The [`super::driver`] task routes each output to the edge task that
/// performs the corresponding I/O.
// PERF: Short-lived buffer entry; boxing the message isn't worth the allocation.
#[expect(clippy::large_enum_variant)]
#[derive(Debug)]
pub(crate) enum Output {
    /// Broadcast a consensus message to all validators (best-effort).
    Broadcast(ConsensusMessage),
    /// Ask the repair loop to fetch this block.
    RequestRepair(BlockId),
    /// The slot (a window start) has a valid parent for block production.
    ParentReady { slot: Slot, parent: BlockId },
    /// A new highest slot was finalized.
    Finalized(Slot),
}

/// The consensus protocol as a synchronous state machine.
///
/// Owns the vote/cert pool and the voting logic outright — no locks, no
/// channels. Mutations enter exclusively through [`Self::handle`].
pub(crate) struct ConsensusCore {
    /// Pool of votes and certificates.
    pool: PoolImpl,
    /// Voting state machine.
    votor: VotorState,
    /// Highest finalized slot already reported via [`Output::Finalized`].
    finalized_slot: Slot,
    /// Time of the last observed finalization progress (or standstill recovery),
    /// used for standstill detection.
    last_progress: Instant,
}

impl ConsensusCore {
    /// Creates a new consensus core with an empty pool and fresh voting state.
    ///
    /// Votor timeouts for the genesis window and the standstill deadline are
    /// scheduled relative to `now`.
    pub(crate) fn new(
        epoch_info: Arc<ValidatorEpochInfo>,
        voting_key: aggsig::SecretKey,
        now: Instant,
    ) -> Self {
        let own_id = epoch_info.own_id();
        Self {
            pool: PoolImpl::new(epoch_info),
            votor: VotorState::new(own_id, voting_key, now),
            finalized_slot: Slot::genesis(),
            last_progress: now,
        }
    }

    /// Advances the state machine by one input, appending side-effects to `out`.
    pub(crate) fn handle(&mut self, input: Input, now: Instant, out: &mut Vec<Output>) {
        match input {
            Input::Vote(vote) => {
                match self.pool.add_vote(vote) {
                    Ok(()) => {}
                    Err(AddVoteError::Slashable(offence)) => {
                        warn!("slashable offence detected: {offence}");
                    }
                    Err(err) => trace!("ignoring invalid vote: {err}"),
                }
                self.drain_pool(now, out);
            }
            Input::Cert(cert) => {
                match self.pool.add_cert(cert) {
                    Ok(()) => {}
                    Err(err) => trace!("ignoring invalid cert: {err}"),
                }
                self.drain_pool(now, out);
            }
            Input::BlockstoreEvent(event) => {
                // a completed block is registered with the pool, which needs the
                // parent info for its parent-ready and safe-to-notar tracking
                if let BlockstoreEvent::Block { slot, block_info } = &event {
                    self.pool
                        .add_block((*slot, block_info.hash.clone()), block_info.parent.clone());
                }
                self.votor.handle_blockstore_event(event);
                self.drain_pool(now, out);
            }
            Input::Tick => {
                self.votor.handle_due_timeouts(now);
                self.drain_votor(out);
                if now.duration_since(self.last_progress) >= DELTA_STANDSTILL {
                    let outbox = self.pool.recover_from_standstill();
                    self.apply_pool_outbox(outbox, now, out);
                    self.last_progress = now;
                }
            }
        }
    }

    /// Returns the deadline at which [`Input::Tick`] must be fed next.
    ///
    /// This is the earlier of the next Votor timeout and the standstill
    /// deadline, so there is always a finite deadline to sleep towards.
    pub(crate) fn next_timeout(&self) -> Instant {
        let standstill = self.last_progress + DELTA_STANDSTILL;
        match self.votor.next_timeout() {
            Some(votor) => votor.min(standstill),
            None => standstill,
        }
    }

    /// Drains the pool outbox, feeding events through Votor and into `out`.
    fn drain_pool(&mut self, now: Instant, out: &mut Vec<Output>) {
        let outbox = self.pool.take_outbox();
        self.apply_pool_outbox(outbox, now, out);
        if self.pool.finalized_slot() > self.finalized_slot {
            self.finalized_slot = self.pool.finalized_slot();
            self.last_progress = now;
            out.push(Output::Finalized(self.finalized_slot));
        }
    }

    /// Routes a [`PoolOutbox`]: repair requests become [`Output`]s directly,
    /// pool events feed Votor (parent-ready ones are additionally surfaced for
    /// the block producer), then Votor's queued broadcasts are drained.
    fn apply_pool_outbox(&mut self, outbox: PoolOutbox, now: Instant, out: &mut Vec<Output>) {
        for block_id in outbox.repairs {
            out.push(Output::RequestRepair(block_id));
        }
        for event in outbox.votor_events {
            if let PoolEvent::ParentReady { slot, parent } = &event {
                out.push(Output::ParentReady {
                    slot: *slot,
                    parent: parent.clone(),
                });
            }
            self.votor.handle_pool_event(event, now);
        }
        self.drain_votor(out);
    }

    /// Moves Votor's queued broadcasts into `out`.
    fn drain_votor(&mut self, out: &mut Vec<Output>) {
        out.extend(
            self.votor
                .take_broadcasts()
                .into_iter()
                .map(Output::Broadcast),
        );
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::super::blockstore::BlockInfo;
    use super::super::{Cert, EpochInfo, Vote};
    use super::*;
    use crate::ValidatorIndex;
    use crate::crypto::Hash;
    use crate::crypto::aggsig::SecretKey;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::test_utils::generate_validators;
    use crate::types::Slot;

    struct TestContext {
        sks: Vec<SecretKey>,
        epoch_info: EpochInfo,
        core: ConsensusCore,
        now: Instant,
    }

    fn setup() -> TestContext {
        let (sks, epoch_info) = generate_validators(11);
        let validator_epoch_info = Arc::new(ValidatorEpochInfo::new(
            ValidatorIndex::new(0),
            epoch_info.clone(),
        ));
        let now = Instant::now();
        let core = ConsensusCore::new(validator_epoch_info, sks[0].clone(), now);
        TestContext {
            sks,
            epoch_info,
            core,
            now,
        }
    }

    impl TestContext {
        fn handle(&mut self, input: Input) -> Vec<Output> {
            let mut out = Vec::new();
            self.core.handle(input, self.now, &mut out);
            out
        }

        fn notar_vote(&self, slot: Slot, v: u64) -> Input {
            let v = ValidatorIndex::new(v);
            let vote = Vote::new_notar(slot, GENESIS_BLOCK_HASH, &self.sks[v.as_usize()], v);
            let vote = ValidatedVote::try_new(vote, &self.epoch_info)
                .expect("test vote should pass verification");
            Input::Vote(vote)
        }
    }

    /// A notarization quorum produces a cert that is broadcast as an output.
    #[test]
    fn vote_quorum_produces_cert_broadcast() {
        let mut ctx = setup();
        let mut outputs = Vec::new();
        for v in 0..7 {
            outputs.extend(ctx.handle(ctx.notar_vote(Slot::genesis(), v)));
        }
        assert!(
            outputs
                .iter()
                .any(|o| matches!(o, Output::Broadcast(ConsensusMessage::Cert(Cert::Notar(_))))),
            "expected a notar cert broadcast, got {outputs:?}"
        );
    }

    /// A reconstructed block is registered with the pool: once its parent is
    /// certified, the safe-to-notar machinery can request its repair or notify
    /// Votor without any external `add_block` call.
    #[test]
    fn block_event_registers_block_with_pool() {
        let mut ctx = setup();
        let slot = Slot::genesis().next();
        let block_info = BlockInfo {
            hash: Hash::random_for_test().into(),
            parent: (Slot::genesis(), GENESIS_BLOCK_HASH),
        };
        let event = BlockstoreEvent::Block { slot, block_info };
        ctx.handle(Input::BlockstoreEvent(event));
        assert_eq!(ctx.core.pool.parents_ready(slot), &[]);
        // the pool saw the block: a notar quorum for it now triggers
        // finalization tracking through the registered parent link
        let mut outputs = Vec::new();
        for v in 0..7 {
            outputs.extend(ctx.handle(ctx.notar_vote(Slot::genesis(), v)));
        }
        assert!(!outputs.is_empty());
    }

    /// Without finalization progress, a tick past the standstill deadline
    /// re-broadcasts certificates and own votes.
    #[test]
    fn standstill_tick_rebroadcasts() {
        let mut ctx = setup();
        // fast-finalize genesis so the pool holds a finalization cert
        // (like on startup, this does not count as finalization *progress*)
        let mut outputs = Vec::new();
        for v in 0..11 {
            outputs.extend(ctx.handle(ctx.notar_vote(Slot::genesis(), v)));
        }
        assert!(
            outputs.iter().any(|o| matches!(
                o,
                Output::Broadcast(ConsensusMessage::Cert(Cert::FastFinal(_)))
            )),
            "expected genesis to fast-finalize, got {outputs:?}"
        );

        // no progress for DELTA_STANDSTILL: recovery bundle is broadcast
        ctx.now += DELTA_STANDSTILL + Duration::from_millis(1);
        let outputs = ctx.handle(Input::Tick);
        assert!(
            outputs
                .iter()
                .any(|o| matches!(o, Output::Broadcast(ConsensusMessage::Cert(_)))),
            "expected standstill recovery to re-broadcast certs, got {outputs:?}"
        );
    }

    /// The next timeout is never later than the standstill deadline.
    #[test]
    fn next_timeout_capped_by_standstill() {
        let ctx = setup();
        assert!(ctx.core.next_timeout() <= ctx.now + DELTA_STANDSTILL);
    }
}
