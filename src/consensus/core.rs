// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Synchronous consensus core state machine.
//!
//! [`ConsensusCore`] combines the [`BlockstoreImpl`], [`PoolImpl`] and
//! [`VotorState`] state machines (plus standstill detection) into a single
//! deterministic transition function: [`ConsensusCore::handle`] consumes an
//! [`Input`], advances the state, and appends the resulting [`Output`]s to a
//! buffer. It performs no I/O, holds no locks and never awaits; all networking
//! and crypto verification happens in the [`super::driver`] task and the
//! ingest tasks feeding it.
//!
//! What used to flow through channels between the blockstore, pool, Votor and
//! the standstill loop is now plain function calls inside
//! [`ConsensusCore::handle`], so event ordering is deterministic and the whole
//! consensus logic can be driven (and tested) without a tokio runtime.

use std::sync::Arc;
use std::time::Instant;

use log::{debug, trace, warn};
use tokio::sync::oneshot;

use super::blockstore::{BlockInfo, BlockstoreEvent, BlockstoreImpl};
use super::pool::{PoolEvent, PoolImpl, PoolOutbox};
use super::votor::VotorState;
use super::{
    AddVoteError, ConsensusMessage, DELTA_STANDSTILL, ValidatedCert, ValidatedVote,
    ValidatorEpochInfo,
};
use crate::crypto::aggsig;
use crate::crypto::merkle::BlockHash;
use crate::repair::{RepairRequest, RepairResponse};
use crate::shredder::{SliceCommitment, TOTAL_SHREDS, ValidatedShred};
use crate::types::{SliceIndex, SlicePayload};
use crate::{BlockId, Slot};

/// Inputs consumed by [`ConsensusCore::handle`].
///
/// Everything the consensus logic reacts to arrives as one of these,
/// pre-validated by the ingest tasks (signature and proof checks happen
/// *before* an input is constructed, so the core never verifies crypto).
#[derive(Debug)]
pub(crate) enum Input {
    /// A verified vote received from another validator.
    Vote(ValidatedVote),
    /// A verified certificate received from another validator.
    Cert(ValidatedCert),
    /// A verified shred received from the block dissemination protocol.
    DisseminatedShred(ValidatedShred),
    /// A verified shred received in a repair response for the given block.
    RepairedShred {
        block_hash: BlockHash,
        shred: ValidatedShred,
    },
    /// A slice of our own produced block (leader fast path).
    ///
    /// The core replies on `completed` with the reconstructed block's info
    /// once the last slice arrives (`None` before that); the block producer
    /// awaits this to pace block production.
    OwnSlice {
        payload: SlicePayload,
        shreds: Box<[ValidatedShred; TOTAL_SHREDS]>,
        completed: oneshot::Sender<Option<BlockInfo>>,
    },
    /// A repair request from a validated peer, answered from the blockstore.
    ///
    /// The core builds the response synchronously and sends it back on `reply`;
    /// the responder task then writes it to the requesting peer's socket. This
    /// mirrors [`Input::OwnSlice`] and keeps the responder socket owned by its
    /// task rather than split across the driver.
    RepairRequest {
        request: RepairRequest,
        reply: oneshot::Sender<RepairResponse>,
    },
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
    /// A commitment for this slice is now cached; the shred ingest edge can
    /// skip signature verification for further shreds of the same slice.
    SliceCommitment {
        slot: Slot,
        slice: SliceIndex,
        commitment: SliceCommitment,
    },
    /// The disseminated block for `slot` completed reconstruction.
    ///
    /// Observed by the block producer to detect a block in the previous slot.
    BlockDisseminated { slot: Slot, hash: BlockHash },
}

/// The consensus protocol as a synchronous state machine.
///
/// Owns the blockstore, the vote/cert pool and the voting logic outright —
/// no locks, no channels. Mutations enter exclusively through [`Self::handle`].
pub(crate) struct ConsensusCore {
    /// Blockstore holding shreds and reconstructed blocks.
    blockstore: BlockstoreImpl,
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
    /// Creates a new consensus core with an empty blockstore and pool and
    /// fresh voting state.
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
            blockstore: BlockstoreImpl::new(),
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
            Input::DisseminatedShred(shred) => {
                let slot = shred.payload().header.slot;
                let slice = shred.payload().header.slice_index;
                let _ = self.blockstore.add_shred_from_dissemination(shred);
                // Publish the commitment cached for this slice, if any, so the
                // ingest edge can skip verifying further shreds of the slice.
                // PERF: re-published per shred; the edge cache insert is cheap.
                if let Some(commitment) = self.blockstore.cached_commitment(slot, slice) {
                    out.push(Output::SliceCommitment {
                        slot,
                        slice,
                        commitment,
                    });
                }
                self.drain_blockstore(true, now, out);
            }
            Input::RepairedShred { block_hash, shred } => {
                let res = self
                    .blockstore
                    .add_shred_from_repair(block_hash.clone(), shred);
                if let Ok(Some(block_info)) = &res {
                    // trusted local invariant: repair stores under the requested hash
                    assert_eq!(block_info.hash, block_hash);
                    debug!("successfully repaired block {}", block_hash.short_hex());
                }
                self.drain_blockstore(false, now, out);
            }
            Input::OwnSlice {
                payload,
                shreds,
                completed,
            } => {
                let block_info = self.blockstore.add_own_slice(payload, shreds);
                // the block producer paces block production on this reply;
                // it may have shut down already, so a send error is fine
                let _ = completed.send(block_info);
                self.drain_blockstore(true, now, out);
            }
            Input::RepairRequest { request, reply } => {
                let response = request.build_response(&self.blockstore);
                // the responder task may have shut down; a send error is fine
                let _ = reply.send(response);
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

    /// Drains the blockstore's buffered events, registering completed blocks
    /// with the pool and feeding all events through Votor.
    ///
    /// `disseminated` says whether the triggering input came from the
    /// dissemination path (including own slices); only then is a completed
    /// block surfaced as [`Output::BlockDisseminated`].
    fn drain_blockstore(&mut self, disseminated: bool, now: Instant, out: &mut Vec<Output>) {
        for event in self.blockstore.take_events() {
            if let BlockstoreEvent::Block { slot, block_info } = &event {
                self.pool
                    .add_block((*slot, block_info.hash.clone()), block_info.parent.clone());
                if disseminated {
                    out.push(Output::BlockDisseminated {
                        slot: *slot,
                        hash: block_info.hash.clone(),
                    });
                }
            }
            self.votor.handle_blockstore_event(event);
        }
        self.drain_pool(now, out);
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
            // suppress repair for blocks we have already reconstructed; the
            // blockstore lives here now, so the repair loop no longer needs to
            // read it to make this check (as it used to in `repair_block`)
            if self.blockstore.get_block(&block_id).is_none() {
                out.push(Output::RequestRepair(block_id));
            }
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

    /// Read access to the owned blockstore, for tests and repair-serving assertions.
    #[cfg(test)]
    pub(crate) fn blockstore(&self) -> &BlockstoreImpl {
        &self.blockstore
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::super::{Cert, EpochInfo, Vote};
    use super::*;
    use crate::ValidatorIndex;
    use crate::crypto::aggsig::SecretKey;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::crypto::signature;
    use crate::repair::RepairRequestType;
    use crate::test_utils::{create_random_shredded_block, generate_validators};
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

    /// The blockstore now lives inside the core: feeding a full block's shreds
    /// via the dissemination path reconstructs it and surfaces the completion
    /// as an output (with a commitment cached for the ingest edge).
    #[test]
    fn disseminated_shreds_reconstruct_block_in_core() {
        let mut ctx = setup();
        let leader_sk = signature::SecretKey::new(&mut rand::rng());
        let slot = Slot::genesis().next();
        let (block_hash, _tree, shreds) = create_random_shredded_block(slot, 1, &leader_sk);

        let mut outputs = Vec::new();
        for shred in shreds.into_iter().flatten() {
            outputs.extend(ctx.handle(Input::DisseminatedShred(shred)));
        }

        assert!(
            outputs.iter().any(|o| matches!(
                o,
                Output::BlockDisseminated { slot: s, hash } if *s == slot && hash == &block_hash
            )),
            "expected a BlockDisseminated output, got {outputs:?}"
        );
        assert!(
            outputs
                .iter()
                .any(|o| matches!(o, Output::SliceCommitment { slot: s, .. } if *s == slot)),
            "expected a SliceCommitment output, got {outputs:?}"
        );
    }

    /// A repair request for a block we do not have is answered with a Nack,
    /// built from the core's blockstore and returned on the reply channel.
    #[tokio::test]
    async fn repair_request_for_unknown_block_nacks() {
        let mut ctx = setup();
        let req_type = RepairRequestType::LastSliceRoot((Slot::new(1), GENESIS_BLOCK_HASH));
        let request = RepairRequest::new_for_test(ValidatorIndex::new(1), req_type.clone());
        let (reply, reply_rx) = oneshot::channel();
        ctx.handle(Input::RepairRequest { request, reply });

        let response = reply_rx.await.expect("core should reply to repair request");
        assert!(matches!(response, RepairResponse::Nack(rt) if rt == req_type));
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
