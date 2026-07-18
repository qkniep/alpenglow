// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Main voting logic for the consensus protocol.
//!
//! Besides [`super::PoolImpl`], [`VotorState`] is the other main internal
//! component of Alpenglow. It handles the main voting decisions for the
//! consensus protocol. As input it receives events from [`super::PoolImpl`]
//! and [`super::Blockstore`], as well as its own internal timeout events.
//! It keeps its own internal state for each slot based on previous events and votes.
//!
//! [`VotorState`] is a pure, synchronous state machine: it performs no I/O,
//! tracks timeouts as deadlines instead of sleeping, and queues the votes it
//! decides to cast in an internal outbox. It is driven as part of
//! [`super::core::ConsensusCore`], whose driver task fires due timeouts and
//! broadcasts the queued votes over the wire.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};
use std::time::Instant;

use log::{debug, trace, warn};

use super::blockstore::{BlockInfo, BlockstoreEvent};
use super::pool::PoolEvent;
use super::{Cert, ConsensusMessage, DELTA_BLOCK, DELTA_TIMEOUT, Vote};
use crate::consensus::DELTA_FIRST_SLICE;
use crate::crypto::aggsig::SecretKey;
use crate::crypto::merkle::{BlockHash, GENESIS_BLOCK_HASH};
use crate::{BlockId, Slot, ValidatorIndex};

/// Votor's state machine: implements the decision process of which votes to cast.
///
/// It keeps some state for each slot and checks the conditions for voting.
///
/// This is a pure, synchronous state machine: it performs no I/O, tracks its
/// timeouts as deadlines (see [`Self::next_timeout`]) rather than sleeping, and
/// queues the votes and certificates it wants broadcast in an internal outbox,
/// drained via [`Self::take_broadcasts`].
pub(crate) struct VotorState {
    /// Per-slot voting state, keyed by slot.
    slots: BTreeMap<Slot, SlotState>,
    /// Highest slot for which we have seen a (slow) final or fast-final cert.
    ///
    /// This is *not* equivalent to e.g. [`super::PoolImpl::finalized_slot`],
    /// because we may have seen a (slow) final cert without a matching notar.
    /// We only use it to decide when our own vote for a slot no longer matters,
    /// at which point the per-slot state for earlier leader windows is pruned.
    highest_final_cert_slot: Slot,

    /// Own validator index.
    validator_index: ValidatorIndex,
    /// Secret key used to sign votes.
    voting_key: SecretKey,

    /// Pending timeout deadlines, earliest first.
    timeouts: BinaryHeap<Reverse<(Instant, VotorTimeout)>>,
    /// Consensus messages queued for (best-effort) broadcast,
    /// drained via [`Self::take_broadcasts`].
    broadcasts: Vec<ConsensusMessage>,
}

impl VotorState {
    /// Creates a new voting state machine with empty per-slot state.
    ///
    /// Timeouts for the genesis window are scheduled relative to `now`.
    pub(crate) fn new(
        validator_index: ValidatorIndex,
        voting_key: SecretKey,
        now: Instant,
    ) -> Self {
        // pre-populate the dummy genesis block's state
        let genesis_state = SlotState {
            voted: true,
            voted_notar: Some(GENESIS_BLOCK_HASH),
            block_notarized: Some(GENESIS_BLOCK_HASH),
            parents_ready: [(Slot::genesis(), GENESIS_BLOCK_HASH)]
                .into_iter()
                .collect(),
            retired: true,
            ..Default::default()
        };
        let slots = [(Slot::genesis(), genesis_state)].into_iter().collect();

        let mut state = Self {
            slots,
            highest_final_cert_slot: Slot::genesis(),
            validator_index,
            voting_key,
            timeouts: BinaryHeap::new(),
            broadcasts: Vec::new(),
        };
        state.set_timeouts(Slot::new(0), now);
        state
    }

    /// Returns `true` iff the given slot has been retired.
    fn is_retired(&self, slot: Slot) -> bool {
        self.slots.get(&slot).is_some_and(|s| s.retired)
    }

    /// Returns `true` iff we already voted notar or skip for the given slot.
    fn has_voted(&self, slot: Slot) -> bool {
        self.slots.get(&slot).is_some_and(|s| s.voted)
    }

    /// Returns `true` iff we received at least one shred for the given slot.
    fn received_shred(&self, slot: Slot) -> bool {
        self.slots.get(&slot).is_some_and(|s| s.received_shred)
    }

    /// Returns a mutable reference to the given slot's state.
    ///
    /// Inserts a default (empty) state if none exists yet.
    fn state_mut(&mut self, slot: Slot) -> &mut SlotState {
        self.slots.entry(slot).or_default()
    }

    /// First slot whose state is still retained, i.e. the start of the leader
    /// window containing [`Self::highest_final_cert_slot`].
    ///
    /// Everything below this has been (or will be) dropped by [`Self::prune`].
    fn first_unpruned_slot(&self) -> Slot {
        self.highest_final_cert_slot.first_slot_in_window()
    }

    /// Returns `true` iff this pool event is for a slot we no longer act on.
    ///
    /// For the most part, we should ignore events for slots that are `retired`
    /// or older than the window with the highest finalization certificate.
    ///
    /// However, this comes with exceptions based on the event type:
    /// - [`PoolEvent::Standstill`] is never ignored.
    ///   It carries a recovery bundle spanning multiple slots.
    ///   See also [`super::PoolImpl::recover_from_standstill`] for more info.
    ///   Simply gating based on [`Self::highest_final_cert_slot`] would not be correct.
    ///   It can run ahead of Pool's finalized slot (final cert vs. final + notar).
    ///   We could drop a bundle that Pool emitted precisely because it is stuck.
    /// - [`PoolEvent::CertCreated`] is not ignored for retired slots,
    ///   so we still broadcast notar/final/fast-final certs.
    fn should_ignore_pool_event(&self, event: &PoolEvent) -> bool {
        let slot = event.slot();
        match event {
            PoolEvent::Standstill { .. } => false,
            PoolEvent::CertCreated(_) => slot < self.first_unpruned_slot(),
            PoolEvent::ParentReady { .. }
            | PoolEvent::SafeToNotar(_)
            | PoolEvent::SafeToSkip(_) => {
                slot < self.first_unpruned_slot() || self.is_retired(slot)
            }
        }
    }

    pub(crate) fn handle_pool_event(&mut self, event: PoolEvent, now: Instant) {
        let slot = event.slot();
        if self.should_ignore_pool_event(&event) {
            trace!("ignoring pool event for old or retired slot {slot}");
            return;
        }
        trace!("votor pool event: {event:?}");
        match event {
            PoolEvent::ParentReady { slot, parent } => {
                let (parent_slot, parent_hash) = &parent;
                trace!(
                    "slot {slot} has new valid parent {} in slot {parent_slot}",
                    parent_hash.short_hex()
                );
                self.state_mut(slot).parents_ready.insert(parent);
                self.check_pending_blocks();
                self.set_timeouts(slot, now);
            }
            PoolEvent::SafeToNotar((slot, hash)) => {
                debug!("voted notar-fallback in slot {slot}");
                let vote =
                    Vote::new_notar_fallback(slot, hash, &self.voting_key, self.validator_index);
                self.enqueue_broadcast(vote);
                self.try_skip_window(slot);
                self.state_mut(slot).bad_window = true;
            }
            PoolEvent::SafeToSkip(slot) => {
                debug!("voted skip-fallback in slot {slot}");
                let vote = Vote::new_skip_fallback(slot, &self.voting_key, self.validator_index);
                self.enqueue_broadcast(vote);
                self.try_skip_window(slot);
                self.state_mut(slot).bad_window = true;
            }
            PoolEvent::CertCreated(cert) => self.handle_cert_created(cert, now),
            PoolEvent::Standstill(_, certs, votes) => {
                for cert in certs {
                    self.enqueue_broadcast(cert);
                }
                for vote in votes {
                    self.enqueue_broadcast(vote);
                }
            }
        }
    }

    /// Updates state based on a newly created certificate and re-broadcasts it.
    fn handle_cert_created(&mut self, cert: Cert, now: Instant) {
        match &cert {
            Cert::Notar(notar_cert) => {
                let hash = notar_cert.block_hash();
                // need to mark notarized BEFORE trying finalization
                self.state_mut(cert.slot()).block_notarized = Some(hash.clone());
                self.try_final(cert.slot(), hash);
            }
            Cert::Final(_) | Cert::FastFinal(_) => {
                // makes sure we eventually vote skip for these slots,
                // even if we never issued a ParentReady for this window
                self.set_timeouts(cert.slot().first_slot_in_window(), now);

                // Votor can already be pruned upon regular final cert,
                // whereas Pool would only be pruned upon actual finalization,
                // because that's when our vote for a slot no longer matters
                self.highest_final_cert_slot = self.highest_final_cert_slot.max(cert.slot());
                self.prune();
            }
            Cert::Skip(_) | Cert::NotarFallback(_) => {}
        }

        self.enqueue_broadcast(cert);
    }

    /// Queues a consensus message for broadcast by the driving task.
    ///
    /// Buffered rather than sent so this state machine stays free of I/O; the
    /// driver drains the queue via [`Self::take_broadcasts`] and performs the
    /// actual (best-effort) broadcast.
    fn enqueue_broadcast(&mut self, msg: impl Into<ConsensusMessage>) {
        self.broadcasts.push(msg.into());
    }

    /// Drains and returns the consensus messages queued for broadcast.
    pub(crate) fn take_broadcasts(&mut self) -> Vec<ConsensusMessage> {
        std::mem::take(&mut self.broadcasts)
    }

    pub(crate) fn handle_blockstore_event(&mut self, event: BlockstoreEvent) {
        let slot = event.slot();
        if slot <= self.highest_final_cert_slot || self.is_retired(slot) {
            trace!("ignoring blockstore event for old or retired slot {slot}");
            return;
        }
        trace!("votor blockstore event: {event:?}");
        match event {
            BlockstoreEvent::FirstShred(slot) => {
                self.state_mut(slot).received_shred = true;
            }
            BlockstoreEvent::InvalidBlock(slot) => {
                warn!("invalid block from leader for slot {slot}, skipping window");
                self.try_skip_window(slot);
            }
            BlockstoreEvent::Block { slot, block_info } => {
                if self.has_voted(slot) {
                    let h = block_info.hash.short_hex();
                    warn!("not voting for block {h} in slot {slot}, already voted");
                    return;
                }
                if self.try_notar(slot, block_info.clone()) {
                    self.check_pending_blocks();
                } else {
                    self.state_mut(slot).pending_block = Some(block_info);
                }
            }
        }
    }

    fn handle_timeout_event(&mut self, event: VotorTimeout) {
        let slot = event.slot();
        if slot <= self.highest_final_cert_slot || self.is_retired(slot) {
            trace!("ignoring timeout for old or retired slot {slot}");
            return;
        }
        trace!("votor timeout event: {event:?}");
        match event {
            VotorTimeout::Timeout(slot) => {
                trace!("timeout for slot {slot}");
                if !self.has_voted(slot) {
                    self.try_skip_window(slot);
                }
            }
            VotorTimeout::TimeoutCrashedLeader(slot) => {
                trace!("timeout (crashed leader) for slot {slot}");
                if !self.received_shred(slot) && !self.has_voted(slot) {
                    self.try_skip_window(slot);
                }
            }
        }
    }

    /// Fires all timeouts that are due at `now`.
    pub(crate) fn handle_due_timeouts(&mut self, now: Instant) {
        while let Some(Reverse((deadline, _))) = self.timeouts.peek() {
            if *deadline > now {
                break;
            }
            let Reverse((_, event)) = self.timeouts.pop().expect("peeked entry exists");
            self.handle_timeout_event(event);
        }
    }

    /// Returns the earliest pending timeout deadline, if any.
    pub(crate) fn next_timeout(&self) -> Option<Instant> {
        self.timeouts.peek().map(|Reverse((deadline, _))| *deadline)
    }

    /// Schedules timeouts for the leader window starting at the given `slot`.
    ///
    /// Deadlines are computed relative to `now`, mirroring the schedule the
    /// leader is expected to keep: the crashed-leader timeout fires after
    /// `DELTA_TIMEOUT + DELTA_FIRST_SLICE`, then one timeout per slot in the
    /// window, `DELTA_BLOCK` apart. They fire via [`Self::handle_due_timeouts`].
    ///
    /// # Panics
    ///
    /// Panics if `slot` is not the first slot of a window.
    fn set_timeouts(&mut self, slot: Slot, now: Instant) {
        assert!(slot.is_start_of_window());

        trace!(
            "setting timeouts for slots {slot}-{}",
            slot.last_slot_in_window()
        );
        let mut deadline = now + DELTA_TIMEOUT + DELTA_FIRST_SLICE;
        self.timeouts.push(Reverse((
            deadline,
            VotorTimeout::TimeoutCrashedLeader(slot),
        )));
        for s in slot.slots_in_window() {
            deadline += if s.is_start_of_window() {
                DELTA_BLOCK.saturating_sub(DELTA_FIRST_SLICE)
            } else {
                DELTA_BLOCK
            };
            self.timeouts
                .push(Reverse((deadline, VotorTimeout::Timeout(s))));
        }
    }

    /// Sends a notarization vote for the given block if the conditions are met.
    ///
    /// Returns `true` iff we decided to send a notarization vote for the block.
    fn try_notar(&mut self, slot: Slot, block_info: BlockInfo) -> bool {
        assert!(slot >= self.first_unpruned_slot());
        if self.has_voted(slot) {
            return false;
        }
        let BlockInfo { hash, parent } = block_info;
        let (parent_slot, parent_hash) = &parent;
        let first_slot_in_window = slot.first_slot_in_window();
        if slot == first_slot_in_window {
            let valid_parent = self
                .slots
                .get(&slot)
                .is_some_and(|s| s.parents_ready.contains(&parent));
            let h = parent_hash.short_hex();
            trace!(
                "try notar slot {slot} with parent {h} in slot {parent_slot} (valid {valid_parent})"
            );
            if !valid_parent {
                return false;
            }
        } else if *parent_slot != slot.prev()
            || self
                .slots
                .get(parent_slot)
                .and_then(|s| s.voted_notar.as_ref())
                != Some(parent_hash)
        {
            return false;
        }
        debug!("voted notar for slot {slot}");
        let vote = Vote::new_notar(slot, hash.clone(), &self.voting_key, self.validator_index);
        self.enqueue_broadcast(vote);
        let state = self.state_mut(slot);
        state.voted = true;
        state.voted_notar = Some(hash.clone());
        state.pending_block = None;
        self.try_final(slot, &hash);
        true
    }

    /// Sends a finalization vote for the given block if the conditions are met.
    fn try_final(&mut self, slot: Slot, hash: &BlockHash) {
        assert!(slot >= self.first_unpruned_slot());
        let state = self.slots.get(&slot);
        let notarized = state.and_then(|s| s.block_notarized.as_ref()) == Some(hash);
        let voted_notar = state.and_then(|s| s.voted_notar.as_ref()) == Some(hash);
        let not_bad = !state.is_some_and(|s| s.bad_window);
        if notarized && voted_notar && not_bad {
            let vote = Vote::new_final(slot, &self.voting_key, self.validator_index);
            self.enqueue_broadcast(vote);
            self.state_mut(slot).retired = true;
        }
    }

    /// Sends skip votes for all unvoted slots in the window that `slot` belongs to.
    fn try_skip_window(&mut self, slot: Slot) {
        assert!(slot >= self.first_unpruned_slot());
        trace!("try skip window of slot {slot}");
        for s in slot.slots_in_window() {
            if self.has_voted(s) {
                continue;
            }
            let state = self.state_mut(s);
            state.voted = true;
            state.bad_window = true;
            let vote = Vote::new_skip(s, &self.voting_key, self.validator_index);
            self.enqueue_broadcast(vote);
            debug!("voted skip for slot {s}");
        }
    }

    /// Checks if we can vote on any of the pending blocks by now.
    fn check_pending_blocks(&mut self) {
        let slots = self
            .slots
            .iter()
            .filter(|(_, s)| s.pending_block.is_some())
            .map(|(slot, _)| *slot)
            .collect::<Vec<_>>();
        for slot in slots {
            if let Some(block_info) = self.slots.get(&slot).and_then(|s| s.pending_block.clone()) {
                self.try_notar(slot, block_info);
            }
        }
    }

    /// Drops voting state for old slots that are no longer relevant.
    ///
    /// Afterwards, [`Self::slots`] only contains entries within or after the
    /// leader window of [`Self::highest_final_cert_slot`].
    fn prune(&mut self) {
        self.slots = self.slots.split_off(&self.first_unpruned_slot());
    }
}

/// Internal timeout events generated by [`VotorState`] itself.
///
/// Ordered so timeouts can serve as tie-breakers in the deadline heap.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum VotorTimeout {
    /// Regular timeout for the given slot has fired.
    Timeout(Slot),
    /// Early timeout for a crashed leader (nothing was received) has fired.
    TimeoutCrashedLeader(Slot),
}

impl VotorTimeout {
    /// Returns the slot this event refers to.
    const fn slot(&self) -> Slot {
        match self {
            Self::Timeout(slot) | Self::TimeoutCrashedLeader(slot) => *slot,
        }
    }
}

/// Per-slot voting state tracked by [`VotorState`].
#[derive(Default)]
struct SlotState {
    /// Whether we already voted notar or skip for this slot.
    voted: bool,
    /// The hash we voted notar for, if any.
    voted_notar: Option<BlockHash>,
    /// Whether the 'bad window' flag is set for this slot.
    bad_window: bool,
    /// Hash of the block with a notarization certificate (not notar-fallback).
    block_notarized: Option<BlockHash>,
    /// Valid parents for this slot, as `(parent_slot, parent_hash)` pairs.
    parents_ready: BTreeSet<BlockId>,
    /// Whether we received at least one shred for this slot.
    received_shred: bool,
    /// Block waiting for previous slots to be notarized.
    pending_block: Option<BlockInfo>,
    /// Whether Votor is done with this slot (`ItsOver` in the paper).
    retired: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consensus::EpochInfo;
    use crate::consensus::cert::{FinalCert, NotarCert};
    use crate::crypto::Hash;
    use crate::test_utils::{generate_validators, genesis_block_id, random_block_id};
    use crate::types::SLOTS_PER_WINDOW;

    struct TestContext {
        state: VotorState,
        /// The instant the state machine was constructed at; deadlines for the
        /// genesis window are relative to this.
        t0: Instant,
        epoch_info: EpochInfo,
        sks: Vec<SecretKey>,
    }

    fn setup() -> TestContext {
        let (sks, epoch_info) = generate_validators(2);
        let t0 = Instant::now();
        let state = VotorState::new(ValidatorIndex::new(0), sks[0].clone(), t0);
        TestContext {
            state,
            t0,
            epoch_info,
            sks,
        }
    }

    /// Drains the queued broadcasts and returns just the votes among them.
    fn drain_votes(state: &mut VotorState) -> Vec<Vote> {
        state
            .take_broadcasts()
            .into_iter()
            .filter_map(|msg| match msg {
                ConsensusMessage::Vote(v) => Some(v),
                ConsensusMessage::Cert(_) => None,
            })
            .collect()
    }

    impl TestContext {
        /// An instant by which every timeout of the genesis window has expired.
        fn after_genesis_window(&self) -> Instant {
            self.t0
                + DELTA_TIMEOUT
                + DELTA_FIRST_SLICE
                + DELTA_BLOCK * u32::try_from(SLOTS_PER_WINDOW).unwrap()
        }

        /// Feeds a reconstructed block and returns the resulting notar vote.
        fn send_block_and_expect_notar(&mut self, slot: Slot, parent: BlockId) -> Vote {
            self.state
                .handle_blockstore_event(BlockstoreEvent::FirstShred(slot));
            let block_info = BlockInfo {
                hash: Hash::random_for_test().into(),
                parent,
            };
            self.state
                .handle_blockstore_event(BlockstoreEvent::Block { slot, block_info });
            let votes = drain_votes(&mut self.state);
            assert_eq!(votes.len(), 1, "expected exactly one vote, got {votes:?}");
            let vote = votes.into_iter().next().unwrap();
            assert!(matches!(vote, Vote::Notar(_)));
            assert_eq!(vote.slot(), slot);
            vote
        }
    }

    /// Once all genesis-window deadlines expire, every non-genesis slot in the
    /// window gets a skip vote, in order.
    #[test]
    fn timeouts() {
        let mut ctx = setup();
        let deadline = ctx.state.next_timeout().expect("timeouts scheduled");
        assert!(deadline > ctx.t0);

        ctx.state.handle_due_timeouts(ctx.after_genesis_window());
        let votes = drain_votes(&mut ctx.state);

        // should vote skip for all slots except (retired) genesis
        let mut slots = Slot::genesis().slots_in_window().collect::<Vec<_>>();
        slots.remove(0);
        assert!(votes.iter().all(|v| matches!(v, Vote::Skip(_))));
        let skipped_slots = votes.iter().map(Vote::slot).collect::<Vec<_>>();
        assert_eq!(skipped_slots, slots);
    }

    #[test]
    fn notar_and_final() {
        let mut ctx = setup();
        let slot = Slot::genesis().next();

        // vote notar after seeing block
        let vote = ctx.send_block_and_expect_notar(slot, genesis_block_id());

        // vote finalize after seeing branch-certified
        let Vote::Notar(notar_vote) = vote else {
            unreachable!()
        };
        let cert = Cert::Notar(NotarCert::new(&[notar_vote], ctx.epoch_info.validators()));
        ctx.state
            .handle_pool_event(PoolEvent::CertCreated(cert), ctx.t0);
        let votes = drain_votes(&mut ctx.state);
        assert!(
            votes
                .iter()
                .any(|v| matches!(v, Vote::Final(_)) && v.slot() == slot),
            "expected a final vote for slot {slot}, got {votes:?}"
        );
    }

    #[test]
    fn notar_out_of_order() {
        let mut ctx = setup();
        let (slot1, hash1) = (Slot::genesis().next(), Hash::random_for_test());
        let (slot2, hash2) = (slot1.next(), Hash::random_for_test());

        // give later block to votor first: no vote yet
        ctx.state
            .handle_blockstore_event(BlockstoreEvent::FirstShred(slot2));
        let block_info = BlockInfo {
            hash: hash2.into(),
            parent: (slot1, hash1.clone().into()),
        };
        ctx.state.handle_blockstore_event(BlockstoreEvent::Block {
            slot: slot2,
            block_info,
        });
        assert!(ctx.state.take_broadcasts().is_empty());

        // now notify votor of earlier block: both blocks get notarized
        ctx.state
            .handle_blockstore_event(BlockstoreEvent::FirstShred(slot1));
        let block_info = BlockInfo {
            hash: hash1.into(),
            parent: genesis_block_id(),
        };
        ctx.state.handle_blockstore_event(BlockstoreEvent::Block {
            slot: slot1,
            block_info,
        });
        let votes = drain_votes(&mut ctx.state);
        assert_eq!(votes.len(), 2, "expected two notar votes, got {votes:?}");
        assert!(votes.iter().all(|v| matches!(v, Vote::Notar(_))));
        assert!(votes.iter().any(|v| v.slot() == slot1));
        assert!(votes.iter().any(|v| v.slot() == slot2));
    }

    #[test]
    fn pending_block_not_notarized_after_skip() {
        let mut ctx = setup();

        // first slot of the second leader window; its parent is not ready yet
        let slot = Slot::new(SLOTS_PER_WINDOW);
        assert!(slot.is_start_of_window());
        let parent = (slot.prev(), Hash::random_for_test().into());

        // block reconstructs before its parent is ready:
        // stashed as pending, no vote yet (parent not in `parents_ready`)
        let block_info = BlockInfo {
            hash: Hash::random_for_test().into(),
            parent: parent.clone(),
        };
        ctx.state
            .handle_blockstore_event(BlockstoreEvent::Block { slot, block_info });

        // window times out: we vote skip for every slot in the window
        ctx.state.handle_timeout_event(VotorTimeout::Timeout(slot));

        // parent becomes ready late: re-checks pending blocks
        ctx.state
            .handle_pool_event(PoolEvent::ParentReady { slot, parent }, ctx.t0);

        let votes_for_slot = drain_votes(&mut ctx.state)
            .into_iter()
            .filter(|v| v.slot() == slot)
            .collect::<Vec<_>>();

        // must not notarize `slot`, which we already voted skip for
        assert!(
            votes_for_slot.iter().any(|v| matches!(v, Vote::Skip(_))),
            "expected a skip vote for slot {slot}",
        );
        assert!(
            !votes_for_slot.iter().any(|v| matches!(v, Vote::Notar(_))),
            "slot {slot} notarized after voting skip (slashable skip-and-notarize)",
        );
    }

    #[test]
    fn safe_to_notar() {
        let mut ctx = setup();
        let slot = Slot::genesis().next();

        // window times out: skip votes for the non-genesis slots
        ctx.state.handle_due_timeouts(ctx.after_genesis_window());
        let votes = drain_votes(&mut ctx.state);
        assert!(votes.iter().all(|v| matches!(v, Vote::Skip(_))));

        // vote notar-fallback after safe-to-notar
        let block = random_block_id(slot);
        ctx.state
            .handle_pool_event(PoolEvent::SafeToNotar(block.clone()), ctx.t0);
        let votes = drain_votes(&mut ctx.state);
        assert_eq!(votes.len(), 1, "expected one vote, got {votes:?}");
        assert!(matches!(votes[0], Vote::NotarFallback(_)));
        assert_eq!(votes[0].slot(), block.0);
        assert_eq!(votes[0].block_hash(), Some(&block.1));
    }

    #[test]
    fn safe_to_skip() {
        let mut ctx = setup();
        let slot = Slot::genesis().next();

        // vote notar after seeing block
        ctx.send_block_and_expect_notar(slot, genesis_block_id());

        // vote skip-fallback after safe-to-skip
        ctx.state
            .handle_pool_event(PoolEvent::SafeToSkip(slot), ctx.t0);
        let votes = drain_votes(&mut ctx.state);
        assert!(
            matches!(votes[0], Vote::SkipFallback(_)) && votes[0].slot() == slot,
            "expected a skip-fallback vote for slot {slot}, got {votes:?}"
        );
    }

    #[test]
    fn prunes_to_finalized_window() {
        let mut ctx = setup();

        // finalize a slot that is NOT first in its window and isn't in the genesis window
        let finalized = Slot::new(SLOTS_PER_WINDOW + 1);
        let window_start = finalized.first_slot_in_window();
        assert!(window_start > Slot::genesis());
        assert!(window_start < finalized);

        // populate per-slot state across the previous window and into the next one
        let highest = Slot::new(2 * SLOTS_PER_WINDOW);
        for i in 1..=highest.inner() {
            let event = BlockstoreEvent::FirstShred(Slot::new(i));
            ctx.state.handle_blockstore_event(event);
        }
        assert!((0..=highest.inner()).all(|i| ctx.state.slots.contains_key(&Slot::new(i))));

        // finalizing a mid-window slot should drop only the slots before its window
        let Vote::Final(final_vote) =
            Vote::new_final(finalized, &ctx.sks[1], ValidatorIndex::new(1))
        else {
            unreachable!()
        };
        let cert = Cert::Final(FinalCert::new(&[final_vote], ctx.epoch_info.validators()));
        ctx.state
            .handle_pool_event(PoolEvent::CertCreated(cert), ctx.t0);
        assert_eq!(ctx.state.highest_final_cert_slot, finalized);

        // the whole finalized window is kept
        assert!(ctx.state.slots.keys().all(|s| *s >= window_start));
        for slot in window_start.slots_in_window() {
            assert!(
                ctx.state.slots.contains_key(&slot),
                "slot {slot} in finalized window should be retained",
            );
        }

        // earlier windows are dropped
        assert!(!ctx.state.slots.contains_key(&Slot::genesis()));
        assert!(!ctx.state.slots.contains_key(&window_start.prev()));
    }
}
