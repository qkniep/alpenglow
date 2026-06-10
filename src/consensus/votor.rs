// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Main voting logic for the consensus protocol.
//!
//! Besides [`super::Pool`], [`Votor`] is the other main internal component Alpenglow.
//! It handles the main voting decisions for the consensus protocol.
//! As input it receives events from [`super::Pool`] (on a [`PoolEvent`] channel),
//! from [`super::Blockstore`] (on a [`BlockstoreEvent`] channel),
//! and its own internal timeout events.
//! Votor keeps its own internal state for each slot based on previous events and votes.
//!
//! Votor has access to an instance of [`All2All`] for broadcasting votes.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use anyhow::Result;
use log::{debug, trace, warn};
use tokio::sync::mpsc::{Receiver, Sender};

use super::blockstore::{BlockInfo, BlockstoreEvent};
use super::pool::PoolEvent;
use super::{Cert, ConsensusMessage, DELTA_BLOCK, DELTA_TIMEOUT, Vote};
use crate::consensus::DELTA_FIRST_SLICE;
use crate::crypto::aggsig::SecretKey;
use crate::crypto::merkle::{BlockHash, GENESIS_BLOCK_HASH};
use crate::{All2All, BlockId, Slot, ValidatorIndex};

/// Votor implements the decision process of which votes to cast.
///
/// It keeps some state for each slot and checks the conditions for voting.
pub struct Votor<A: All2All> {
    /// Per-slot voting state, keyed by slot.
    slots: BTreeMap<Slot, SlotState>,
    /// Highest slot for which we have seen a (slow) final or fast-final cert.
    ///
    /// This is *not* equivalent to e.g. [`super::Pool::finalized_slot`],
    /// because we may have seen a (slow) final cert without a matching notar.
    /// We only use it to decide when our own vote for a slot no longer matters,
    /// at which point the per-slot state for earlier leader windows is pruned.
    highest_final_cert_slot: Slot,

    /// Own validator index.
    validator_index: ValidatorIndex,
    /// Secret key used to sign votes.
    voting_key: SecretKey,

    /// Channel for receiving events from Pool.
    pool_receiver: Receiver<PoolEvent>,
    /// Channel for receiving events from Blockstore.
    blockstore_receiver: Receiver<BlockstoreEvent>,
    /// Channel for receiving internal timeout events.
    timeout_receiver: Receiver<VotorTimeout>,
    /// Sender side of the timeout channel. Used for scheduling timeouts.
    timeout_sender: Sender<VotorTimeout>,
    /// [`All2All`] instance used to broadcast votes.
    all2all: Arc<A>,
}

impl<A: All2All> Votor<A> {
    /// Creates a new Votor instance with empty state.
    ///
    /// On `pool_receiver` and `blockstore_receiver`, it receives events from
    /// [`super::Pool`] and [`super::Blockstore`] respectively.
    /// Informed by these events Votor updates its state and generates votes.
    /// Votes are signed with `voting_key` and broadcast using `all2all`.
    pub fn new(
        validator_index: ValidatorIndex,
        voting_key: SecretKey,
        pool_receiver: Receiver<PoolEvent>,
        blockstore_receiver: Receiver<BlockstoreEvent>,
        all2all: Arc<A>,
    ) -> Self {
        let (timeout_sender, timeout_receiver) = tokio::sync::mpsc::channel(256);

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

        let votor = Self {
            slots,
            highest_final_cert_slot: Slot::genesis(),
            validator_index,
            voting_key,
            pool_receiver,
            blockstore_receiver,
            timeout_receiver,
            timeout_sender,
            all2all,
        };
        votor.set_timeouts(Slot::new(0));
        votor
    }

    /// Handles the voting (leader and non-leader) side of consensus protocol.
    ///
    /// Checks consensus conditions and broadcasts new votes.
    #[fastrace::trace]
    pub async fn voting_loop(&mut self) -> Result<()> {
        loop {
            tokio::select! {
                Some(event) = self.pool_receiver.recv() => self.handle_pool_event(event).await,
                Some(event) = self.blockstore_receiver.recv() => self.handle_blockstore_event(event).await,
                Some(event) = self.timeout_receiver.recv() => self.handle_timeout_event(event).await,
                else => break,
            }
        }

        Ok(())
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
    ///   See also [`super::Pool::recover_from_standstill`] for more info.
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

    async fn handle_pool_event(&mut self, event: PoolEvent) {
        let slot = event.slot();
        if self.should_ignore_pool_event(&event) {
            trace!("ignoring pool event for old or retired slot {slot}");
            return;
        }
        trace!("votor pool event: {event:?}");
        match event {
            PoolEvent::ParentReady { slot, parent } => {
                let (parent_slot, parent_hash) = &parent;
                let h = parent_hash.short_hex();
                trace!("slot {slot} has new valid parent {h} in slot {parent_slot}");
                self.state_mut(slot).parents_ready.insert(parent);
                self.check_pending_blocks().await;
                self.set_timeouts(slot);
            }
            PoolEvent::SafeToNotar((slot, hash)) => {
                debug!("voted notar-fallback in slot {slot}");
                let vote =
                    Vote::new_notar_fallback(slot, hash, &self.voting_key, self.validator_index);
                self.all2all.broadcast(&vote.into()).await.unwrap();
                self.try_skip_window(slot).await;
                self.state_mut(slot).bad_window = true;
            }
            PoolEvent::SafeToSkip(slot) => {
                debug!("voted skip-fallback in slot {slot}");
                let vote = Vote::new_skip_fallback(slot, &self.voting_key, self.validator_index);
                self.all2all.broadcast(&vote.into()).await.unwrap();
                self.try_skip_window(slot).await;
                self.state_mut(slot).bad_window = true;
            }
            PoolEvent::CertCreated(cert) => self.handle_cert_created(cert).await,
            PoolEvent::Standstill(_, certs, votes) => {
                for cert in certs {
                    self.all2all.broadcast(&cert.into()).await.unwrap();
                }
                for vote in votes {
                    self.all2all.broadcast(&vote.into()).await.unwrap();
                }
            }
        }
    }

    /// Updates state based on a newly created certificate and re-broadcasts it.
    async fn handle_cert_created(&mut self, cert: Box<Cert>) {
        match cert.as_ref() {
            Cert::Notar(_) => {
                let hash = cert.block_hash().unwrap();
                // need to mark notarized BEFORE trying finalization
                self.state_mut(cert.slot()).block_notarized = Some(hash.clone());
                self.try_final(cert.slot(), hash).await;
            }
            Cert::Final(_) | Cert::FastFinal(_) => {
                // makes sure we eventually vote skip for these slots,
                // even if we never issued a ParentReady for this window
                self.set_timeouts(cert.slot().first_slot_in_window());

                // Votor can already be pruned upon regular final cert,
                // whereas Pool would only be pruned upon actual finalization,
                // because that's when our vote for a slot no longer matters
                self.highest_final_cert_slot = self.highest_final_cert_slot.max(cert.slot());
                self.prune();
            }
            _ => {}
        }
        let message = ConsensusMessage::from(*cert);
        self.all2all.broadcast(&message).await.unwrap();
    }

    async fn handle_blockstore_event(&mut self, event: BlockstoreEvent) {
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
                self.try_skip_window(slot).await;
            }
            BlockstoreEvent::Block { slot, block_info } => {
                if self.has_voted(slot) {
                    let h = block_info.hash.short_hex();
                    warn!("not voting for block {h} in slot {slot}, already voted");
                    return;
                }
                if self.try_notar(slot, block_info.clone()).await {
                    self.check_pending_blocks().await;
                } else {
                    self.state_mut(slot).pending_block = Some(block_info);
                    self.pending_block_slots.insert(slot);
                }
            }
        }
    }

    async fn handle_timeout_event(&mut self, event: VotorTimeout) {
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
                    self.try_skip_window(slot).await;
                }
            }
            VotorTimeout::TimeoutCrashedLeader(slot) => {
                trace!("timeout (crashed leader) for slot {slot}");
                if !self.received_shred(slot) && !self.has_voted(slot) {
                    self.try_skip_window(slot).await;
                }
            }
        }
    }

    /// Sets timeouts for the leader window starting at the given `slot`.
    ///
    /// # Panics
    ///
    /// Panics if `slot` is not the first slot of a window.
    fn set_timeouts(&self, slot: Slot) {
        assert!(slot.is_start_of_window());

        trace!(
            "setting timeouts for slots {slot}-{}",
            slot.last_slot_in_window()
        );
        let sender = self.timeout_sender.clone();
        tokio::spawn(async move {
            tokio::time::sleep(DELTA_TIMEOUT + DELTA_FIRST_SLICE).await;
            // HACK: ignoring errors to prevent panic when shutting down votor
            let _ = sender.send(VotorTimeout::TimeoutCrashedLeader(slot)).await;
            for s in slot.slots_in_window() {
                if s.is_start_of_window() {
                    tokio::time::sleep(DELTA_BLOCK - DELTA_FIRST_SLICE).await;
                } else {
                    tokio::time::sleep(DELTA_BLOCK).await;
                }
                let _ = sender.send(VotorTimeout::Timeout(s)).await;
            }
        });
    }

    /// Sends a notarization vote for the given block if the conditions are met.
    ///
    /// Returns `true` iff we decided to send a notarization vote for the block.
    async fn try_notar(&mut self, slot: Slot, block_info: BlockInfo) -> bool {
        assert!(slot >= self.first_unpruned_slot());
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
        self.all2all.broadcast(&vote.into()).await.unwrap();
        let state = self.state_mut(slot);
        state.voted = true;
        state.voted_notar = Some(hash.clone());
        state.pending_block = None;
        self.try_final(slot, &hash).await;
        true
    }

    /// Sends a finalization vote for the given block if the conditions are met.
    async fn try_final(&mut self, slot: Slot, hash: &BlockHash) {
        assert!(slot >= self.first_unpruned_slot());
        let state = self.slots.get(&slot);
        let notarized = state.and_then(|s| s.block_notarized.as_ref()) == Some(hash);
        let voted_notar = state.and_then(|s| s.voted_notar.as_ref()) == Some(hash);
        let not_bad = !state.is_some_and(|s| s.bad_window);
        if notarized && voted_notar && not_bad {
            let vote = Vote::new_final(slot, &self.voting_key, self.validator_index);
            self.all2all.broadcast(&vote.into()).await.unwrap();
            self.state_mut(slot).retired = true;
        }
    }

    /// Sends skip votes for all unvoted slots in the window that `slot` belongs to.
    async fn try_skip_window(&mut self, slot: Slot) {
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
            self.all2all.broadcast(&vote.into()).await.unwrap();
            debug!("voted skip for slot {s}");
        }
    }

    /// Checks if we can vote on any of the pending blocks by now.
    async fn check_pending_blocks(&mut self) {
        let slots = self
            .slots
            .iter()
            .filter(|(_, s)| s.pending_block.is_some())
            .map(|(slot, _)| *slot)
            .collect::<Vec<_>>();
        for slot in slots {
            if let Some(block_info) = self.slots.get(&slot).and_then(|s| s.pending_block.clone()) {
                self.try_notar(slot, block_info).await;
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

/// Internal timeout events generated by [`Votor`] itself.
#[derive(Debug)]
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

/// Per-slot voting state tracked by [`Votor`].
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
    use std::time::Duration;

    use tokio::sync::mpsc;

    use super::*;
    use crate::all2all::TrivialAll2All;
    use crate::consensus::cert::{FinalCert, NotarCert};
    use crate::consensus::{ConsensusMessage, EpochInfo};
    use crate::crypto::Hash;
    use crate::network::SimulatedNetwork;
    use crate::test_utils::{
        generate_all2all_instances, generate_validators, genesis_block_id, random_block_id,
    };
    use crate::types::SLOTS_PER_WINDOW;

    type A2A = TrivialAll2All<SimulatedNetwork<ConsensusMessage, ConsensusMessage>>;

    struct TestContext {
        other_a2a: A2A,
        pool_tx: mpsc::Sender<PoolEvent>,
        blockstore_tx: mpsc::Sender<BlockstoreEvent>,
        epoch_info: EpochInfo,
        sks: Vec<SecretKey>,
    }

    impl TestContext {
        /// Notifies the votor of a new block and waits for the resulting notar vote.
        async fn send_block_and_expect_notar(&self, slot: Slot, parent: (Slot, BlockHash)) -> Vote {
            self.blockstore_tx
                .send(BlockstoreEvent::FirstShred(slot))
                .await
                .unwrap();
            let block_info = BlockInfo {
                hash: Hash::random_for_test().into(),
                parent,
            };
            self.blockstore_tx
                .send(BlockstoreEvent::Block { slot, block_info })
                .await
                .unwrap();
            match self.other_a2a.receive().await.unwrap() {
                ConsensusMessage::Vote(v) => {
                    assert!(matches!(v, Vote::Notar(_)));
                    assert_eq!(v.slot(), slot);
                    v
                }
                m => panic!("other msg: {m:?}"),
            }
        }
    }

    /// Creates a fresh fully wired-up [`Votor`] instance.
    ///
    /// The returned votor is not running its event loop.
    /// Callers either run its [`Votor::voting_loop`] (see [`start_votor`])
    /// or drive its handlers manually.
    async fn build_votor() -> (Votor<A2A>, TestContext) {
        let (sks, epoch_info) = generate_validators(2);
        let mut a2a = generate_all2all_instances(epoch_info.validators().to_vec()).await;
        let (pool_tx, pool_rx) = mpsc::channel(100);
        let (blockstore_tx, blockstore_rx) = mpsc::channel(100);
        let other_a2a = a2a.pop().unwrap();
        let votor_a2a = a2a.pop().unwrap();
        let votor = Votor::new(
            ValidatorIndex::new(0),
            sks[0].clone(),
            pool_rx,
            blockstore_rx,
            Arc::new(votor_a2a),
        );
        let ctx = TestContext {
            other_a2a,
            pool_tx,
            blockstore_tx,
            epoch_info,
            sks,
        };
        (votor, ctx)
    }

    /// Builds a votor and spawns its [`Votor::voting_loop`].
    ///
    /// Returns the votor instance and the test context.
    async fn start_votor() -> TestContext {
        let (mut votor, ctx) = build_votor().await;
        tokio::spawn(async move {
            votor.voting_loop().await.unwrap();
        });
        ctx
    }

    #[tokio::test]
    async fn timeouts() {
        let ctx = start_votor().await;

        // should vote skip for all slots
        let mut skipped_slots = Vec::new();
        let mut slots = Slot::genesis().slots_in_window().collect::<Vec<_>>();
        slots.remove(0);
        for _ in slots.clone() {
            if let Ok(msg) = ctx.other_a2a.receive().await {
                match msg {
                    ConsensusMessage::Vote(v) => {
                        assert!(matches!(v, Vote::Skip(_)));
                        skipped_slots.push(v.slot());
                    }
                    m => panic!("other msg: {m:?}"),
                }
            }
        }
        assert_eq!(skipped_slots, slots);
    }

    #[tokio::test]
    async fn notar_and_final() {
        let ctx = start_votor().await;
        let slot = Slot::genesis().next();
        let parent = genesis_block_id();

        // vote notar after seeing block
        let vote = ctx.send_block_and_expect_notar(slot, parent).await;

        // vote finalize after seeing branch-certified
        let Vote::Notar(notar_vote) = vote else {
            unreachable!()
        };
        let cert = Cert::Notar(NotarCert::new_unchecked(
            &[notar_vote],
            ctx.epoch_info.validators(),
        ));
        ctx.pool_tx
            .send(PoolEvent::CertCreated(Box::new(cert)))
            .await
            .unwrap();
        match ctx.other_a2a.receive().await.unwrap() {
            ConsensusMessage::Vote(v) => {
                assert!(matches!(v, Vote::Final(_)));
                assert_eq!(v.slot(), slot);
            }
            m => panic!("other msg: {m:?}"),
        }
    }

    #[tokio::test]
    async fn notar_out_of_order() {
        let ctx = start_votor().await;
        let (slot1, hash1) = (Slot::genesis().next(), Hash::random_for_test());
        let (slot2, hash2) = (slot1.next(), Hash::random_for_test());

        // give later block to votor first
        ctx.blockstore_tx
            .send(BlockstoreEvent::FirstShred(slot2))
            .await
            .unwrap();
        let block_info = BlockInfo {
            hash: hash2.into(),
            parent: (slot1, hash1.clone().into()),
        };
        ctx.blockstore_tx
            .send(BlockstoreEvent::Block {
                slot: slot2,
                block_info,
            })
            .await
            .unwrap();

        // should not vote yet
        assert!(
            tokio::time::timeout(Duration::from_secs(1), ctx.other_a2a.receive())
                .await
                .is_err()
        );

        // now notify votor of earlier block
        ctx.blockstore_tx
            .send(BlockstoreEvent::FirstShred(slot1))
            .await
            .unwrap();
        let block_info = BlockInfo {
            hash: hash1.into(),
            parent: genesis_block_id(),
        };
        ctx.blockstore_tx
            .send(BlockstoreEvent::Block {
                slot: slot1,
                block_info,
            })
            .await
            .unwrap();

        // should now see notar votes
        for _ in 0..2 {
            match ctx.other_a2a.receive().await.unwrap() {
                ConsensusMessage::Vote(vote) => {
                    assert!(matches!(vote, Vote::Notar(_)));
                    assert!(vote.slot() == slot1 || vote.slot() == slot2);
                }
                m => panic!("other msg: {m:?}"),
            };
        }
    }

    #[tokio::test]
    async fn safe_to_notar() {
        let ctx = start_votor().await;
        let slot = Slot::genesis().next();

        // wait for skip votes
        for s in slot.slots_in_window() {
            if s.is_genesis() {
                continue;
            }
            if let Ok(msg) = ctx.other_a2a.receive().await {
                match msg {
                    ConsensusMessage::Vote(v) => assert!(matches!(v, Vote::Skip(_))),
                    m => panic!("other msg: {m:?}"),
                }
            }
        }

        // vote notar-fallback after safe-to-notar
        let block = random_block_id(slot);
        ctx.pool_tx
            .send(PoolEvent::SafeToNotar(block.clone()))
            .await
            .unwrap();
        match ctx.other_a2a.receive().await.unwrap() {
            ConsensusMessage::Vote(v) => {
                assert!(matches!(v, Vote::NotarFallback(_)));
                assert_eq!(v.slot(), block.0);
                assert_eq!(v.block_hash(), Some(&block.1));
            }
            m => panic!("other msg: {m:?}"),
        }
    }

    #[tokio::test]
    async fn safe_to_skip() {
        let ctx = start_votor().await;
        let slot = Slot::genesis().next();
        let parent = genesis_block_id();

        // vote notar after seeing block
        ctx.send_block_and_expect_notar(slot, parent).await;

        // vote skip-fallback after safe-to-skip
        ctx.pool_tx.send(PoolEvent::SafeToSkip(slot)).await.unwrap();
        match ctx.other_a2a.receive().await.unwrap() {
            ConsensusMessage::Vote(v) => {
                assert!(matches!(v, Vote::SkipFallback(_)));
                assert_eq!(v.slot(), slot);
            }
            m => panic!("other msg: {m:?}"),
        }
    }

    #[tokio::test]
    async fn prunes_to_finalized_window() {
        let (mut votor, ctx) = build_votor().await;

        // drain broadcasts so votor's sends never block on the bounded network
        let other_a2a = ctx.other_a2a;
        tokio::spawn(async move { while other_a2a.receive().await.is_ok() {} });

        // finalize a slot that is NOT first in its window and isn't in the genesis window
        let finalized = Slot::new(SLOTS_PER_WINDOW + 1);
        let window_start = finalized.first_slot_in_window();
        assert!(window_start > Slot::genesis());
        assert!(window_start < finalized);

        // populate per-slot state across the previous window and into the next one
        let highest = Slot::new(2 * SLOTS_PER_WINDOW);
        for i in 1..=highest.inner() {
            let event = BlockstoreEvent::FirstShred(Slot::new(i));
            votor.handle_blockstore_event(event).await;
        }
        assert!((0..=highest.inner()).all(|i| votor.slots.contains_key(&Slot::new(i))));

        // finalizing a mid-window slot should drop only the slots before its window
        let Vote::Final(final_vote) =
            Vote::new_final(finalized, &ctx.sks[1], ValidatorIndex::new(1))
        else {
            unreachable!()
        };
        let cert = Cert::Final(FinalCert::new_unchecked(
            &[final_vote],
            ctx.epoch_info.validators(),
        ));
        let event = PoolEvent::CertCreated(Box::new(cert));
        votor.handle_pool_event(event).await;
        assert_eq!(votor.highest_final_cert_slot, finalized);

        // the whole finalized window is kept
        assert!(votor.slots.keys().all(|s| *s >= window_start));
        for slot in window_start.slots_in_window() {
            assert!(
                votor.slots.contains_key(&slot),
                "slot {slot} in finalized window should be retained",
            );
        }

        // earlier windows are dropped
        assert!(!votor.slots.contains_key(&Slot::genesis()));
        assert!(!votor.slots.contains_key(&window_start.prev()));
    }
}
