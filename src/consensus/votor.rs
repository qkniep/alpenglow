// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Main voting logic for the consensus protocol.
//!
//! Besides [`super::Pool`], [`Votor`] is the other main internal component Alpenglow.
//! It handles the main voting decisions for the consensus protocol. As input it
//! receives events of type [`VotorEvent`] over a channel, depending on the event
//! type these were emitted by  [`super::Pool`], [`super::Blockstore`] and itself.
//! Votor keeps its own internal state for each slot based on previous events and votes.
//!
//! Votor has access to an instance of [`All2All`] for broadcasting votes.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use color_eyre::Result;
use log::{debug, trace};
use tokio::sync::mpsc::{Receiver, Sender};

use crate::crypto::Hash;
use crate::crypto::aggsig::SecretKey;
use crate::{All2All, Slot, ValidatorId};

use super::{Cert, DELTA_BLOCK, DELTA_EARLY_TIMEOUT, SLOTS_PER_WINDOW, Vote};

#[derive(Clone, Copy, Debug)]
struct BlockInfo {
    hash: Hash,
    parent_slot: Slot,
    parent_hash: Hash,
}

/// Events that Votor is interested in.
/// These are emitted by [`super::Pool`], [`super::Blockstore`] and [`Votor`] itself.
#[derive(Clone, Debug)]
pub enum VotorEvent {
    /// The pool has newly marked the given hash in the given slot as branch certified.
    BranchCertified(Slot, Hash),
    /// The pool has newly observed a skip certificate for the given slot.
    SkipCertified(Slot),
    /// The given block hash in the given slot has reached the safe-to-notar status.
    SafeToNotar(Slot, Hash),
    /// The given slot has reached the safe-to-skip status.
    SafeToSkip(Slot),
    /// New certificated created in pool (should be broadcast by Votor).
    CertCreated(Box<Cert>),

    /// First valid shred of the leader's block was received for the block.
    FirstShred(Slot),
    /// New (complete) block was received.
    Block(Slot, Hash, Slot, Hash),

    /// Regular timeout for the given slot has fired.
    Timeout(Slot),
    /// Early timeout for a crashed leader (nothing was received) has fired.
    TimeoutCrashedLeader(Slot),
}

/// Votor implements the decision process of which votes to cast.
///
/// It keeps some state for each slot and checks the conditions for voting.
/// On [`Votor::event_receiver`], it receives events from [`super::Pool`],
/// [`super::Blockstore`] and itself.
/// Informed by these events Votor updates its state and generates votes.
/// Votes are signed with [`Votor::voting_key`] and broadcast using [`Votor::all2all`].
pub struct Votor<A: All2All + Sync + Send + 'static> {
    // TODO: merge all of these into `SlotState` struct?
    /// Indicates for which slots we already voted notar or skip.
    voted: BTreeSet<Slot>,
    /// Indicates for which slots we already voted notar and for what hash.
    voted_notar: BTreeMap<Slot, Hash>,
    /// Indicates for which slots we voted skip.
    skipped: BTreeSet<Slot>,
    /// Indicates for which slots we received at least one shred.
    received_shred: BTreeSet<Slot>,
    /// Indicates if there is a block that is branch certified.
    branch_certified: BTreeMap<Slot, Hash>,
    /// Indicates for which slots there is a skip certificate in the Pool.
    skip_certified: BTreeSet<Slot>,
    /// Blocks that are waiting for previous slots to be notarized.
    pending_blocks: BTreeMap<Slot, BlockInfo>,
    /// Slots that Votor is done with.
    retired_slots: BTreeSet<Slot>,

    /// Own validator ID.
    validator_id: ValidatorId,
    /// Secret key used to sign votes.
    voting_key: SecretKey,
    /// Channel for receiving events from pool, blockstore and Votor itself.
    event_receiver: Receiver<VotorEvent>,
    /// Sender side of event channel. Used for sending events to self.
    event_sender: Sender<VotorEvent>,
    /// [`All2All`] instance used to broadcast votes.
    all2all: Arc<A>,
}

impl<A: All2All + Sync + Send + 'static> Votor<A> {
    /// Creates a new Votor instance with empty state.
    pub const fn new(
        validator_id: ValidatorId,
        voting_key: SecretKey,
        event_sender: Sender<VotorEvent>,
        event_receiver: Receiver<VotorEvent>,
        all2all: Arc<A>,
    ) -> Self {
        Self {
            voted: BTreeSet::new(),
            voted_notar: BTreeMap::new(),
            skipped: BTreeSet::new(),
            received_shred: BTreeSet::new(),
            branch_certified: BTreeMap::new(),
            skip_certified: BTreeSet::new(),
            pending_blocks: BTreeMap::new(),
            retired_slots: BTreeSet::new(),
            validator_id,
            voting_key,
            event_receiver,
            event_sender,
            all2all,
        }
    }

    /// Handles the voting (leader and non-leader) side of consensus protocol.
    ///
    /// Checks consensus conditions and broadcasts new votes.
    #[fastrace::trace]
    pub async fn voting_loop(&mut self) -> Result<()> {
        while let Some(event) = self.event_receiver.recv().await {
            if self.retired_slots.contains(&event.slot()) {
                trace!("ignoring event for retired slot {}", event.slot());
                continue;
            }
            trace!("votor event: {:?}", event);
            match event {
                // events from Pool
                VotorEvent::BranchCertified(slot, hash) => {
                    self.branch_certified.insert(slot, hash);
                    self.try_final(slot, hash).await;
                    self.check_pending_blocks().await;
                    if slot % SLOTS_PER_WINDOW == SLOTS_PER_WINDOW - 1 {
                        self.set_timeouts(slot);
                    }
                }
                VotorEvent::SkipCertified(slot) => {
                    self.skip_certified.insert(slot);
                    self.check_pending_blocks().await;
                    if slot % SLOTS_PER_WINDOW == SLOTS_PER_WINDOW - 1 {
                        self.set_timeouts(slot);
                    }
                }
                VotorEvent::SafeToNotar(slot, hash) => {
                    let vote =
                        Vote::new_notar_fallback(slot, hash, &self.voting_key, self.validator_id);
                    self.all2all.broadcast(&vote.into()).await.unwrap();
                    self.try_skip_window(slot).await;
                    self.skipped.insert(slot);
                }
                VotorEvent::SafeToSkip(slot) => {
                    let vote = Vote::new_skip_fallback(slot, &self.voting_key, self.validator_id);
                    self.all2all.broadcast(&vote.into()).await.unwrap();
                    self.try_skip_window(slot).await;
                    self.skipped.insert(slot);
                }
                VotorEvent::CertCreated(cert) => {
                    self.all2all.broadcast(&(*cert).into()).await.unwrap();
                }

                // events from Blockstore
                VotorEvent::FirstShred(slot) => {
                    self.received_shred.insert(slot);
                }
                VotorEvent::Block(slot, hash, parent_slot, parent_hash) => {
                    if self.voted.contains(&slot) {
                        continue;
                    }
                    if self.try_notar(slot, hash, parent_slot, parent_hash).await {
                        self.check_pending_blocks().await;
                    } else {
                        let block_info = BlockInfo {
                            hash,
                            parent_slot,
                            parent_hash,
                        };
                        self.pending_blocks.insert(slot, block_info);
                    }
                }

                // events from Votor itself
                VotorEvent::Timeout(slot) => {
                    self.try_skip_window(slot).await;
                }
                VotorEvent::TimeoutCrashedLeader(slot) => {
                    if !self.received_shred.contains(&slot) {
                        self.try_skip_window(slot).await;
                    }
                }
            }
        }

        Ok(())
    }

    /// Sets timeouts for the leader window following the given `slot`.
    ///
    /// # Panics
    ///
    /// Panics if `slot` is not the last slot of a window.
    fn set_timeouts(&self, slot: Slot) {
        assert_eq!((slot + 1) % SLOTS_PER_WINDOW, 0);
        let sender = self.event_sender.clone();
        tokio::spawn(async move {
            tokio::time::sleep(DELTA_EARLY_TIMEOUT).await;
            for offset in 1..=SLOTS_PER_WINDOW {
                let event = VotorEvent::TimeoutCrashedLeader(slot + offset);
                // HACK: ignoring errors to prevent panic when shutting down votor
                let _ = sender.send(event).await;
                tokio::time::sleep(DELTA_BLOCK).await;
                let event = VotorEvent::Timeout(slot + offset);
                let _ = sender.send(event).await;
            }
        });
    }

    /// Sends a notarization vote for the given block if the conditions are met.
    ///
    /// Returns `true` iff we decided to send a notarization vote for the block.
    async fn try_notar(
        &mut self,
        slot: Slot,
        hash: Hash,
        parent_slot: Slot,
        parent_hash: Hash,
    ) -> bool {
        let first_slot = slot / SLOTS_PER_WINDOW * SLOTS_PER_WINDOW;
        if slot == first_slot {
            let parent_certified =
                slot == 0 || self.branch_certified.get(&parent_slot) == Some(&parent_hash);
            let skips_certified = (parent_slot + 1..slot).all(|s| self.skip_certified.contains(&s));
            debug!("try notar slot {}", slot);
            if !parent_certified || !skips_certified {
                return false;
            }
        } else if parent_slot != slot - 1
            || self.voted_notar.get(&parent_slot) != Some(&parent_hash)
        {
            return false;
        }
        debug!(
            "validator {} voted notar for slot {}",
            self.validator_id, slot
        );
        let vote = Vote::new_notar(slot, hash, &self.voting_key, self.validator_id);
        self.all2all.broadcast(&vote.into()).await.unwrap();
        self.voted.insert(slot);
        self.voted_notar.insert(slot, hash);
        self.pending_blocks.remove(&slot);
        self.try_final(slot, hash).await;
        true
    }

    /// Sends a finalization vote for the given block if the conditions are met.
    async fn try_final(&mut self, slot: Slot, hash: Hash) {
        let certified = self.branch_certified.get(&slot) == Some(&hash);
        let voted = self.voted_notar.get(&slot) == Some(&hash);
        let not_skipped = !self.skipped.contains(&slot);
        if certified && voted && not_skipped {
            let vote = Vote::new_final(slot, &self.voting_key, self.validator_id);
            self.all2all.broadcast(&vote.into()).await.unwrap();
            self.retired_slots.insert(slot);
        }
    }

    /// Sends skip votes for all unvoted slots in the window that `slot` belongs to.
    async fn try_skip_window(&mut self, slot: Slot) {
        trace!("try skip window of slot {}", slot);
        let first_slot = slot / SLOTS_PER_WINDOW * SLOTS_PER_WINDOW;
        for s in first_slot..first_slot + SLOTS_PER_WINDOW {
            if self.voted.insert(s) {
                let vote = Vote::new_skip(s, &self.voting_key, self.validator_id);
                self.all2all.broadcast(&vote.into()).await.unwrap();
                self.skipped.insert(s);
                debug!("validator {} voted skip for slot {}", self.validator_id, s);
            }
        }
    }

    /// Checks if we can vote on any of the pending blocks by now.
    async fn check_pending_blocks(&mut self) {
        let slots: Vec<_> = self.pending_blocks.keys().copied().collect();
        for slot in &slots {
            if let Some(block_info) = self.pending_blocks.get(slot) {
                let BlockInfo {
                    hash,
                    parent_slot,
                    parent_hash,
                } = block_info;
                self.try_notar(*slot, *hash, *parent_slot, *parent_hash)
                    .await;
            }
        }
    }
}

impl VotorEvent {
    const fn slot(&self) -> Slot {
        match self {
            Self::BranchCertified(slot, _)
            | Self::SkipCertified(slot)
            | Self::SafeToNotar(slot, _)
            | Self::SafeToSkip(slot)
            | Self::FirstShred(slot)
            | Self::Block(slot, _, _, _)
            | Self::Timeout(slot)
            | Self::TimeoutCrashedLeader(slot) => *slot,
            Self::CertCreated(cert) => cert.slot(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::all2all::TrivialAll2All;
    use crate::network::{NetworkMessage, SimulatedNetwork};
    use crate::tests::{generate_all2all_instances, generate_validators};

    use tokio::sync::mpsc;

    type A2A = TrivialAll2All<SimulatedNetwork>;

    async fn start_votor() -> (A2A, mpsc::Sender<VotorEvent>) {
        let (sks, epoch_info) = generate_validators(2);
        let mut a2a = generate_all2all_instances(epoch_info.validators.clone()).await;
        let (tx, rx) = mpsc::channel(100);
        let other_a2a = a2a.pop().unwrap();
        let votor_a2a = a2a.pop().unwrap();
        let mut votor = Votor::new(0, sks[0].clone(), tx.clone(), rx, Arc::new(votor_a2a));
        tokio::spawn(async move {
            votor.voting_loop().await.unwrap();
        });
        (other_a2a, tx)
    }

    // FIXME: sometimes waits forever
    #[tokio::test]
    async fn skips() {
        let (other_a2a, tx) = start_votor().await;
        for i in 0..SLOTS_PER_WINDOW {
            tx.send(VotorEvent::SkipCertified(i)).await.unwrap();
        }

        // only receive first shred of first block, no full block for the next window
        let event = VotorEvent::FirstShred(SLOTS_PER_WINDOW);
        tx.send(event).await.unwrap();

        // should vote skip for all slots
        for i in 0..SLOTS_PER_WINDOW {
            if let Ok(msg) = other_a2a.receive().await {
                match msg {
                    NetworkMessage::Vote(v) => {
                        assert!(v.is_skip());
                        assert_eq!(v.slot(), SLOTS_PER_WINDOW + i);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[tokio::test]
    async fn notar_and_final() {
        let (other_a2a, tx) = start_votor().await;

        // vote notar after seeing block
        let event = VotorEvent::FirstShred(0);
        tx.send(event).await.unwrap();
        let event = VotorEvent::Block(0, [1u8; 32], 0, Hash::default());
        tx.send(event).await.unwrap();
        if let Ok(msg) = other_a2a.receive().await {
            match msg {
                NetworkMessage::Vote(v) => {
                    assert!(v.is_notar());
                    assert_eq!(v.slot(), 0);
                }
                _ => unreachable!(),
            }
        }

        // vote finalize after seeing branch-certified
        let event = VotorEvent::BranchCertified(0, [1u8; 32]);
        tx.send(event).await.unwrap();
        if let Ok(msg) = other_a2a.receive().await {
            match msg {
                NetworkMessage::Vote(v) => {
                    assert!(v.is_final());
                    assert_eq!(v.slot(), 0);
                }
                _ => unreachable!(),
            }
        }
    }
}
