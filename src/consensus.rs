// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Core consensus logic and data structures.
//!
//! The central structure of the consensus protocol is [`Alpenglow`].
//! It contains all state for a single consensus instance and also has access
//! to the different necessary network protocols.
//!
//! Most important component data structures defined in this module are:
//! - [`Blockstore`] holds individual shreds and reconstructed blocks for each slot.
//! - [`Pool`] holds votes and certificates for each slot.
//! - [`Votor`] handles the main voting logic.
//!
//! Some other data types for consensus are also defined here:
//! - [`Cert`] represents a certificate of votes of a specific type.
//! - [`Vote`] represents a vote of a specific type.
//! - [`EpochInfo`] holds information about the epoch and all validators.

mod block_producer;
mod blockstore;
mod cert;
mod epoch_info;
mod pool;
mod validated_cert;
mod validated_vote;
mod vote;
mod votor;

use std::marker::{Send, Sync};
use std::num::NonZeroU64;
use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::Result;
use fastrace::Span;
use fastrace::future::FutureExt;
use log::{debug, error, trace, warn};
use tokio::sync::{RwLock, mpsc};
use tokio_util::sync::CancellationToken;
use wincode::{SchemaRead, SchemaWrite};

pub use self::blockstore::{
    AddShredError, BlockInfo, Blockstore, BlockstoreEvent, BlockstoreImpl, SharedBlockstore,
};
pub use self::cert::{Cert, CertError, NotarCert};
pub use self::epoch_info::{EpochInfo, ValidatorEpochInfo};
#[cfg(feature = "test-utils")]
pub use self::pool::bench_replay_votes;
pub use self::pool::{AddVoteError, Pool, PoolEffect, PoolEvent, PoolImpl, PoolOutbox, SharedPool};
pub use self::validated_cert::{CertValidationError, ValidatedCert};
pub use self::validated_vote::{ValidatedVote, VoteValidationError};
pub use self::vote::{FinalVote, NotarFallbackVote, NotarVote, SkipFallbackVote, SkipVote, Vote};
pub use self::votor::Votor;
use crate::consensus::block_producer::BlockProducer;
use crate::crypto::{aggsig, signature};
use crate::network::{RepairRequesterNetwork, RepairResponderNetwork, TransactionNetwork};
use crate::repair::{Repair, RepairRequestHandler};
use crate::shredder::{Shred, ValidatedShred};
use crate::types::Fraction;
use crate::{All2All, BlockId, Disseminator, Slot, ValidatorInfo};

/// Time bound assumed on network transmission delays during periods of synchrony.
pub const DELTA: Duration = Duration::from_millis(250);
/// Time the leader has for producing and sending the block.
const DELTA_BLOCK: Duration = Duration::from_millis(400);
/// Time the leader has for producing and sending the first slice.
const DELTA_FIRST_SLICE: Duration = Duration::from_millis(10);
const _: () = assert!(DELTA_FIRST_SLICE.as_nanos() <= DELTA_BLOCK.as_nanos());
/// Base timeout for when leader's first slice should arrive if they sent it immediately.
const DELTA_TIMEOUT: Duration = DELTA.checked_mul(3).unwrap();
/// Timeout for standstill detection mechanism.
const DELTA_STANDSTILL: Duration = Duration::from_millis(10_000);

/// Minimum fraction of total stake required for a weakest quorum (20%).
pub const WEAKEST_QUORUM_THRESHOLD: Fraction = Fraction::new(1, NonZeroU64::new(5).unwrap());
/// Minimum fraction of total stake required for a weak quorum (40%).
pub const WEAK_QUORUM_THRESHOLD: Fraction = Fraction::new(2, NonZeroU64::new(5).unwrap());
/// Minimum fraction of total stake required for a standard quorum (60%).
///
/// Used for notar, notar-fallback, skip, and final certificates.
pub const QUORUM_THRESHOLD: Fraction = Fraction::new(3, NonZeroU64::new(5).unwrap());
/// Minimum fraction of total stake required for a strong quorum (80%).
///
/// Used for fast-final certificates.
pub const STRONG_QUORUM_THRESHOLD: Fraction = Fraction::new(4, NonZeroU64::new(5).unwrap());

#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub enum ConsensusMessage {
    Vote(Vote),
    Cert(Cert),
}

impl From<Vote> for ConsensusMessage {
    fn from(vote: Vote) -> Self {
        Self::Vote(vote)
    }
}

impl From<Cert> for ConsensusMessage {
    fn from(cert: Cert) -> Self {
        Self::Cert(cert)
    }
}

/// Forwards side-effects drained from the Blockstore and Pool outboxes to Votor
/// and the repair loop *after* the producing task has released the write lock.
///
/// The Blockstore and Pool buffer their events instead of sending them while
/// holding their write lock: a blocking send under the lock would let a slow or
/// stalled Votor jam every other task contending for that lock, while a
/// non-blocking send would have to drop the event (which for a reconstructed-block
/// event silently costs this node its vote for that block, with no retry path).
/// Each task that mutates the Blockstore/Pool drains the outbox (with
/// [`Blockstore::take_events`] / [`Pool::take_outbox`]) and hands it here; the
/// blocking send then back-pressures that (ingest) task instead of dropping the
/// event or stalling the lock.
///
/// # Ordering
///
/// Forwarding one drained outbox preserves the order the producing component
/// buffered its effects in. What the write lock no longer provides is a *global*
/// order across tasks: two tasks that each mutate the Pool or Blockstore can now
/// interleave their forwarding, so Votor may see a later task's event before an
/// earlier one's.
///
/// Votor must therefore not depend on the relative order of events from different
/// tasks, on either channel. For pool events that holds already: handling is
/// order-insensitive apart from the prune gate
/// (`Votor::should_ignore_pool_event`), and an event losing that race is by
/// definition one for a slot whose vote no longer matters. On the blockstore
/// channel the order-sensitive pair is `InvalidBlock` against `Block` for the same
/// window, which `Votor::try_skip_window` handles by marking the window bad
/// regardless of whether the slot was already voted on.
///
/// Restoring the global order is not the alternative it looks like: it would take
/// a second lock held across the send, reintroducing exactly the jam this design
/// exists to avoid, and it would not even be sufficient — the lock only ever
/// ordered events already buffered, never the arrival of the inputs that produce
/// them.
///
/// Cloneable so the message loop, the repair loop and the block producer can each
/// forward the events they produce.
#[derive(Clone)]
pub(crate) struct EventForwarder {
    /// Blockstore events destined for Votor.
    blockstore_events: mpsc::Sender<BlockstoreEvent>,
    /// Pool events destined for Votor.
    pool_events: mpsc::Sender<PoolEvent>,
    /// Repair requests destined for the repair loop.
    repairs: mpsc::Sender<BlockId>,
    /// Shuts the node down when a consumer disappears unexpectedly.
    cancel_token: CancellationToken,
}

impl EventForwarder {
    /// Creates a forwarder over Votor's event channels and the repair channel.
    ///
    /// `cancel_token` is the node's shutdown token, used both to tell an expected
    /// shutdown from an unexpected consumer death and to bring the node down in
    /// the latter case.
    pub(crate) fn new(
        blockstore_events: mpsc::Sender<BlockstoreEvent>,
        pool_events: mpsc::Sender<PoolEvent>,
        repairs: mpsc::Sender<BlockId>,
        cancel_token: CancellationToken,
    ) -> Self {
        Self {
            blockstore_events,
            pool_events,
            repairs,
            cancel_token,
        }
    }

    /// Sends a single `item` to `sender`, returning `false` if the channel closed.
    ///
    /// A closed channel means the consuming task is gone. While the node is
    /// shutting down that is expected and the item is simply dropped. Otherwise
    /// it is unrecoverable: Votor or the repair loop died, and a node that keeps
    /// ingesting but can no longer vote contributes nothing while still counting
    /// against liveness. Rather than fail silently, log at error level (using
    /// `what` to name the channel) and shut the node down.
    async fn send<T>(&self, sender: &mpsc::Sender<T>, item: T, what: &str) -> bool {
        if sender.send(item).await.is_ok() {
            return true;
        }
        if self.cancel_token.is_cancelled() {
            debug!("{what} channel closed during shutdown, dropping remaining events");
        } else {
            error!("{what} channel closed unexpectedly, shutting down node");
            self.cancel_token.cancel();
        }
        false
    }

    /// Forwards buffered blockstore events to Votor.
    pub(crate) async fn forward_blockstore_events(&self, events: Vec<BlockstoreEvent>) {
        for event in events {
            if !self
                .send(&self.blockstore_events, event, "Votor blockstore-event")
                .await
            {
                return;
            }
        }
    }

    /// Forwards a single Pool event to Votor.
    pub(crate) async fn forward_pool_event(&self, event: PoolEvent) {
        self.send(&self.pool_events, event, "Votor pool-event")
            .await;
    }

    /// Forwards a drained [`PoolOutbox`], replaying the effects in the order the
    /// Pool produced them.
    pub(crate) async fn forward_pool_outbox(&self, outbox: PoolOutbox) {
        for effect in outbox.effects {
            let sent = match effect {
                PoolEffect::VotorEvent(event) => {
                    self.send(&self.pool_events, event, "Votor pool-event")
                        .await
                }
                PoolEffect::Repair(block_id) => self.send(&self.repairs, block_id, "repair").await,
            };
            if !sent {
                return;
            }
        }
    }
}

/// Alpenglow consensus protocol implementation.
pub struct Alpenglow<A: All2All, D: Disseminator, T>
where
    T: TransactionNetwork + 'static,
{
    /// Other validators' info.
    epoch_info: Arc<ValidatorEpochInfo>,

    /// Blockstore for storing raw block data.
    blockstore: SharedBlockstore,
    /// Pool of votes and certificates.
    pool: SharedPool,

    /// Block production (i.e. leader side) component of the consensus protocol.
    block_producer: Arc<BlockProducer<D, T>>,

    /// All-to-all broadcast network protocol for consensus messages.
    all2all: Arc<A>,
    /// Block dissemination network protocol for shreds.
    disseminator: Arc<D>,

    /// Forwards blockstore outbox events to Votor off the write lock.
    event_forwarder: EventForwarder,

    /// Indicates whether the node is shutting down.
    cancel_token: CancellationToken,
    /// Votor task handle.
    votor_handle: tokio::task::JoinHandle<()>,
}

/// Interprets a joined task result during shutdown.
///
/// On shutdown the loops are aborted.
/// So a [`JoinError`] from cancellation is the expected outcome and maps to `Ok(())`.
/// A panic still propagates, as does any error the task itself returned.
///
/// [`JoinError`]: tokio::task::JoinError
fn join_for_shutdown(res: Result<Result<()>, tokio::task::JoinError>) -> Result<()> {
    match res {
        Ok(inner) => inner,
        Err(err) if err.is_cancelled() => Ok(()),
        Err(err) => Err(err.into()),
    }
}

impl<A, D, T> Alpenglow<A, D, T>
where
    A: All2All + Send + Sync + 'static,
    D: Disseminator + Send + Sync + 'static,
    T: TransactionNetwork + 'static,
{
    /// Creates a new Alpenglow consensus node.
    ///
    /// `repair_requester_network` - [`RepairRequesterNetwork`] for sending requests and receiving responses.
    /// `repair_responder_network` - [`RepairResponderNetwork`] for answering incoming requests.
    #[must_use]
    #[expect(clippy::too_many_arguments)]
    pub fn new<RQ, RP>(
        secret_key: signature::SecretKey,
        voting_secret_key: aggsig::SecretKey,
        all2all: A,
        disseminator: D,
        repair_requester_network: RQ,
        repair_responder_network: RP,
        epoch_info: Arc<ValidatorEpochInfo>,
        txs_receiver: T,
    ) -> Self
    where
        RQ: RepairRequesterNetwork + 'static,
        RP: RepairResponderNetwork + 'static,
    {
        let cancel_token = CancellationToken::new();
        // Votor's event channels. The Blockstore/Pool buffer events into an outbox
        // under their write lock and the producing task forwards them here *after*
        // releasing the lock (see `EventForwarder`), so a full channel back-pressures
        // the ingest task rather than jamming the lock or dropping the event. The
        // buffer is sized to absorb ordinary bursts without back-pressuring.
        let (blockstore_tx, blockstore_rx) = mpsc::channel(1024);
        let (pool_tx, pool_rx) = mpsc::channel(1024);
        let (repair_tx, repair_rx) = mpsc::channel(1024);
        let all2all = Arc::new(all2all);

        let event_forwarder =
            EventForwarder::new(blockstore_tx, pool_tx, repair_tx, cancel_token.clone());

        let blockstore: SharedBlockstore = Arc::new(RwLock::new(BlockstoreImpl::new()));

        let pool: SharedPool = Arc::new(RwLock::new(PoolImpl::new(epoch_info.clone())));

        let repair_request_handler = RepairRequestHandler::new(
            epoch_info.clone(),
            blockstore.clone(),
            repair_responder_network,
        );
        let _repair_request_handler =
            tokio::spawn(async move { repair_request_handler.run().await });

        let mut repair = Repair::new(
            Arc::clone(&blockstore),
            Arc::clone(&pool),
            repair_requester_network,
            epoch_info.clone(),
            event_forwarder.clone(),
        );

        let _repair_handle = tokio::spawn(
            async move { repair.repair_loop(repair_rx).await }
                .in_span(Span::enter_with_local_parent("repair loop")),
        );

        let mut votor = Votor::new(
            epoch_info.own_id(),
            voting_secret_key,
            pool_rx,
            blockstore_rx,
            all2all.clone(),
        );
        let votor_handle = tokio::spawn(
            async move { votor.voting_loop().await }
                .in_span(Span::enter_with_local_parent("voting loop")),
        );

        let disseminator = Arc::new(disseminator);

        let block_producer = Arc::new(BlockProducer::new(
            secret_key,
            epoch_info.clone(),
            disseminator.clone(),
            txs_receiver,
            blockstore.clone(),
            pool.clone(),
            event_forwarder.clone(),
            cancel_token.clone(),
            DELTA_BLOCK,
            DELTA_FIRST_SLICE,
        ));

        Self {
            epoch_info,
            blockstore,
            pool,
            block_producer,
            all2all,
            disseminator,
            event_forwarder,
            cancel_token,
            votor_handle,
        }
    }

    /// Starts the different tasks of the Alpenglow node.
    ///
    /// # Errors
    ///
    /// Returns an error only if any of the tasks panics.
    #[fastrace::trace(short_name = true)]
    pub async fn run(self) -> Result<()> {
        let msg_loop_span = Span::enter_with_local_parent("message loop");
        let node = Arc::new(self);
        let nn = node.clone();
        let msg_loop = tokio::spawn(async move { nn.message_loop().await }.in_span(msg_loop_span));

        let standstill_loop_span = Span::enter_with_local_parent("standstill detection loop");
        let nn = node.clone();
        let standstill_loop =
            tokio::spawn(async move { nn.standstill_loop().await }.in_span(standstill_loop_span));

        let block_production_span = Span::enter_with_local_parent("block production");
        let block_producer = Arc::clone(&node.block_producer);
        let prod_loop = tokio::spawn(
            async move { block_producer.block_production_loop().await }
                .in_span(block_production_span),
        );

        node.cancel_token.cancelled().await;
        node.votor_handle.abort();
        msg_loop.abort();
        standstill_loop.abort();
        prod_loop.abort();

        let (msg_res, prod_res) = tokio::join!(msg_loop, prod_loop);
        join_for_shutdown(msg_res)?;
        join_for_shutdown(prod_res)?;
        Ok(())
    }

    pub fn get_info(&self) -> &ValidatorInfo {
        self.epoch_info
            .epoch_info()
            .validator(self.epoch_info.own_id())
    }

    pub fn get_pool(&self) -> SharedPool {
        Arc::clone(&self.pool)
    }

    pub fn get_cancel_token(&self) -> CancellationToken {
        self.cancel_token.clone()
    }

    /// Handles incoming messages on all the different network interfaces.
    ///
    /// [`All2All`]: Handles incoming votes and certificates. Adds them to the [`Pool`].
    /// [`Disseminator`]: Handles incoming shreds. Adds them to the [`Blockstore`].
    async fn message_loop(self: &Arc<Self>) -> Result<()> {
        loop {
            tokio::select! {
                // handle incoming votes and certificates
                res = self.all2all.receive() => self.handle_all2all_message(res?).await,
                // handle shreds received by block dissemination protocol
                res = self.disseminator.receive() => self.handle_disseminator_shred(res?).await?,

                () = self.cancel_token.cancelled() => return Ok(()),
            };
        }
    }

    /// Handles standstill detection and triggers recovery.
    ///
    /// Keeps track of when consensus progresses, i.e., [`Pool`] finalizes new blocks.
    /// Triggers standstill recovery if no progress was detected for a long time.
    async fn standstill_loop(self: &Arc<Self>) -> Result<()> {
        let mut finalized_slot = Slot::new(0);
        let mut last_progress = Instant::now();
        loop {
            let slot = self.pool.read().await.finalized_slot();
            if slot > finalized_slot {
                finalized_slot = slot;
                last_progress = Instant::now();
            } else if last_progress.elapsed() > DELTA_STANDSTILL {
                let outbox = self.pool.read().await.recover_from_standstill();
                self.event_forwarder.forward_pool_outbox(outbox).await;
                last_progress = Instant::now();
            }
            tokio::time::sleep(DELTA_BLOCK).await;
        }
    }

    #[fastrace::trace(short_name = true)]
    async fn handle_all2all_message(&self, msg: ConsensusMessage) {
        trace!("received all2all msg: {msg:?}");

        // verify signatures BEFORE taking the pool lock,
        // mirroring the `ValidatedShred` pattern on the shred path
        let epoch_info = self.epoch_info.epoch_info();
        match msg {
            ConsensusMessage::Vote(v) => {
                let vote = match ValidatedVote::try_new(v, epoch_info) {
                    Ok(vote) => vote,
                    Err(err) => {
                        trace!("ignoring invalid vote: {err}");
                        return;
                    }
                };
                // Add under the lock, then forward the buffered events off the lock.
                let outbox = {
                    let mut pool = self.pool.write().await;
                    match pool.add_vote(vote).await {
                        Ok(()) => {}
                        Err(AddVoteError::Slashable(offence)) => {
                            warn!("slashable offence detected: {offence}");
                        }
                        Err(err) => trace!("ignoring invalid vote: {err}"),
                    }
                    pool.take_outbox()
                };
                self.event_forwarder.forward_pool_outbox(outbox).await;
            }
            ConsensusMessage::Cert(c) => {
                let cert = match ValidatedCert::try_new(c, epoch_info) {
                    Ok(cert) => cert,
                    Err(err) => {
                        trace!("ignoring invalid cert: {err}");
                        return;
                    }
                };
                let outbox = {
                    let mut pool = self.pool.write().await;
                    match pool.add_cert(cert).await {
                        Ok(()) => {}
                        Err(err) => trace!("ignoring invalid cert: {err}"),
                    }
                    pool.take_outbox()
                };
                self.event_forwarder.forward_pool_outbox(outbox).await;
            }
        }
    }

    #[fastrace::trace(short_name = true)]
    #[hotpath::measure]
    async fn handle_disseminator_shred(&self, shred: Shred) -> std::io::Result<()> {
        // validate shred before forwarding or inserting
        let slot = shred.payload().header.slot;
        let slice_index = shred.payload().header.slice_index;
        let leader_pk = self.epoch_info.epoch_info().leader(slot).pubkey;
        // use cached commitment, if we have it, to skip signature verification
        let cached = self
            .blockstore
            .read()
            .await
            .cached_commitment(slot, slice_index);
        let validated = match ValidatedShred::try_new(shred, cached.as_ref(), &leader_pk) {
            Ok(v) => v,
            Err(_) => return Ok(()),
        };

        // potentially forward shred
        self.disseminator.forward(validated.as_shred()).await?;

        // if we are the leader, we already have the shred
        if self.epoch_info.epoch_info().leader(slot).id == self.epoch_info.own_id() {
            return Ok(());
        }

        // Ingest into the blockstore, then forward the buffered events to Votor
        // *after* releasing the write lock (see `EventForwarder`).
        let (res, events) = {
            let mut blockstore = self.blockstore.write().await;
            let res = blockstore.add_shred_from_dissemination(validated).await;
            (res, blockstore.take_events())
        };
        self.event_forwarder.forward_blockstore_events(events).await;

        if let Ok(Some(block_info)) = res {
            let block_id = (slot, block_info.hash);
            let outbox = {
                let mut pool = self.pool.write().await;
                pool.add_block(block_id, block_info.parent).await;
                pool.take_outbox()
            };
            self.event_forwarder.forward_pool_outbox(outbox).await;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;

    /// A closed Votor / repair channel on a shutting-down node must not panic the
    /// forwarder: the send fails, is logged, and the remaining items are dropped.
    #[tokio::test]
    async fn forward_to_closed_channels_during_shutdown_does_not_panic() {
        let (bs_tx, bs_rx) = mpsc::channel(1);
        let (pool_tx, pool_rx) = mpsc::channel(1);
        let (repair_tx, repair_rx) = mpsc::channel(1);
        let cancel_token = CancellationToken::new();
        // The node is already shutting down, which is why its consumers are gone.
        cancel_token.cancel();
        let forwarder = EventForwarder::new(bs_tx, pool_tx, repair_tx, cancel_token);
        drop(bs_rx);
        drop(pool_rx);
        drop(repair_rx);

        forwarder
            .forward_blockstore_events(vec![BlockstoreEvent::FirstShred(Slot::new(1))])
            .await;
        forwarder
            .forward_pool_outbox(PoolOutbox {
                effects: vec![
                    PoolEffect::VotorEvent(PoolEvent::SafeToSkip(Slot::new(1))),
                    PoolEffect::Repair((Slot::new(1), GENESIS_BLOCK_HASH)),
                ],
            })
            .await;
    }

    /// A consumer dying while the node is running is unrecoverable: this node can
    /// no longer vote, so the forwarder shuts it down instead of dropping events
    /// silently and leaving a zombie that still counts against liveness.
    #[tokio::test]
    async fn consumer_death_while_running_shuts_node_down() {
        let (bs_tx, bs_rx) = mpsc::channel(1);
        let (pool_tx, _pool_rx) = mpsc::channel(1);
        let (repair_tx, _repair_rx) = mpsc::channel(1);
        let cancel_token = CancellationToken::new();
        let forwarder = EventForwarder::new(bs_tx, pool_tx, repair_tx, cancel_token.clone());
        // Votor died mid-run, taking its receiver with it.
        drop(bs_rx);

        assert!(!cancel_token.is_cancelled());
        forwarder
            .forward_blockstore_events(vec![BlockstoreEvent::FirstShred(Slot::new(1))])
            .await;
        assert!(cancel_token.is_cancelled());
    }

    /// A drained outbox is replayed in the order the Pool produced it: a repair
    /// request buffered before a Votor event is issued before it, not held back
    /// until every Votor event has drained.
    #[tokio::test]
    async fn forward_pool_outbox_preserves_effect_order() {
        let (bs_tx, _bs_rx) = mpsc::channel(1);
        // Capacity 1, so forwarding blocks on the second Votor event.
        let (pool_tx, _pool_rx) = mpsc::channel(1);
        let (repair_tx, mut repair_rx) = mpsc::channel(1);
        let forwarder = EventForwarder::new(bs_tx, pool_tx, repair_tx, CancellationToken::new());

        let block = (Slot::new(3), GENESIS_BLOCK_HASH);
        let outbox = PoolOutbox {
            effects: vec![
                PoolEffect::Repair(block.clone()),
                PoolEffect::VotorEvent(PoolEvent::SafeToSkip(Slot::new(3))),
                PoolEffect::VotorEvent(PoolEvent::SafeToSkip(Slot::new(4))),
            ],
        };
        let handle = tokio::spawn(async move { forwarder.forward_pool_outbox(outbox).await });

        let repaired = tokio::time::timeout(Duration::from_secs(1), repair_rx.recv())
            .await
            .expect("repair request should be forwarded before the Votor events drain");
        assert_eq!(repaired.unwrap(), block);
        handle.abort();
    }

    /// Forwarding delivers all buffered items, in order, to open channels.
    #[tokio::test]
    async fn forward_delivers_all_events_in_order() {
        let (bs_tx, mut bs_rx) = mpsc::channel(8);
        let (pool_tx, mut pool_rx) = mpsc::channel(8);
        let (repair_tx, mut repair_rx) = mpsc::channel(8);
        let forwarder = EventForwarder::new(bs_tx, pool_tx, repair_tx, CancellationToken::new());

        forwarder
            .forward_blockstore_events(vec![
                BlockstoreEvent::FirstShred(Slot::new(1)),
                BlockstoreEvent::InvalidBlock(Slot::new(2)),
            ])
            .await;
        assert!(
            matches!(bs_rx.try_recv(), Ok(BlockstoreEvent::FirstShred(s)) if s == Slot::new(1))
        );
        assert!(
            matches!(bs_rx.try_recv(), Ok(BlockstoreEvent::InvalidBlock(s)) if s == Slot::new(2))
        );
        assert!(bs_rx.try_recv().is_err());

        let block = (Slot::new(3), GENESIS_BLOCK_HASH);
        forwarder
            .forward_pool_outbox(PoolOutbox {
                effects: vec![
                    PoolEffect::VotorEvent(PoolEvent::SafeToSkip(Slot::new(3))),
                    PoolEffect::Repair(block.clone()),
                ],
            })
            .await;
        assert!(matches!(pool_rx.try_recv(), Ok(PoolEvent::SafeToSkip(s)) if s == Slot::new(3)));
        assert_eq!(repair_rx.try_recv().unwrap(), block);
    }
}
