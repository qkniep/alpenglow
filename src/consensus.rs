// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Core consensus logic and data structures.
//!
//! The central structure of the consensus protocol is [`Alpenglow`].
//! It contains all state for a single consensus instance and also has access
//! to the different necessary network protocols.
//!
//! Most important component data structures defined in this module are:
//! - [`BlockstoreImpl`] holds individual shreds and reconstructed blocks for each slot.
//! - [`PoolImpl`] holds votes and certificates for each slot.
//! - `VotorState` handles the main voting logic.
//! - `ConsensusCore` combines the three into one synchronous state machine,
//!   driven by a single `Driver` task that performs all I/O.
//!
//! Some other data types for consensus are also defined here:
//! - [`Cert`] represents a certificate of votes of a specific type.
//! - [`Vote`] represents a vote of a specific type.
//! - [`EpochInfo`] holds information about the epoch and all validators.

mod block_producer;
mod blockstore;
mod cert;
pub(crate) mod core;
mod driver;
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
use log::{debug, trace};
use static_assertions::const_assert;
use tokio::sync::{mpsc, watch};
use tokio_util::sync::CancellationToken;
use wincode::{SchemaRead, SchemaWrite};

pub use self::blockstore::{AddShredError, BlockInfo, BlockstoreEvent, BlockstoreImpl};
pub use self::cert::{Cert, CertError, NotarCert};
use self::core::{ConsensusCore, Input};
use self::driver::{CommitmentCache, DisseminatedMap, Driver, ParentReadyMap};
pub use self::epoch_info::{EpochInfo, ValidatorEpochInfo};
#[cfg(feature = "test-utils")]
pub use self::pool::bench_replay_votes;
pub use self::pool::{AddVoteError, PoolEvent, PoolImpl, PoolOutbox};
pub use self::validated_cert::{CertValidationError, ValidatedCert};
pub use self::validated_vote::{ValidatedVote, VoteValidationError};
pub use self::vote::{FinalVote, NotarFallbackVote, NotarVote, SkipFallbackVote, SkipVote, Vote};
use crate::consensus::block_producer::BlockProducer;
use crate::crypto::{aggsig, signature};
use crate::network::{RepairRequesterNetwork, RepairResponderNetwork, TransactionNetwork};
use crate::repair::{Repair, RepairRequestHandler};
use crate::shredder::{Shred, ValidatedShred};
use crate::types::Fraction;
use crate::{All2All, Disseminator, Slot, ValidatorInfo};

/// Time bound assumed on network transmission delays during periods of synchrony.
pub const DELTA: Duration = Duration::from_millis(250);
/// Time the leader has for producing and sending the block.
const DELTA_BLOCK: Duration = Duration::from_millis(400);
/// Time the leader has for producing and sending the first slice.
const DELTA_FIRST_SLICE: Duration = Duration::from_millis(10);
const_assert!(DELTA_FIRST_SLICE.as_nanos() <= DELTA_BLOCK.as_nanos());
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

/// Alpenglow consensus protocol implementation.
pub struct Alpenglow<A: All2All, D: Disseminator, T>
where
    T: TransactionNetwork + 'static,
{
    /// Other validators' info.
    epoch_info: Arc<ValidatorEpochInfo>,

    /// Inputs destined for the consensus core (driver task).
    ///
    /// A full channel back-pressures the ingest tasks; a closed one means the
    /// driver shut down, at which point remaining messages are dropped.
    inputs: mpsc::Sender<Input>,
    /// Per-slice commitment cache read by the shred-ingest path; written by the
    /// driver from the core's [`core::Output::SliceCommitment`] outputs.
    commitments: CommitmentCache,
    /// Observes the highest finalized slot, published by the driver.
    finalized: watch::Receiver<Slot>,

    /// Block production (i.e. leader side) component of the consensus protocol.
    block_producer: Arc<BlockProducer<D, T>>,

    /// All-to-all broadcast network protocol for consensus messages.
    all2all: Arc<A>,
    /// Block dissemination network protocol for shreds.
    disseminator: Arc<D>,

    /// Indicates whether the node is shutting down.
    cancel_token: CancellationToken,
    /// Consensus driver task handle.
    driver_handle: tokio::task::JoinHandle<()>,
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
        // The consensus core's inbox. Ingest tasks (message loop, block
        // producer, repair loop) push validated inputs here; a full channel
        // back-pressures them. The buffer is sized to absorb ordinary bursts
        // without back-pressuring.
        let (input_tx, input_rx) = mpsc::channel(1024);
        let (repair_tx, repair_rx) = mpsc::channel(1024);
        let (parent_ready_tx, parent_ready_rx) = watch::channel(ParentReadyMap::new());
        let (disseminated_tx, disseminated_rx) = watch::channel(DisseminatedMap::new());
        let (finalized_tx, finalized_rx) = watch::channel(Slot::genesis());
        let commitments = CommitmentCache::default();
        let all2all = Arc::new(all2all);

        let core = ConsensusCore::new(epoch_info.clone(), voting_secret_key, Instant::now());
        let driver = Driver::new(
            core,
            input_rx,
            all2all.clone(),
            repair_tx,
            parent_ready_tx,
            disseminated_tx,
            finalized_tx,
            commitments.clone(),
            cancel_token.clone(),
        );
        let driver_handle = tokio::spawn(
            driver
                .run()
                .in_span(Span::enter_with_local_parent("consensus driver")),
        );

        let repair_request_handler = RepairRequestHandler::new(
            epoch_info.clone(),
            input_tx.clone(),
            repair_responder_network,
        );
        let _repair_request_handler =
            tokio::spawn(async move { repair_request_handler.run().await });

        let mut repair = Repair::new(
            repair_requester_network,
            epoch_info.clone(),
            input_tx.clone(),
        );

        let _repair_handle = tokio::spawn(
            async move { repair.repair_loop(repair_rx).await }
                .in_span(Span::enter_with_local_parent("repair loop")),
        );

        let disseminator = Arc::new(disseminator);

        let block_producer = Arc::new(BlockProducer::new(
            secret_key,
            epoch_info.clone(),
            disseminator.clone(),
            txs_receiver,
            input_tx.clone(),
            parent_ready_rx,
            disseminated_rx,
            finalized_rx.clone(),
            cancel_token.clone(),
            DELTA_BLOCK,
            DELTA_FIRST_SLICE,
        ));

        Self {
            epoch_info,
            inputs: input_tx,
            commitments,
            finalized: finalized_rx,
            block_producer,
            all2all,
            disseminator,
            cancel_token,
            driver_handle,
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

        let block_production_span = Span::enter_with_local_parent("block production");
        let block_producer = Arc::clone(&node.block_producer);
        let prod_loop = tokio::spawn(
            async move { block_producer.block_production_loop().await }
                .in_span(block_production_span),
        );

        node.cancel_token.cancelled().await;
        node.driver_handle.abort();
        msg_loop.abort();
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

    /// Returns a watch receiver tracking the highest finalized slot.
    #[must_use]
    pub fn finalized_slot(&self) -> watch::Receiver<Slot> {
        self.finalized.clone()
    }

    pub fn get_cancel_token(&self) -> CancellationToken {
        self.cancel_token.clone()
    }

    /// Handles incoming messages on all the different network interfaces.
    ///
    /// [`All2All`]: Handles incoming votes and certificates, feeding them to the consensus core.
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

    /// Pushes an input into the consensus core's inbox.
    ///
    /// A full inbox back-pressures the calling ingest task. A closed inbox
    /// means the driver shut down; the input is dropped with a debug log
    /// rather than treated as an error, since the node is going down anyway.
    async fn send_input(&self, input: Input) {
        if self.inputs.send(input).await.is_err() {
            debug!("consensus core inbox closed, dropping input");
        }
    }

    /// Validates an incoming consensus message and feeds it to the core.
    ///
    /// Signatures are verified here, in the (parallelizable) ingest task,
    /// mirroring the `ValidatedShred` pattern on the shred path — the core
    /// never performs crypto.
    #[fastrace::trace(short_name = true)]
    async fn handle_all2all_message(&self, msg: ConsensusMessage) {
        trace!("received all2all msg: {msg:?}");

        let epoch_info = self.epoch_info.epoch_info();
        match msg {
            ConsensusMessage::Vote(v) => match ValidatedVote::try_new(v, epoch_info) {
                Ok(vote) => self.send_input(Input::Vote(vote)).await,
                Err(err) => trace!("ignoring invalid vote: {err}"),
            },
            ConsensusMessage::Cert(c) => match ValidatedCert::try_new(c, epoch_info) {
                Ok(cert) => self.send_input(Input::Cert(cert)).await,
                Err(err) => trace!("ignoring invalid cert: {err}"),
            },
        }
    }

    #[fastrace::trace(short_name = true)]
    #[hotpath::measure]
    async fn handle_disseminator_shred(&self, shred: Shred) -> std::io::Result<()> {
        // validate shred before forwarding or inserting
        let slot = shred.payload().header.slot;
        let slice_index = shred.payload().header.slice_index;
        let leader_pk = self.epoch_info.epoch_info().leader(slot).pubkey;
        // use cached commitment, if we have it, to skip signature verification;
        // the cache is fed by the core's `SliceCommitment` outputs (the core
        // owns the blockstore, so this edge can no longer read it directly)
        let cached = self.commitments.get(slot, slice_index);
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

        // Hand the validated shred to the consensus core, which owns the
        // blockstore, ingests it and registers any completed block with the pool.
        self.send_input(Input::DisseminatedShred(validated)).await;
        Ok(())
    }
}
