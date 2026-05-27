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
mod vote;
mod votor;

use std::marker::{Send, Sync};
use std::num::NonZeroU64;
use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::Result;
use fastrace::Span;
use fastrace::future::FutureExt;
use log::{trace, warn};
use static_assertions::const_assert;
use tokio::sync::{RwLock, mpsc};
use tokio_util::sync::CancellationToken;
use wincode::{SchemaRead, SchemaWrite};

pub use self::blockstore::{
    AddShredError, BlockInfo, Blockstore, BlockstoreEvent, BlockstoreImpl, SharedBlockstore,
};
pub use self::cert::{Cert, CertError, NotarCert};
pub use self::epoch_info::{EpochInfo, ValidatorEpochInfo};
pub use self::pool::{AddVoteError, Pool, PoolEvent, PoolImpl, SharedPool};
pub use self::vote::{FinalVote, NotarFallbackVote, NotarVote, SkipFallbackVote, SkipVote, Vote};
pub use self::votor::Votor;
use crate::consensus::block_producer::BlockProducer;
use crate::crypto::{aggsig, signature};
use crate::network::{RepairNetwork, RepairRequestNetwork, TransactionNetwork};
use crate::repair::{Repair, RepairRequestHandler};
use crate::shred_verifier::{NUM_VERIFY_WORKERS, ShredVerifier};
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

    /// Parallel signature-verification stage between the network and consumers.
    shred_verifier: Arc<ShredVerifier>,
    /// Receiver for verified shreds; taken once by [`Self::run`].
    validated_shreds_rx: Option<mpsc::Receiver<ValidatedShred>>,

    /// Indicates whether the node is shutting down.
    cancel_token: CancellationToken,
    /// Votor task handle.
    votor_handle: tokio::task::JoinHandle<()>,
}

impl<A, D, T> Alpenglow<A, D, T>
where
    A: All2All + Send + Sync + 'static,
    D: Disseminator + Send + Sync + 'static,
    T: TransactionNetwork + 'static,
{
    /// Creates a new Alpenglow consensus node.
    ///
    /// `repair_network` - [`RepairNetwork`] for sending requests and receiving responses.
    /// `repair_request_network` - [`RepairRequestNetwork`] for answering incoming requests.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn new<RN, RR>(
        secret_key: signature::SecretKey,
        voting_secret_key: aggsig::SecretKey,
        all2all: A,
        disseminator: D,
        repair_network: RN,
        repair_request_network: RR,
        epoch_info: Arc<ValidatorEpochInfo>,
        txs_receiver: T,
    ) -> Self
    where
        RR: RepairRequestNetwork + 'static,
        RN: RepairNetwork + 'static,
    {
        let cancel_token = CancellationToken::new();
        let (blockstore_tx, blockstore_rx) = mpsc::channel(1024);
        let (pool_tx, pool_rx) = mpsc::channel(1024);
        let (repair_tx, repair_rx) = mpsc::channel(1024);
        let all2all = Arc::new(all2all);

        let blockstore: SharedBlockstore =
            Arc::new(RwLock::new(BlockstoreImpl::new(blockstore_tx)));
        let pool: SharedPool = Arc::new(RwLock::new(PoolImpl::new(
            epoch_info.clone(),
            pool_tx,
            repair_tx,
        )));

        let repair_request_handler = RepairRequestHandler::new(
            epoch_info.clone(),
            blockstore.clone(),
            repair_request_network,
        );
        let _repair_request_handler =
            tokio::spawn(async move { repair_request_handler.run().await });

        let mut repair = Repair::new(
            Arc::clone(&blockstore),
            Arc::clone(&pool),
            repair_network,
            epoch_info.clone(),
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
            async move { votor.voting_loop().await.unwrap() }
                .in_span(Span::enter_with_local_parent("voting loop")),
        );

        let disseminator = Arc::new(disseminator);

        let (shred_verifier, validated_shreds_rx) =
            ShredVerifier::spawn(NUM_VERIFY_WORKERS, epoch_info.clone(), cancel_token.clone());
        let shred_verifier = Arc::new(shred_verifier);

        let block_producer = Arc::new(BlockProducer::new(
            secret_key,
            epoch_info.clone(),
            disseminator.clone(),
            txs_receiver,
            blockstore.clone(),
            pool.clone(),
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
            shred_verifier,
            validated_shreds_rx: Some(validated_shreds_rx),
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
    pub async fn run(mut self) -> Result<()> {
        // `take()` moves the receiver out so the rest of `self` can still be
        // moved into the `Arc` below; `new()` always sets this, so it is `Some`.
        let validated_shreds_rx = self
            .validated_shreds_rx
            .take()
            .expect("validated_shreds_rx is always set by new()");

        let msg_loop_span = Span::enter_with_local_parent("message loop");
        let node = Arc::new(self);
        let nn = node.clone();
        let msg_loop = tokio::spawn(async move { nn.message_loop().await }.in_span(msg_loop_span));

        let validated_loop_span = Span::enter_with_local_parent("validated shreds loop");
        let nn = node.clone();
        let validated_loop = tokio::spawn(
            async move { nn.validated_shreds_loop(validated_shreds_rx).await }
                .in_span(validated_loop_span),
        );

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
        validated_loop.abort();
        standstill_loop.abort();
        prod_loop.abort();

        let (msg_res, validated_res, prod_res) =
            tokio::join!(msg_loop, validated_loop, prod_loop);
        msg_res??;
        validated_res??;
        prod_res??;
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
    /// [`Disseminator`]: Hands incoming shreds to the parallel [`ShredVerifier`];
    /// successfully verified shreds are then processed in [`Self::validated_shreds_loop`].
    async fn message_loop(self: &Arc<Self>) -> Result<()> {
        loop {
            tokio::select! {
                // handle incoming votes and certificates
                res = self.all2all.receive() => self.handle_all2all_message(res?).await,
                // hand shreds off to the verify stage
                res = self.disseminator.receive() => self.shred_verifier.submit(res?).await,

                () = self.cancel_token.cancelled() => return Ok(()),
            };
        }
    }

    /// Consumes shreds emitted by the [`ShredVerifier`] stage and runs the
    /// per-shred forward + blockstore ingest steps.
    async fn validated_shreds_loop(
        self: &Arc<Self>,
        mut rx: mpsc::Receiver<ValidatedShred>,
    ) -> Result<()> {
        loop {
            tokio::select! {
                Some(shred) = rx.recv() => self.handle_validated_shred(shred).await?,
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
                self.pool.read().await.recover_from_standstill().await;
                last_progress = Instant::now();
            }
            tokio::time::sleep(DELTA_BLOCK).await;
        }
    }

    #[fastrace::trace(short_name = true)]
    async fn handle_all2all_message(&self, msg: ConsensusMessage) {
        trace!("received all2all msg: {msg:?}");
        match msg {
            ConsensusMessage::Vote(v) => match self.pool.write().await.add_vote(v).await {
                Ok(()) => {}
                Err(AddVoteError::Slashable(offence)) => {
                    warn!("slashable offence detected: {offence}");
                }
                Err(err) => trace!("ignoring invalid vote: {err}"),
            },
            ConsensusMessage::Cert(c) => match self.pool.write().await.add_cert(c).await {
                Ok(()) => {}
                Err(err) => trace!("ignoring invalid cert: {err}"),
            },
        }
    }

    #[fastrace::trace(short_name = true)]
    #[hotpath::measure]
    async fn handle_validated_shred(&self, shred: ValidatedShred) -> std::io::Result<()> {
        // potentially forward shred
        self.disseminator.forward(validated.as_shred()).await?;

        // if we are the leader, we already have the shred
        if self.epoch_info.epoch_info().leader(slot).id == self.epoch_info.own_id() {
            return Ok(());
        }

        // otherwise, ingest into blockstore
        let res = self
            .blockstore
            .write()
            .await
            .add_shred_from_dissemination(validated)
            .await;
        if let Ok(Some(block_info)) = res {
            let mut guard = self.pool.write().await;
            let block_id = (slot, block_info.hash);
            guard.add_block(block_id, block_info.parent).await;
        }
        Ok(())
    }
}
