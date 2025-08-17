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

mod blockstore;
mod cert;
mod epoch_info;
mod pool;
mod produce_block;
mod vote;
pub(crate) mod votor;

use std::marker::{Send, Sync};
use std::time::Instant;
use std::{sync::Arc, time::Duration};

use color_eyre::Result;
use either::Either;
use fastrace::Span;
use fastrace::future::FutureExt;
use log::{debug, trace, warn};
use tokio::sync::{RwLock, mpsc};
use tokio::time::sleep;
use tokio_util::sync::CancellationToken;

use crate::crypto::{Hash, aggsig, signature};
use crate::network::{Network, NetworkError, NetworkMessage};
use crate::repair::{Repair, RepairMessage};
use crate::shredder::Shred;
use crate::{All2All, Disseminator, Slot, ValidatorInfo};

pub use blockstore::{BlockInfo, Blockstore};
pub use cert::Cert;
pub use epoch_info::EpochInfo;
pub use pool::{AddVoteError, Pool};
pub use vote::Vote;
use votor::Votor;

/// Time bound assumed on network transmission delays during periods of synchrony.
const DELTA: Duration = Duration::from_millis(250);
/// Time the leader has for producing and sending the block.
const DELTA_BLOCK: Duration = Duration::from_millis(400);
/// Base timeout for when leader's first slice should arrive if they sent it immediately.
const DELTA_TIMEOUT: Duration = DELTA.checked_mul(3).unwrap();
/// Timeout for standstill detection mechanism.
const DELTA_STANDSTILL: Duration = Duration::from_millis(10_000);

/// Alpenglow consensus protocol implementation.
pub struct Alpenglow<A: All2All, D: Disseminator, R: Network, T: Network> {
    /// Own validator's secret key (used e.g. for block production).
    /// This is not the same as the voting secret key, which is held by [`Votor`].
    secret_key: signature::SecretKey,
    /// Other validators' info.
    epoch_info: Arc<EpochInfo>,

    /// Blockstore for storing raw block data.
    blockstore: Arc<RwLock<Blockstore>>,
    /// Pool of votes and certificates.
    pool: Arc<RwLock<Pool>>,

    /// All-to-all broadcast network protocol for consensus messages.
    all2all: Arc<A>,
    /// Block dissemination network protocol for shreds.
    disseminator: Arc<D>,
    /// Block repair protocol.
    repair: Arc<Repair<R>>,
    /// Network connection to receive transactions from clients.
    txs_receiver: T,

    /// Indicates whether the node is shutting down.
    cancel_token: CancellationToken,
    /// Votor task handle.
    votor_handle: tokio::task::JoinHandle<()>,
}

/// Waits for first slot in the given window to become ready for block production.
///
/// Ready here can mean:
/// - Pool emitted the `ParentReady` event for it, OR
/// - the blockstore has stored a canonical block for the previous slot.
///
/// If the slot became ready, returns `Some((parent_slot, parent_hash, is_parent-ready))`.
/// Else returns `None` if the window should be skipped.
async fn wait_for_first_slot(
    pool: Arc<RwLock<Pool>>,
    blockstore: Arc<RwLock<Blockstore>>,
    first_slot_in_window: Slot,
) -> Option<(Slot, Hash, bool)> {
    if first_slot_in_window.is_genesis_window() {
        return Some((Slot::new(0), Hash::default(), false));
    }

    let last_slot_in_window = first_slot_in_window.last_slot_in_window();

    // if already have parent ready, return it, otherwise get a channel to await on
    let rx = {
        let mut guard = pool.write().await;
        match guard.wait_for_parent_ready(first_slot_in_window) {
            Either::Left((slot, hash)) => {
                return Some((slot, hash, true));
            }
            Either::Right(rx) => rx,
        }
    };

    // Concurrently wait for:
    // - `ParentReady` event,
    // - canonical block reconstruction in blockstore, OR
    // - notification that a later slot was finalized.
    tokio::select! {
        res = rx => {
            let (slot, hash) = res.expect("Sender dropped channel.");
            Some((slot, hash, true))
        }

        res = async {
            let handle = tokio::spawn(async move {
                // PERF: These are burning a CPU. Can we use async here?
                loop {
                    let last_slot_in_prev_window = first_slot_in_window.prev();
                    if let Some(hash) = blockstore
                        .read()
                        .await
                        .canonical_block_hash(last_slot_in_prev_window)
                    {
                        debug!(
                            "optimistically building block on parent {} in slot {}",
                            &hex::encode(hash)[..8],
                            last_slot_in_prev_window,
                        );
                        return Some((last_slot_in_prev_window, hash, false));
                    }
                    if pool.read().await.finalized_slot() >= last_slot_in_window {
                        warn!(
                            "ignoring window {first_slot_in_window}..{last_slot_in_window} for block production"
                        );
                        return None;
                    }
                    sleep(Duration::from_millis(1)).await;
                }
            });
            handle.await.expect("Error in task")
        } => {
            res
        }
    }
}

impl<A, D, R, T> Alpenglow<A, D, R, T>
where
    A: All2All + Sync + Send + 'static,
    D: Disseminator + Sync + Send + 'static,
    R: Network + Sync + Send + 'static,
    T: Network + Sync + Send + 'static,
{
    /// Creates a new Alpenglow consensus node.
    #[must_use]
    pub fn new(
        secret_key: signature::SecretKey,
        voting_secret_key: aggsig::SecretKey,
        all2all: A,
        disseminator: D,
        repair_network: R,
        epoch_info: Arc<EpochInfo>,
        txs_receiver: T,
    ) -> Self {
        let cancel_token = CancellationToken::new();
        let (votor_tx, votor_rx) = mpsc::channel(1024);
        let (repair_tx, repair_rx) = mpsc::channel(1024);
        let all2all = Arc::new(all2all);

        let blockstore = Blockstore::new(epoch_info.clone(), votor_tx.clone());
        let blockstore = Arc::new(RwLock::new(blockstore));
        let pool = Pool::new(epoch_info.clone(), votor_tx.clone(), repair_tx.clone());
        let pool = Arc::new(RwLock::new(pool));
        let repair = Repair::new(
            Arc::clone(&blockstore),
            Arc::clone(&pool),
            repair_network,
            (repair_tx, repair_rx),
            epoch_info.clone(),
        );
        let repair = Arc::new(repair);

        let r = Arc::clone(&repair);
        let _repair_handle = tokio::spawn(
            async move { r.repair_loop().await }
                .in_span(Span::enter_with_local_parent("repair loop")),
        );

        let mut votor = Votor::new(
            epoch_info.own_id,
            voting_secret_key,
            votor_tx.clone(),
            votor_rx,
            all2all.clone(),
        );
        let votor_handle = tokio::spawn(
            async move { votor.voting_loop().await.unwrap() }
                .in_span(Span::enter_with_local_parent("voting loop")),
        );

        Self {
            secret_key,
            epoch_info,
            blockstore,
            pool,
            all2all,
            disseminator: Arc::new(disseminator),
            repair,
            cancel_token,
            votor_handle,
            txs_receiver,
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
        let nn = node.clone();
        let prod_loop = tokio::spawn(
            async move { nn.block_production_loop().await }.in_span(block_production_span),
        );

        node.cancel_token.cancelled().await;
        node.votor_handle.abort();
        msg_loop.abort();
        standstill_loop.abort();
        prod_loop.abort();

        let (msg_res, prod_res) = tokio::join!(msg_loop, prod_loop);
        msg_res??;
        prod_res??;
        Ok(())
    }

    pub fn get_info(&self) -> &ValidatorInfo {
        self.epoch_info.validator(self.epoch_info.own_id)
    }

    pub fn get_pool(&self) -> Arc<RwLock<Pool>> {
        Arc::clone(&self.pool)
    }

    pub fn get_cancel_token(&self) -> CancellationToken {
        self.cancel_token.clone()
    }

    /// Handles incoming messages on all the different network interfaces.
    ///
    /// [`All2All`]: Handles incoming votes and certificates. Adds them to the [`Pool`].
    /// [`Disseminator`]: Handles incoming shreds. Adds them to the [`Blockstore`].
    /// [`Repair`]: Answers incoming repair requests.
    async fn message_loop(self: &Arc<Self>) -> Result<()> {
        loop {
            tokio::select! {
                // handle incoming votes and certificates
                res = self.all2all.receive() => self.handle_all2all_message(res?).await?,
                // handle shreds received by block dissemination protocol
                res = self.disseminator.receive() => self.handle_disseminator_shred(res?).await?,
                // handle repair requests
                res = self.repair.receive() => self.handle_repair_message(res?).await?,

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

    /// Handles the leader side of the consensus protocol.
    ///
    /// Once all previous blocks have been notarized or skipped and the next
    /// slot belongs to our leader window, we will produce a block.
    async fn block_production_loop(&self) -> Result<()> {
        for first_slot_in_window in Slot::windows() {
            if self.cancel_token.is_cancelled() {
                break;
            }

            let last_slot_in_window = first_slot_in_window.last_slot_in_window();

            // don't do anything if we are not the leader
            let leader = self.epoch_info.leader(first_slot_in_window);
            if leader.id != self.epoch_info.own_id {
                continue;
            }

            if self.pool.read().await.finalized_slot() >= last_slot_in_window {
                warn!(
                    "ignoring window {first_slot_in_window}..{last_slot_in_window} for block production"
                );
                continue;
            }

            let (parent, parent_hash, mut parent_ready) = match wait_for_first_slot(
                self.pool.clone(),
                self.blockstore.clone(),
                first_slot_in_window,
            )
            .await
            {
                Some(res) => res,
                None => continue,
            };

            // produce blocks for all slots in window
            let mut block = parent;
            let mut block_hash = parent_hash;
            for slot in first_slot_in_window.slots_in_window() {
                if slot.is_genesis() {
                    parent_ready = true;
                    continue;
                }
                self.produce_block(slot, (block, block_hash), parent_ready)
                    .await?;

                // build off own block next
                block = slot;
                block_hash = self
                    .blockstore
                    .read()
                    .await
                    .canonical_block_hash(slot)
                    .expect("missing own block during block production");
                parent_ready = true;
            }
        }

        Ok(())
    }

    #[fastrace::trace(short_name = true)]
    async fn handle_all2all_message(&self, msg: NetworkMessage) -> Result<(), NetworkError> {
        trace!("received all2all msg: {msg:?}");
        match msg {
            NetworkMessage::Vote(v) => match self.pool.write().await.add_vote(v).await {
                Ok(()) => {}
                Err(AddVoteError::Slashable(offence)) => {
                    warn!("slashable offence detected: {offence}");
                }
                Err(err) => trace!("ignoring invalid vote: {err}"),
            },
            NetworkMessage::Cert(c) => match self.pool.write().await.add_cert(c).await {
                Ok(()) => {}
                Err(err) => trace!("ignoring invalid cert: {err}"),
            },
            msg => warn!("unexpected message on all2all port: {msg:?}"),
        }
        Ok(())
    }

    #[fastrace::trace(short_name = true)]
    async fn handle_disseminator_shred(&self, shred: Shred) -> Result<(), NetworkError> {
        self.disseminator.forward(&shred).await?;
        let b = self
            .blockstore
            .write()
            .await
            .add_shred_from_disseminator(shred)
            .await;
        if let Ok(Some((slot, block_info))) = b {
            let mut guard = self.pool.write().await;
            guard.add_block(slot, block_info).await;
        }
        Ok(())
    }

    async fn handle_repair_message(&self, msg: RepairMessage) -> Result<(), NetworkError> {
        match msg {
            RepairMessage::Request(request) => {
                self.repair.answer_request(request).await?;
            }
            RepairMessage::Response(resposne) => {
                self.repair.handle_response(resposne).await;
            }
        }
        Ok(())
    }
}
