// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Background worker that reconstructs slices off the blockstore lock.
//!
//! On the dissemination and repair ingest paths, [`super::BlockstoreImpl`] only stores
//! shreds under the lock and, when a slice becomes reconstructable, hands a
//! [`ReconstructJob`] to this worker. The worker runs the expensive Reed–Solomon decode
//! plus Merkle rebuild ([`Shredder::deshred`]) *without* holding the lock, then briefly
//! re-acquires it to commit the result and emit the resulting [`BlockstoreEvent`].

use log::trace;
use tokio::sync::mpsc::{Sender, UnboundedReceiver};

use super::{AddShredError, BlockstoreEvent, ReconstructJob, ReconstructTarget, SharedBlockstore};
use crate::consensus::SharedPool;
use crate::shredder::{RegularShredder, Shredder};

/// Reconstructs slices handed off by the blockstore, off the blockstore lock.
///
/// A single worker processes jobs sequentially, which keeps a single reusable shredder
/// and preserves per-slot ordering of emitted events for free.
pub struct ReconstructionWorker {
    /// Reused across all jobs (avoids re-allocating the Reed–Solomon coder).
    shredder: RegularShredder,
    /// Incoming reconstruction jobs from the blockstore.
    jobs: UnboundedReceiver<ReconstructJob>,
    /// Blockstore to commit reconstructed slices into.
    blockstore: SharedBlockstore,
    /// Pool, to register reconstructed blocks with.
    pool: SharedPool,
    /// Channel for forwarding [`BlockstoreEvent`]s to Votor.
    votor_channel: Sender<BlockstoreEvent>,
}

impl ReconstructionWorker {
    /// Creates a new reconstruction worker.
    pub fn new(
        blockstore: SharedBlockstore,
        pool: SharedPool,
        votor_channel: Sender<BlockstoreEvent>,
        jobs: UnboundedReceiver<ReconstructJob>,
    ) -> Self {
        Self {
            shredder: RegularShredder::default(),
            jobs,
            blockstore,
            pool,
            votor_channel,
        }
    }

    /// Runs the worker loop until the job channel is closed (i.e. on shutdown).
    pub async fn run(mut self) {
        while let Some(job) = self.jobs.recv().await {
            self.handle_job(job).await;
        }
    }

    async fn handle_job(&mut self, job: ReconstructJob) {
        let ReconstructJob {
            target,
            slice_index,
            shreds,
        } = job;
        let slot = target.slot();
        let is_disseminated = matches!(target, ReconstructTarget::Disseminated(_));

        // expensive reconstruction, off the blockstore lock
        let result = self.shredder.deshred(&shreds);

        // commit under the lock (released at the `;`)
        let event = self
            .blockstore
            .write()
            .await
            .commit_reconstructed_slice(target, slice_index, result)
            .await;

        // forward the outcome to Votor / the pool, outside the lock
        match event {
            Ok(Some(event)) => {
                // register the reconstructed block with the pool
                let block_to_add = if let BlockstoreEvent::Block { block_info, .. } = &event {
                    Some(((slot, block_info.hash.clone()), block_info.parent.clone()))
                } else {
                    None
                };
                if self.votor_channel.send(event).await.is_err() {
                    trace!("votor channel closed, dropping blockstore event");
                }
                if let Some((block_id, parent)) = block_to_add {
                    self.pool.write().await.add_block(block_id, parent).await;
                }
            }
            Ok(None) => {}
            // an invalid disseminated block must be surfaced to Votor (repair does not)
            Err(AddShredError::InvalidShred) if is_disseminated => {
                if self
                    .votor_channel
                    .send(BlockstoreEvent::InvalidBlock(slot))
                    .await
                    .is_err()
                {
                    trace!("votor channel closed, dropping blockstore event");
                }
            }
            Err(_) => {}
        }
    }
}
