// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parallel shred signature verification stage.
//!
//! Sits between the network receive path and the consumers (Rotor relay
//! forwarding, blockstore ingest). Raw [`Shred`]s are submitted via
//! [`ShredVerifier::submit`] and distributed round-robin across a fixed pool of
//! worker tasks. Each worker runs the CPU-bound [`ValidatedShred::try_new`] on
//! tokio's blocking pool (via [`tokio::task::spawn_blocking`]) so signature
//! checks don't occupy the async worker threads shared with the rest of the
//! node; concurrent verifications are bounded by the worker count. Successfully
//! verified shreds are emitted on the receiver returned from
//! [`ShredVerifier::spawn`]. Shreds with bad signatures are dropped silently.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use tokio::sync::mpsc;
use tokio_util::sync::CancellationToken;

use crate::consensus::ValidatorEpochInfo;
use crate::shredder::{Shred, ValidatedShred};

/// Number of worker tasks running shred signature verification in parallel.
pub const NUM_VERIFY_WORKERS: usize = 4;

/// Bound on each worker's input queue and on the verified-shred output queue.
const VERIFY_QUEUE_SIZE: usize = 1024;

/// A pool of worker tasks that verify [`Shred`] signatures in parallel.
///
/// See the module-level docs for the overall pipeline shape.
pub struct ShredVerifier {
    /// Per-worker input channels. Shreds submitted via [`Self::submit`] are
    /// round-robin'd across these.
    worker_txs: Vec<mpsc::Sender<Shred>>,
    /// Round-robin counter for `submit`.
    next: AtomicUsize,
}

impl ShredVerifier {
    /// Spawns `num_workers` verifier tasks and returns the verifier handle
    /// together with the receiver downstream consumers should pull verified
    /// shreds from.
    pub fn spawn(
        num_workers: usize,
        epoch_info: Arc<ValidatorEpochInfo>,
        cancel_token: CancellationToken,
    ) -> (Self, mpsc::Receiver<ValidatedShred>) {
        assert!(num_workers > 0);
        let (output_tx, output_rx) = mpsc::channel(VERIFY_QUEUE_SIZE);
        let mut worker_txs = Vec::with_capacity(num_workers);
        for _ in 0..num_workers {
            let (input_tx, input_rx) = mpsc::channel(VERIFY_QUEUE_SIZE);
            worker_txs.push(input_tx);
            let output_tx = output_tx.clone();
            let epoch_info = epoch_info.clone();
            let cancel_token = cancel_token.clone();
            tokio::spawn(
                async move { Self::worker(input_rx, output_tx, epoch_info, cancel_token).await },
            );
        }
        let verifier = Self {
            worker_txs,
            next: AtomicUsize::new(0),
        };
        (verifier, output_rx)
    }

    /// Submits a shred for verification. Awaits if the chosen worker's queue
    /// is full (bounded backpressure to the caller).
    pub async fn submit(&self, shred: Shred) {
        let i = self.next.fetch_add(1, Ordering::Relaxed) % self.worker_txs.len();
        // Send failures only occur if the worker task has terminated, which only
        // happens on shutdown; drop the shred in that case.
        let _ = self.worker_txs[i].send(shred).await;
    }

    async fn worker(
        mut input_rx: mpsc::Receiver<Shred>,
        output_tx: mpsc::Sender<ValidatedShred>,
        epoch_info: Arc<ValidatorEpochInfo>,
        cancel_token: CancellationToken,
    ) {
        loop {
            tokio::select! {
                res = input_rx.recv() => {
                    let Some(shred) = res else { break };
                    let slot = shred.payload().header.slot;
                    let leader_pk = epoch_info.epoch_info().leader(slot).pubkey;
                    // Run the CPU-bound signature verification on the blocking pool
                    // rather than inline, so it does not occupy tokio's async worker
                    // threads (shared with the latency-sensitive consensus tasks).
                    // Each worker awaits its own verification before pulling the next
                    // shred, so the number of concurrent blocking jobs is bounded by
                    // the worker count.
                    let verified = tokio::task::spawn_blocking(move || {
                        ValidatedShred::try_new(shred, None, &leader_pk).ok()
                    })
                    .await;
                    match verified {
                        // verified successfully -> forward downstream
                        Ok(Some(validated)) => {
                            if output_tx.send(validated).await.is_err() {
                                break;
                            }
                        }
                        // bad signature -> drop silently
                        Ok(None) => {}
                        // join error (panic or runtime shutdown) -> stop the worker
                        Err(_) => break,
                    }
                }
                () = cancel_token.cancelled() => break,
            }
        }
    }
}
