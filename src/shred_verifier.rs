// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parallel shred signature verification stage.
//!
//! Sits between the network receive path and the consumers (Rotor relay
//! forwarding, blockstore ingest). Raw [`Shred`]s are submitted via
//! [`ShredVerifier::submit`] and verified concurrently: each shred is dispatched
//! to tokio's blocking pool (via [`tokio::task::spawn_blocking`]) so the
//! CPU-bound signature check does not occupy the async worker threads shared
//! with the latency-sensitive consensus tasks. The number of in-flight
//! verifications is bounded by a semaphore, providing backpressure to the
//! caller. Successfully verified shreds are emitted on the receiver returned
//! from [`ShredVerifier::spawn`]; shreds with bad signatures are dropped
//! silently.

use std::sync::Arc;

use tokio::sync::{Semaphore, mpsc};
use tokio_util::sync::CancellationToken;

use crate::consensus::ValidatorEpochInfo;
use crate::shredder::{Shred, ValidatedShred};

/// Maximum number of shred verifications running concurrently on the blocking pool.
pub(crate) const MAX_CONCURRENT_VERIFICATIONS: usize = 4;

/// Bound on the input queue and on the verified-shred output queue.
const VERIFY_QUEUE_SIZE: usize = 256;

/// Verifies [`Shred`] signatures concurrently on tokio's blocking pool.
///
/// See the module-level docs for the overall pipeline shape.
pub(crate) struct ShredVerifier {
    /// Channel into the verification stage. Shreds submitted via [`Self::submit`]
    /// are dispatched to the blocking pool by the stage's dispatch task.
    input_tx: mpsc::Sender<Shred>,
}

impl ShredVerifier {
    /// Spawns the verification stage and returns the verifier handle together
    /// with the receiver downstream consumers should pull verified shreds from.
    ///
    /// At most `max_concurrent` verifications run in parallel.
    pub(crate) fn spawn(
        max_concurrent: usize,
        epoch_info: Arc<ValidatorEpochInfo>,
        cancel_token: CancellationToken,
    ) -> (Self, mpsc::Receiver<ValidatedShred>) {
        assert!(max_concurrent > 0);
        let (input_tx, input_rx) = mpsc::channel(VERIFY_QUEUE_SIZE);
        let (output_tx, output_rx) = mpsc::channel(VERIFY_QUEUE_SIZE);
        tokio::spawn(Self::dispatch(
            max_concurrent,
            input_rx,
            output_tx,
            epoch_info,
            cancel_token,
        ));
        (Self { input_tx }, output_rx)
    }

    /// Submits a shred for verification. Awaits if the stage is at capacity
    /// (bounded backpressure to the caller).
    pub(crate) async fn submit(&self, shred: Shred) {
        // The send only fails once the stage has shut down (input channel
        // closed), which happens on node shutdown; drop the shred in that case.
        let _ = self.input_tx.send(shred).await;
    }

    /// Pulls submitted shreds and dispatches each to the blocking pool for
    /// verification, bounding concurrency with a semaphore. Runs until the
    /// input channel closes or the node shuts down.
    async fn dispatch(
        max_concurrent: usize,
        mut input_rx: mpsc::Receiver<Shred>,
        output_tx: mpsc::Sender<ValidatedShred>,
        epoch_info: Arc<ValidatorEpochInfo>,
        cancel_token: CancellationToken,
    ) {
        let semaphore = Arc::new(Semaphore::new(max_concurrent));
        loop {
            let shred = tokio::select! {
                res = input_rx.recv() => match res {
                    Some(shred) => shred,
                    None => break,
                },
                () = cancel_token.cancelled() => break,
            };
            // Wait for a free verification slot, racing shutdown so a saturated
            // blocking pool can't pin the stage past cancellation.
            let permit = tokio::select! {
                res = semaphore.clone().acquire_owned() => {
                    res.expect("semaphore is never closed")
                }
                () = cancel_token.cancelled() => break,
            };
            let epoch_info = epoch_info.clone();
            let output_tx = output_tx.clone();
            // A panic during verification is isolated to this blocking task and
            // surfaces as a single dropped shred (recoverable via repair); it
            // does not strand a worker or shrink the stage's capacity.
            tokio::task::spawn_blocking(move || {
                let _permit = permit;
                if let Some(validated) = Self::verify(&epoch_info, shred) {
                    let _ = output_tx.blocking_send(validated);
                }
            });
        }
    }

    /// Verifies a single shred's signature against the slot leader's key,
    /// returning `None` (dropping the shred) if verification fails.
    fn verify(epoch_info: &ValidatorEpochInfo, shred: Shred) -> Option<ValidatedShred> {
        let slot = shred.payload().header.slot;
        ValidatedShred::try_new(shred, None, epoch_info.leader_pubkey(slot)).ok()
    }
}

#[cfg(test)]
mod tests {
    use std::net::SocketAddr;
    use std::time::Duration;

    use rand::rng;

    use super::*;
    use crate::consensus::EpochInfo;
    use crate::crypto::{aggsig, signature};
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
    use crate::types::slice::create_slice_with_invalid_txs;
    use crate::{Stake, ValidatorId, ValidatorInfo};

    /// Builds an epoch with a single validator (and therefore a single leader
    /// for every slot) whose signing key is `leader_pk`.
    fn single_leader_epoch(leader_pk: signature::PublicKey) -> Arc<ValidatorEpochInfo> {
        let addr: SocketAddr = "127.0.0.1:0".parse().unwrap();
        let validator = ValidatorInfo {
            id: ValidatorId::new(0),
            stake: Stake::new(1),
            pubkey: leader_pk,
            voting_pubkey: aggsig::SecretKey::new(&mut rng()).to_pk(),
            all2all_address: addr,
            disseminator_address: addr,
            repair_request_address: addr,
            repair_response_address: addr,
        };
        let epoch = EpochInfo::new(vec![validator]);
        Arc::new(ValidatorEpochInfo::new(ValidatorId::new(0), epoch))
    }

    /// Creates a single shred signed by `sk`.
    fn random_shred(sk: &signature::SecretKey) -> Shred {
        let mut shredder = RegularShredder::default();
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE - 16);
        let shreds = shredder.shred(slice, sk).unwrap();
        shreds[shreds.len() - 1].clone().into_shred()
    }

    /// A shred signed by the slot leader is emitted; one signed by another key
    /// is dropped silently.
    #[tokio::test]
    async fn emits_valid_drops_invalid() {
        let mut rng = rng();
        let leader_sk = signature::SecretKey::new(&mut rng);
        let other_sk = signature::SecretKey::new(&mut rng);
        let cancel = CancellationToken::new();
        let (verifier, mut rx) = ShredVerifier::spawn(
            MAX_CONCURRENT_VERIFICATIONS,
            single_leader_epoch(leader_sk.to_pk()),
            cancel,
        );

        let valid = random_shred(&leader_sk);
        let invalid = random_shred(&other_sk);
        let valid_root = valid.merkle_root();

        verifier.submit(invalid).await;
        verifier.submit(valid).await;

        let out = tokio::time::timeout(Duration::from_secs(5), rx.recv())
            .await
            .expect("verify stage timed out")
            .expect("expected a verified shred");
        assert_eq!(out.merkle_root(), &valid_root);

        // Closing the input drains the stage; the invalid shred was dropped, so
        // nothing else is emitted.
        drop(verifier);
        let next = tokio::time::timeout(Duration::from_secs(5), rx.recv())
            .await
            .expect("verify stage timed out");
        assert!(next.is_none());
    }

    /// Cancelling the token shuts the stage down even while the handle is held.
    #[tokio::test]
    async fn shuts_down_on_cancel() {
        let leader_sk = signature::SecretKey::new(&mut rng());
        let cancel = CancellationToken::new();
        let (_verifier, mut rx) = ShredVerifier::spawn(
            MAX_CONCURRENT_VERIFICATIONS,
            single_leader_epoch(leader_sk.to_pk()),
            cancel.clone(),
        );

        cancel.cancel();

        let res = tokio::time::timeout(Duration::from_secs(5), rx.recv())
            .await
            .expect("verify stage timed out");
        assert!(res.is_none());
    }
}
