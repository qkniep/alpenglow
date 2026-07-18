// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Block repair sub-protocol.
//!
//! This module implements the double-Merkle based block repair protocol.
//! It uses the fact that the block hash is the root of a Merkle tree, where
//! the leaves of this tree are the Merkle roots of each of the block's slices.
//! Each repair response is accompanied by a Merkle proof and can thus be
//! individually verified.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap, HashSet};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use log::{debug, trace, warn};
use tokio::sync::{mpsc, oneshot};
use wincode::{SchemaRead, SchemaWrite};

use crate::consensus::core::Input;
use crate::consensus::{BlockstoreImpl, DELTA, ValidatorEpochInfo};
use crate::crypto::merkle::{DoubleMerkleProof, DoubleMerkleTree, SliceRoot};
use crate::crypto::{Hash, hash};
use crate::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use crate::network::{Network, RepairRequesterNetwork, RepairResponderNetwork};
use crate::shredder::{Shred, ShredIndex, ValidatedShred};
use crate::types::SliceIndex;
use crate::{BlockId, ValidatorIndex};

/// Maximum time to wait for a response to a repair request.
///
/// After a request times out we retry it from another node.
const REPAIR_TIMEOUT: Duration = DELTA.checked_mul(2).unwrap();

/// Different types of [`RepairRequest`] messages.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub enum RepairRequestType {
    /// Request for the total number of slices in block with a given hash.
    LastSliceRoot(BlockId),
    /// Request for the root hash of a slice, identified by block hash and slice index.
    SliceRoot(BlockId, SliceIndex),
    /// Request for shred, identified by block hash, slice index and shred index.
    Shred(BlockId, SliceIndex, ShredIndex),
}

impl RepairRequestType {
    /// Digests the [`RepairRequestType`] into a [`crate::crypto::Hash`].
    fn hash(&self) -> Hash {
        let repair = RepairRequest {
            req_type: self.clone(),
            sender: ValidatorIndex::new(0),
        };
        let msg_bytes = crate::serialize(&repair);
        hash(&msg_bytes)
    }
}

/// Request messages for the repair sub-protocol.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub struct RepairRequest {
    /// The validator that sent the message.
    sender: ValidatorIndex,
    /// The type of repair message sent.
    req_type: RepairRequestType,
}

impl RepairRequest {
    /// The validator that sent this request.
    #[must_use]
    pub(crate) fn sender(&self) -> ValidatorIndex {
        self.sender
    }

    /// Builds a response to this request from `blockstore`.
    ///
    /// Returns the requested data if the blockstore holds it, otherwise a
    /// [`RepairResponse::Nack`] so the requester can immediately try another
    /// peer. Called by [`crate::consensus`]'s core, which owns the blockstore.
    #[must_use]
    pub(crate) fn build_response(&self, blockstore: &BlockstoreImpl) -> RepairResponse {
        self.try_build_response(blockstore)
            .unwrap_or_else(|| RepairResponse::Nack(self.req_type.clone()))
    }

    /// Tries to build a positive response for this request.
    ///
    /// Returns `None` if the requested data is not available in the blockstore.
    fn try_build_response(&self, blockstore: &BlockstoreImpl) -> Option<RepairResponse> {
        match &self.req_type {
            RepairRequestType::LastSliceRoot(block_id) => {
                let last_slice = blockstore.get_last_slice_index(block_id)?;
                let root = blockstore.get_slice_root(block_id, last_slice)?;
                let proof = blockstore.create_double_merkle_proof(block_id, last_slice)?;
                Some(RepairResponse::LastSliceRoot(
                    self.req_type.clone(),
                    last_slice,
                    root,
                    proof,
                ))
            }
            RepairRequestType::SliceRoot(block_id, slice) => {
                let root = blockstore.get_slice_root(block_id, *slice)?;
                let proof = blockstore.create_double_merkle_proof(block_id, *slice)?;
                Some(RepairResponse::SliceRoot(
                    self.req_type.clone(),
                    root,
                    proof,
                ))
            }
            RepairRequestType::Shred(block_id, slice, shred_index) => {
                let shred = blockstore
                    .get_shred(block_id, *slice, *shred_index)
                    .cloned()?;
                Some(RepairResponse::Shred(
                    self.req_type.clone(),
                    shred.into_shred(),
                ))
            }
        }
    }

    /// Constructs a request as if received from `sender`; for tests only.
    #[cfg(test)]
    pub(crate) fn new_for_test(sender: ValidatorIndex, req_type: RepairRequestType) -> Self {
        Self { sender, req_type }
    }
}

/// Response messages for the repair sub-protocol.
///
/// Each response type corresponds to a specific request message type.
/// Each response contains the request message that it is a response to.
/// If well-formed, it thus contains the corresponding variant of [`RepairRequest`].
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub enum RepairResponse {
    /// Response with the last slice's Merkle root hash, plus corresponding proof.
    LastSliceRoot(RepairRequestType, SliceIndex, SliceRoot, DoubleMerkleProof),
    /// Response with the Merkle root hash of a specific slice, plus corresponding proof.
    SliceRoot(RepairRequestType, SliceRoot, DoubleMerkleProof),
    /// Response with a specific shred.
    Shred(RepairRequestType, Shred),
    /// Negative acknowledgment indicating the requested data cannot be served.
    ///
    /// Sent when a node cannot fulfil a repair request.
    /// This lets the requester immediately try another peer instead of waiting for a timeout.
    Nack(RepairRequestType),
}

impl RepairResponse {
    /// Returns a reference to the [`RepairRequestType`] that this response corresponds to.
    #[must_use]
    const fn request_type(&self) -> &RepairRequestType {
        match self {
            Self::LastSliceRoot(req_type, _, _, _)
            | Self::SliceRoot(req_type, _, _)
            | Self::Shred(req_type, _)
            | Self::Nack(req_type) => req_type,
        }
    }
}

/// Handle repair requests from other nodes.
///
/// This is separated from [`Repair`] to handle repair requests and responses on separate sockets and tokio tasks.
/// The blockstore lives inside the consensus core, so this handler forwards each
/// (validated) request to the core as an `Input::RepairRequest` and writes the
/// core's reply back to the requesting peer.
///
/// NOTE: serving requests now shares the core's single-threaded inbox with
/// consensus processing, rather than the dedicated read-lock the previous
/// design used. Repair serving is network-bound and not latency-critical, so
/// this is acceptable, but if it ever shows up in `performance_test` the core
/// could grow a priority lane for serve requests.
pub struct RepairRequestHandler<N: Network> {
    epoch_info: Arc<ValidatorEpochInfo>,
    /// Feeds validated repair requests to the consensus core.
    inputs: mpsc::Sender<Input>,
    network: N,
}

impl<N> RepairRequestHandler<N>
where
    N: RepairResponderNetwork,
{
    /// Creates a new repair request handler instance.
    ///
    /// Given `network` instance will be used for receiving repair requests and sending repair responses.
    /// Requests are answered by the consensus core, reached via `inputs`.
    pub(crate) fn new(
        epoch_info: Arc<ValidatorEpochInfo>,
        inputs: mpsc::Sender<Input>,
        network: N,
    ) -> Self {
        Self {
            epoch_info,
            inputs,
            network,
        }
    }

    /// Main loop of the repair request handler.
    ///
    /// Listens for repair requests on `self.network`, forwards each to the
    /// consensus core, and sends the core's reply back to the requester.
    pub async fn run(&self) {
        loop {
            let request = match self.network.receive().await {
                Ok(req) => req,
                Err(err) => {
                    warn!("receiving repair request failed: {err}");
                    continue;
                }
            };
            if let Err(err) = self.answer_request(request).await {
                warn!("answering repair request failed: {err}");
            }
        }
    }

    /// Answers a repair request by asking the core to build a response.
    ///
    /// The core reads its blockstore and replies (with the data or a
    /// [`RepairResponse::Nack`]) on a oneshot channel; the reply is then written
    /// to the requesting peer's socket.
    #[hotpath::measure]
    async fn answer_request(&self, request: RepairRequest) -> std::io::Result<()> {
        trace!("answering repair request: {request:?}");

        // drop requests from validators outside the current epoch's set,
        // otherwise `validator()` indexing in `send_response` would panic on byzantine input
        let epoch = self.epoch_info.epoch_info();
        if request.sender().as_usize() >= epoch.validators().len() {
            warn!(
                "dropping repair request from unknown validator {:?}",
                request.sender()
            );
            return Ok(());
        }
        let sender = request.sender();

        let (reply, reply_rx) = oneshot::channel();
        if self
            .inputs
            .send(Input::RepairRequest { request, reply })
            .await
            .is_err()
        {
            debug!("consensus core inbox closed, dropping repair request");
            return Ok(());
        }
        let Ok(response) = reply_rx.await else {
            debug!("consensus core dropped repair reply, node shutting down");
            return Ok(());
        };
        self.send_response(response, sender).await
    }

    #[hotpath::measure]
    async fn send_response(
        &self,
        response: RepairResponse,
        validator: ValidatorIndex,
    ) -> std::io::Result<()> {
        let to = self
            .epoch_info
            .epoch_info()
            .validator(validator)
            .repair_requester_address;
        self.network.send(&response, to).await
    }
}

/// Instance of double-Merkle based block repair protocol.
///
/// This is used by the node to repair blocks that it is missing.
/// This does not answer repair requests from other nodes, that is handled by [`RepairRequestHandler`].
pub struct Repair<N: Network> {
    slice_roots: BTreeMap<(BlockId, SliceIndex), SliceRoot>,
    outstanding_requests: BTreeMap<Hash, RepairRequestType>,
    /// Expiry times of outstanding requests, earliest first (min-heap via [`Reverse`]).
    request_timeouts: BinaryHeap<Reverse<(Instant, Hash)>>,
    network: N,
    sampler: StakeWeightedSampler,
    epoch_info: Arc<ValidatorEpochInfo>,
    /// Feeds repaired shreds to the consensus core.
    inputs: mpsc::Sender<Input>,
}

impl<N> Repair<N>
where
    N: RepairRequesterNetwork,
{
    /// Creates a new repair instance.
    ///
    /// Given `network` will be used for sending repair requests and receiving
    /// repair responses. Repaired shreds are fed to the consensus core via
    /// `inputs`, which owns the blockstore they are written into.
    pub(crate) fn new(
        network: N,
        epoch_info: Arc<ValidatorEpochInfo>,
        inputs: mpsc::Sender<Input>,
    ) -> Self {
        let validators = epoch_info.epoch_info().validators().to_vec();
        let sampler = StakeWeightedSampler::new(validators);
        Self {
            slice_roots: BTreeMap::new(),
            outstanding_requests: BTreeMap::new(),
            request_timeouts: BinaryHeap::new(),
            network,
            sampler,
            epoch_info,
            inputs,
        }
    }

    /// Main loop of the repair protocol.
    ///
    /// Listens to incoming requests for blocks to repair on `self.repair_channel`.
    /// Initiates the corresponding repair process and handles ongoing repairs.
    pub async fn repair_loop(&mut self, mut repair_receiver: tokio::sync::mpsc::Receiver<BlockId>) {
        loop {
            let next_timeout = self.request_timeouts.peek().map(|Reverse((t, _))| t);
            let sleep_duration = match next_timeout {
                None => std::time::Duration::MAX,
                Some(t) => t.duration_since(Instant::now()),
            };
            tokio::select! {
                // handle repair response from network
                res = self.network.receive() => match res {
                    Ok(response) => self.handle_response(response).await,
                    Err(err) => warn!("receiving repair response failed: {err}"),
                },
                // handle request for repairing new block
                Some(block_id) = repair_receiver.recv() => {
                    self.repair_block(block_id).await;
                }
                // handle next request timeout
                () = tokio::time::sleep(sleep_duration) => {
                    let Some(Reverse((_, hash))) = self.request_timeouts.pop() else {
                        continue;
                    };
                    if let Some(request) = self.outstanding_requests.remove(&hash) {
                        debug!("retrying timed-out repair request {request:?}");
                        if let Err(err) = self.send_request(request).await {
                            warn!("sending timed-out repair request failed: {err}");
                        }
                    }
                }
            }
        }
    }

    /// Starts repair process for the block specified by `slot` and `block_hash`.
    ///
    /// The core suppresses repair requests for blocks it already holds (it owns
    /// the blockstore), so this is only reached for genuinely missing blocks.
    pub async fn repair_block(&mut self, block_id: BlockId) {
        let (slot, block_hash) = &block_id;
        debug!("repairing block {} in slot {slot}", block_hash.short_hex());
        let req = RepairRequestType::LastSliceRoot(block_id);
        if let Err(err) = self.send_request(req).await {
            warn!("sending initial repair request failed: {err}");
        }
    }

    /// Handles a repair response, storing the received data.
    ///
    /// If the response contains a shred, it will be stored in the blockstore.
    /// Otherwise, metadata is stored in the [`Repair`] struct itself.
    /// Does nothing if the provided `response` is not well-formed.
    #[hotpath::measure]
    async fn handle_response(&mut self, response: RepairResponse) {
        trace!("handling repair response: {response:?}");
        let request_hash = response.request_type().hash();

        // check whether we are (still) waiting on response to this request
        let Some(_) = self.outstanding_requests.remove(&request_hash) else {
            warn!("received repair response for unknown request {response:?}");
            return;
        };

        match response {
            RepairResponse::Nack(req_type) => {
                debug!("received NACK for repair request {req_type:?}, retrying immediately");
                if let Err(err) = self.send_request(req_type).await {
                    warn!("retrying NACKed repair request failed: {err}");
                }
            }
            RepairResponse::LastSliceRoot(req_type, last_slice, root, proof) => {
                // check validity of response
                let RepairRequestType::LastSliceRoot(block_id) = &req_type else {
                    warn!("repair response (LastSliceRoot) to mismatching request {req_type:?}");
                    return;
                };
                let (_, block_hash) = block_id;
                if !DoubleMerkleTree::check_proof_last(
                    &root,
                    last_slice.inner(),
                    block_hash,
                    &proof,
                ) {
                    warn!("repair response (LastSliceRoot) with invalid proof");
                    return;
                }

                // store slice Merkle root
                self.slice_roots
                    .insert((block_id.clone(), last_slice), root);

                // issue next requests
                // TODO: do not request last slice root again
                // TODO: already requests shreds for last slice here
                for slice in last_slice.until() {
                    let req_type = RepairRequestType::SliceRoot(block_id.clone(), slice);
                    if let Err(err) = self.send_request(req_type).await {
                        warn!("sending SliceRoot repair request failed: {err}");
                    }
                }
            }
            RepairResponse::SliceRoot(req_type, root, proof) => {
                // check validity of response
                let RepairRequestType::SliceRoot(ref block_id, slice) = req_type else {
                    warn!("repair response (SliceRoot) to mismatching request {req_type:?}");
                    return;
                };
                let (_, block_hash) = block_id;
                if !DoubleMerkleTree::check_proof(&root, slice.inner(), block_hash, &proof) {
                    warn!("repair response (SliceRoot) with invalid proof");
                    return;
                }

                // store slice Merkle root
                self.slice_roots.insert((block_id.clone(), slice), root);

                // issue next requests
                // HACK: workaround for when other nodes don't have the first `DATA_SHREDS` shreds
                for shred_index in ShredIndex::all() {
                    let req = RepairRequestType::Shred(block_id.clone(), slice, shred_index);
                    if let Err(err) = self.send_request(req).await {
                        warn!("sending Shred repair request failed: {err}");
                    }
                }
            }
            RepairResponse::Shred(req_type, shred) => {
                // check validity of response
                let RepairRequestType::Shred(ref block_id, slice, index) = req_type else {
                    warn!("repair response (Shred) to mismatching request {req_type:?}");
                    return;
                };
                let (slot, block_hash) = block_id;
                if shred.payload().header.slot != *slot
                    || shred.payload().header.slice_index != slice
                    || shred.payload().shred_index != index
                {
                    warn!("repair response (Shred) for mismatching shred index");
                    return;
                }
                let Some(root) = self.slice_roots.get(&(block_id.clone(), slice)) else {
                    unreachable!("issued repair request (Shred) before knowing slice root");
                };
                let leader_pk = &self.epoch_info.epoch_info().leader(*slot).pubkey;
                // shred for the wrong slice root, don't even try to verify signature
                if &shred.slice_root() != root {
                    warn!("repair response (Shred) with slice root not matching proved slice root");
                    return;
                }
                // have no commitment cache for repair, always verify signature (i.e. `None` here)
                let Ok(validated) = ValidatedShred::try_new(shred, None, leader_pk) else {
                    warn!("repair response (Shred) with invalid Merkle proof or signature");
                    return;
                };

                // Feed the repaired shred to the consensus core, which owns the
                // blockstore and registers any completed block with the pool.
                let input = Input::RepairedShred {
                    block_hash: block_hash.clone(),
                    shred: validated,
                };
                if self.inputs.send(input).await.is_err() {
                    debug!("consensus core inbox closed, dropping repaired shred");
                }
            }
        }
    }

    #[hotpath::measure]
    async fn send_request(&mut self, req_type: RepairRequestType) -> std::io::Result<()> {
        let hash = req_type.hash();

        let expiry = Instant::now() + REPAIR_TIMEOUT;
        self.outstanding_requests
            .insert(hash.clone(), req_type.clone());
        self.request_timeouts.retain(|Reverse((_, h))| h != &hash);
        self.request_timeouts.push(Reverse((expiry, hash)));

        let request = RepairRequest {
            sender: self.epoch_info.own_id(),
            req_type,
        };
        // HACK: magic number to fix high-failure scenarios
        let mut to_all = HashSet::new();
        for _ in 0..10 {
            to_all.insert(self.pick_random_peer());
            if to_all.len() == 3 {
                break;
            }
        }
        self.network.send_to_many(&request, to_all).await?;
        Ok(())
    }

    fn pick_random_peer(&self) -> SocketAddr {
        let mut rng = rand::rng();
        let mut peer_info = self.sampler.sample_info(&mut rng);
        while peer_info.id == self.epoch_info.own_id() {
            peer_info = self.sampler.sample_info(&mut rng);
        }
        peer_info.repair_responder_address
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::time::Instant;

    use tokio::sync::Mutex;
    use tokio::sync::mpsc::Sender;

    use super::*;
    use crate::ValidatorIndex;
    use crate::consensus::EpochInfo;
    use crate::consensus::core::ConsensusCore;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::crypto::signature::SecretKey;
    use crate::network::simulated::SimulatedNetworkCore;
    use crate::network::{SimulatedNetwork, localhost_ip_sockaddr};
    use crate::shredder::TOTAL_SHREDS;
    use crate::test_utils::{create_random_shredded_block, generate_validators, random_block_id};
    use crate::types::Slot;
    use crate::types::slice_index::MAX_SLICES_PER_BLOCK;

    /// Shared handle to the consensus core driven by the repair-test harness.
    ///
    /// Stands in for production's [`crate::consensus`] driver: a background task
    /// feeds it inputs from the repair loop and request handler, and the test
    /// injects disseminated shreds or queries the blockstore through it.
    type SharedCore = Arc<Mutex<ConsensusCore>>;

    /// Test context for repair tests.
    ///
    /// Sets up a small network of 2 validators:
    /// - Validator 0: leader of the genesis window, no repair instance.
    /// - Validator 1: has repair set up, is not the leader.
    struct TestContext {
        repair_tx: Sender<BlockId>,
        /// Direct handle to the core's inbox, for injecting disseminated shreds.
        input_tx: Sender<Input>,
        /// The consensus core owning the blockstore, for assertions.
        core: SharedCore,
        /// Validator 0's network endpoint for handling repair requests
        /// (receives [`RepairRequest`] messages, sends [`RepairResponse`] messages).
        v0_request_net: SimulatedNetwork<RepairResponse, RepairRequest>,
        /// Validator 0's network endpoint for handling repair responses
        /// (sends [`RepairRequest`] messages, receives [`RepairResponse`] messages).
        v0_reply_net: SimulatedNetwork<RepairRequest, RepairResponse>,
        leader_sk: SecretKey,
    }

    async fn setup() -> TestContext {
        // create EpochInfo for 2 validators and the corresponding network
        let (_, epoch_info) = generate_validators(2);
        let leader_key = SecretKey::new(&mut rand::rng());
        let mut validators = epoch_info.validators().to_vec();
        validators[0].pubkey = leader_key.to_pk();
        validators[0].repair_requester_address = localhost_ip_sockaddr(0);
        validators[0].repair_responder_address = localhost_ip_sockaddr(1);
        validators[1].repair_requester_address = localhost_ip_sockaddr(2);
        validators[1].repair_responder_address = localhost_ip_sockaddr(3);

        let net_core = Arc::new(SimulatedNetworkCore::new(1, 0.0, 0.0));
        let v0_repair_requester_network = net_core.join_unlimited(ValidatorIndex::new(0)).await;
        let v0_repair_responder_network = net_core.join_unlimited(ValidatorIndex::new(1)).await;
        let v1_repair_requester_network = net_core.join_unlimited(ValidatorIndex::new(2)).await;
        let v1_repair_responder_network = net_core.join_unlimited(ValidatorIndex::new(3)).await;

        let epoch_info = EpochInfo::new(validators);
        let epoch_info = Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(1), epoch_info));

        // set up the consensus core (owns the blockstore) and a task that feeds
        // it inputs from the repair loop / request handler, mirroring the driver
        let voting_key = crate::crypto::aggsig::SecretKey::new(&mut rand::rng());
        let core: SharedCore = Arc::new(Mutex::new(ConsensusCore::new(
            epoch_info.clone(),
            voting_key,
            Instant::now(),
        )));
        let (input_tx, mut input_rx) = tokio::sync::mpsc::channel::<Input>(100);
        let (repair_tx, repair_rx) = tokio::sync::mpsc::channel(100);
        {
            let core = Arc::clone(&core);
            tokio::spawn(async move {
                while let Some(input) = input_rx.recv().await {
                    // outputs (repair requests, broadcasts, ...) are not needed
                    // by these tests, which drive the repair protocol directly
                    let mut out = Vec::new();
                    core.lock().await.handle(input, Instant::now(), &mut out);
                }
            });
        }

        // create and start Repair instance
        let mut repair = Repair::new(
            v1_repair_requester_network,
            epoch_info.clone(),
            input_tx.clone(),
        );
        tokio::spawn(async move {
            repair.repair_loop(repair_rx).await;
        });
        let repair_request_handler =
            RepairRequestHandler::new(epoch_info, input_tx.clone(), v1_repair_responder_network);
        tokio::spawn(async move {
            repair_request_handler.run().await;
        });
        TestContext {
            repair_tx,
            input_tx,
            core,
            v0_request_net: v0_repair_responder_network,
            v0_reply_net: v0_repair_requester_network,
            leader_sk: leader_key,
        }
    }

    #[tokio::test]
    async fn repair_tiny_block() {
        repair_block(1).await;
    }

    #[tokio::test]
    async fn repair_regular_block() {
        repair_block(10).await;
    }

    #[tokio::test]
    #[ignore = "slow in debug mode; runs in release via `just test-sequential`"]
    async fn repair_large_block() {
        repair_block(MAX_SLICES_PER_BLOCK).await;
    }

    async fn repair_block(num_slices: usize) {
        let ctx = setup().await;

        // create a block to repair
        let slot = Slot::genesis().next();
        let (block_hash, merkle_tree, shreds) =
            create_random_shredded_block(slot, num_slices, &ctx.leader_sk);
        let block_to_repair = (slot, block_hash);

        // ask repair instance to repair this block
        ctx.repair_tx.send(block_to_repair.clone()).await.unwrap();

        // expect LastSliceRoot request first
        let msg = ctx.v0_request_net.receive().await.unwrap();
        let req_type = RepairRequestType::LastSliceRoot(block_to_repair.clone());
        assert_eq!(msg.req_type, req_type);

        // answer LastSliceRoot request
        let response = RepairResponse::LastSliceRoot(
            req_type,
            SliceIndex::new_for_test(num_slices - 1),
            shreds.last().unwrap()[0].slice_root().clone(),
            merkle_tree.create_proof(num_slices - 1),
        );
        // responses go to v1's repair requester socket (joined at index 2)
        let port1 = localhost_ip_sockaddr(2);
        ctx.v0_request_net.send(&response, port1).await.unwrap();

        // expect SliceRoot requests next
        let mut slice_roots_requested = BTreeSet::new();
        while slice_roots_requested.len() < num_slices {
            let msg = ctx.v0_request_net.receive().await.unwrap();

            for slice in SliceIndex::all().take(num_slices) {
                let req_type = RepairRequestType::SliceRoot(block_to_repair.clone(), slice);
                if msg.req_type == req_type {
                    slice_roots_requested.insert(slice);
                    break;
                }
            }
        }

        // assert all other slice roots requested + answer the requests
        for slice in SliceIndex::all().take(num_slices) {
            assert!(slice_roots_requested.contains(&slice));
            let req_type = RepairRequestType::SliceRoot(block_to_repair.clone(), slice);
            let root = shreds[slice.inner()][0].slice_root().clone();
            let proof = merkle_tree.create_proof(slice.inner());
            let response = RepairResponse::SliceRoot(req_type, root, proof);
            ctx.v0_request_net.send(&response, port1).await.unwrap();

            // expect Shred requests for this slice next
            let mut shreds_requested = BTreeSet::new();
            while shreds_requested.len() < TOTAL_SHREDS {
                let msg = ctx.v0_request_net.receive().await.unwrap();
                for shred_index in ShredIndex::all() {
                    let req_type =
                        RepairRequestType::Shred(block_to_repair.clone(), slice, shred_index);
                    if msg.req_type == req_type {
                        shreds_requested.insert(shred_index);
                        break;
                    }
                }
            }

            // assert all shreds requested + answer the requests
            let slice_shreds = shreds[slice.inner()].clone();
            for (shred_index, shred) in slice_shreds.into_iter().take(TOTAL_SHREDS).enumerate() {
                let shred_index = ShredIndex::new(shred_index).unwrap();
                assert!(shreds_requested.contains(&shred_index));
                let req_type =
                    RepairRequestType::Shred(block_to_repair.clone(), slice, shred_index);
                let response = RepairResponse::Shred(req_type, shred.into_shred());
                ctx.v0_request_net.send(&response, port1).await.unwrap();
            }
        }

        // block should be repaired shortly; poll until it lands rather than
        // relying on a fixed sleep, which is racy under CI load
        let repaired = tokio::time::timeout(Duration::from_secs(10), async {
            while ctx
                .core
                .lock()
                .await
                .blockstore()
                .get_block(&block_to_repair)
                .is_none()
            {
                tokio::time::sleep(Duration::from_millis(5)).await;
            }
        })
        .await;
        assert!(repaired.is_ok(), "block was not repaired within timeout");
    }

    #[tokio::test]
    async fn oldest_timed_out_request_retried_first() {
        let ctx = setup().await;

        // ask to repair two different blocks, then never answer any requests
        let block_a = random_block_id(Slot::genesis().next());
        let block_b = random_block_id(Slot::genesis().next().next());
        ctx.repair_tx.send(block_a.clone()).await.unwrap();
        ctx.repair_tx.send(block_b.clone()).await.unwrap();

        // consume the two initial requests
        let msg = ctx.v0_request_net.receive().await.unwrap();
        let req_type_a = RepairRequestType::LastSliceRoot(block_a);
        assert_eq!(msg.req_type, req_type_a);
        let msg = ctx.v0_request_net.receive().await.unwrap();
        assert_eq!(msg.req_type, RepairRequestType::LastSliceRoot(block_b));

        // both requests time out, the one sent first must be retried first
        let msg = ctx.v0_request_net.receive().await.unwrap();
        assert_eq!(msg.req_type, req_type_a);
    }

    #[tokio::test]
    async fn unknown_sender_request_dropped() {
        let ctx = setup().await;
        let num_validators = 2;
        let block_id = (Slot::genesis().next(), GENESIS_BLOCK_HASH);

        // send a request with an out-of-bounds `sender`
        // the handler must drop it instead of panicking on `validator()` lookup
        let request = RepairRequest {
            req_type: RepairRequestType::LastSliceRoot(block_id.clone()),
            sender: ValidatorIndex::new(num_validators),
        };
        let port1 = localhost_ip_sockaddr(3);
        ctx.v0_reply_net.send(&request, port1).await.unwrap();

        // no response is expected; verify by following up with a valid request
        // and checking we get its response (proves the handler is still alive)
        let valid_request = RepairRequest {
            req_type: RepairRequestType::SliceRoot(block_id, SliceIndex::new_for_test(0)),
            sender: ValidatorIndex::new(0),
        };
        ctx.v0_reply_net.send(&valid_request, port1).await.unwrap();
        let msg = ctx.v0_reply_net.receive().await.unwrap();
        assert!(matches!(
            msg,
            RepairResponse::Nack(RepairRequestType::SliceRoot(..))
        ));
    }

    #[tokio::test]
    async fn answer_requests() {
        const SLICES: usize = 2;
        let ctx = setup().await;

        // create a block to repair
        let slot = Slot::genesis().next();
        let (block_hash, _, shreds) = create_random_shredded_block(slot, SLICES, &ctx.leader_sk);
        let block_to_repair = (slot, block_hash.clone());

        // ingest the block into the core's blockstore via the dissemination path
        for slice_shreds in shreds.clone() {
            for shred in slice_shreds {
                ctx.input_tx
                    .send(Input::DisseminatedShred(shred))
                    .await
                    .unwrap();
            }
        }
        // wait until the core has reconstructed the block (inputs are async)
        tokio::time::timeout(Duration::from_secs(10), async {
            while ctx
                .core
                .lock()
                .await
                .blockstore()
                .get_block(&block_to_repair)
                .is_none()
            {
                tokio::time::sleep(Duration::from_millis(5)).await;
            }
        })
        .await
        .expect("block should reconstruct from disseminated shreds");
        assert_eq!(
            ctx.core
                .lock()
                .await
                .blockstore()
                .disseminated_block_hash(slot),
            Some(&block_hash)
        );

        // request last slice root to learn how many slices there are
        let request = RepairRequest {
            req_type: RepairRequestType::LastSliceRoot(block_to_repair.clone()),
            sender: ValidatorIndex::new(0),
        };
        // requests go to v1's repair responder socket (joined at index 3)
        let port1 = localhost_ip_sockaddr(3);
        ctx.v0_reply_net.send(&request, port1).await.unwrap();

        // verify response
        let msg = ctx.v0_reply_net.receive().await.unwrap();
        let RepairResponse::LastSliceRoot(req_type, last_slice, root, proof) = msg else {
            panic!("not LastSliceRoot response");
        };
        assert_eq!(req_type, request.req_type);
        assert_eq!(last_slice.inner(), SLICES - 1);
        assert_eq!(&root, shreds[last_slice.inner()][0].slice_root());
        let correct_proof = ctx
            .core
            .lock()
            .await
            .blockstore()
            .create_double_merkle_proof(&block_to_repair, last_slice)
            .unwrap();
        assert_eq!(proof, correct_proof);

        // request slice roots
        for slice in SliceIndex::all().take(SLICES) {
            let request = RepairRequest {
                req_type: RepairRequestType::SliceRoot(block_to_repair.clone(), slice),
                sender: ValidatorIndex::new(0),
            };
            ctx.v0_reply_net.send(&request, port1).await.unwrap();

            // verify response
            let msg = ctx.v0_reply_net.receive().await.unwrap();
            let RepairResponse::SliceRoot(req_type, root, proof) = msg else {
                panic!("not SliceRoot response");
            };
            assert_eq!(req_type, request.req_type);
            assert_eq!(&root, shreds[slice.inner()][0].slice_root());
            let correct_proof = ctx
                .core
                .lock()
                .await
                .blockstore()
                .create_double_merkle_proof(&block_to_repair, slice)
                .unwrap();
            assert_eq!(proof, correct_proof);

            // request slice shreds
            for shred_index in ShredIndex::all() {
                let request = RepairRequest {
                    req_type: RepairRequestType::Shred(block_to_repair.clone(), slice, shred_index),
                    sender: ValidatorIndex::new(0),
                };
                ctx.v0_reply_net.send(&request, port1).await.unwrap();

                // verify response
                let msg = ctx.v0_reply_net.receive().await.unwrap();
                let RepairResponse::Shred(req_type, shred) = msg else {
                    panic!("not Shred response");
                };
                assert_eq!(req_type, request.req_type);
                assert_eq!(
                    shred.payload().data,
                    shreds[slice.inner()][*shred_index].payload().data
                );
            }
        }
    }
}
