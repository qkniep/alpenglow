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
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashSet, VecDeque};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use log::{debug, trace, warn};
use wincode::{SchemaRead, SchemaWrite};

use crate::consensus::{DELTA, SharedBlockstore, SharedPool, ValidatorEpochInfo};
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
const REPAIR_TIMEOUT: Duration = DELTA.saturating_mul(2);

/// Number of peers a single repair request is fanned out to in parallel.
const REPAIR_FANOUT: usize = 3;

/// How long to remember an answered request after its first accepted response.
///
/// Each request is fanned out to up to [`REPAIR_FANOUT`] peers and retried on timeout,
/// so the same request is typically answered more than once.
/// The first accepted response completes it; remembering the request
/// lets the later responses be recognised as duplicates instead of mistaken for
/// responses we never asked for.
const COMPLETED_REQUEST_GRACE: Duration = REPAIR_TIMEOUT.saturating_mul(2);

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
    ///
    /// The hash serves as a local lookup key identifying the request,
    /// independently of which [`RepairRequest`] messages carried it.
    fn hash(&self) -> Hash {
        hash(&crate::serialize(self))
    }
}

/// Request messages for the repair sub-protocol.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub struct RepairRequest {
    /// The validator that sent this request.
    sender: ValidatorIndex,
    /// The actual request payload.
    req_type: RepairRequestType,
}

/// Response message for the repair sub-protocol.
///
/// Carries the [`RepairResponsePayload`] together with the identity of the
/// responding validator, so the requester can correlate the response back to
/// the specific peer it fanned the request out to.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub struct RepairResponse {
    /// The validator who sent this response.
    responder: ValidatorIndex,
    /// The actual response payload.
    payload: RepairResponsePayload,
}

/// Payload of a [`RepairResponse`].
///
/// Each response type corresponds to a specific request message type.
/// Each response contains the request message that it is a response to.
/// If well-formed, it thus contains the corresponding variant of [`RepairRequest`].
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub enum RepairResponsePayload {
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

impl RepairResponsePayload {
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
/// This allows us to prioritise repairing blocks for ourselves over serving repair requests for other nodes.
pub struct RepairRequestHandler<N: Network> {
    epoch_info: Arc<ValidatorEpochInfo>,
    blockstore: SharedBlockstore,
    network: N,
}

impl<N> RepairRequestHandler<N>
where
    N: RepairResponderNetwork,
{
    /// Creates a new repair request handler instance.
    ///
    /// Given `network` instance will be used for receiving repair requests and sending repair responses.
    /// The blockstore will be used to handle the repair requests.
    pub fn new(
        epoch_info: Arc<ValidatorEpochInfo>,
        blockstore: SharedBlockstore,
        network: N,
    ) -> Self {
        Self {
            epoch_info,
            blockstore,
            network,
        }
    }

    /// Main loop of the repair request handler.
    ///
    /// Listens for repair requests on `self.network`.
    /// Looks up the corresponding data in `self.blockstore` and sends replies.
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

    /// Tries to answer the given repair request.
    ///
    /// If we have the information in blockstore, it is sent to the requester.
    /// Otherwise, a [`RepairResponsePayload::Nack`] is sent back to the requester.
    #[hotpath::measure]
    async fn answer_request(&self, request: RepairRequest) -> std::io::Result<()> {
        trace!("answering repair request: {request:?}");

        // drop requests from validators outside the current epoch's set,
        // otherwise `validator()` indexing in `send_response` would panic on byzantine input
        let epoch = self.epoch_info.epoch_info();
        if request.sender.as_usize() >= epoch.validators().len() {
            warn!(
                "dropping repair request from unknown validator {:?}",
                request.sender
            );
            return Ok(());
        }

        let payload = self
            .try_build_response(&request)
            .await
            .unwrap_or_else(|| RepairResponsePayload::Nack(request.req_type.clone()));
        self.send_response(payload, request.sender).await
    }

    /// Tries to build a positive response payload for the given repair request.
    ///
    /// Returns `None` if the requested data is not available in the blockstore.
    async fn try_build_response(&self, request: &RepairRequest) -> Option<RepairResponsePayload> {
        match &request.req_type {
            RepairRequestType::LastSliceRoot(block_id) => {
                let blockstore = self.blockstore.read().await;
                let last_slice = blockstore.get_last_slice_index(block_id)?;
                let root = blockstore.get_slice_root(block_id, last_slice)?;
                let proof = blockstore.create_double_merkle_proof(block_id, last_slice)?;
                drop(blockstore);
                Some(RepairResponsePayload::LastSliceRoot(
                    request.req_type.clone(),
                    last_slice,
                    root,
                    proof,
                ))
            }
            RepairRequestType::SliceRoot(block_id, slice) => {
                let blockstore = self.blockstore.read().await;
                let root = blockstore.get_slice_root(block_id, *slice)?;
                let proof = blockstore.create_double_merkle_proof(block_id, *slice)?;
                drop(blockstore);
                Some(RepairResponsePayload::SliceRoot(
                    request.req_type.clone(),
                    root,
                    proof,
                ))
            }
            RepairRequestType::Shred(block_id, slice, shred_index) => {
                let blockstore = self.blockstore.read().await;
                let shred = blockstore
                    .get_shred(block_id, *slice, *shred_index)
                    .cloned()?;
                drop(blockstore);
                Some(RepairResponsePayload::Shred(
                    request.req_type.clone(),
                    shred.into_shred(),
                ))
            }
        }
    }

    #[hotpath::measure]
    async fn send_response(
        &self,
        payload: RepairResponsePayload,
        validator: ValidatorIndex,
    ) -> std::io::Result<()> {
        let to = self
            .epoch_info
            .epoch_info()
            .validator(validator)
            .repair_requester_address;
        let response = RepairResponse {
            responder: self.epoch_info.own_id(),
            payload,
        };
        self.network.send(&response, to).await
    }
}

/// Instance of double-Merkle based block repair protocol.
///
/// This is used by the node to repair blocks that it is missing.
/// This does not answer repair requests from other nodes, that is handled by [`RepairRequestHandler`].
pub struct Repair<N: Network> {
    blockstore: SharedBlockstore,
    pool: SharedPool,
    slice_roots: BTreeMap<(BlockId, SliceIndex), SliceRoot>,
    outstanding_requests: BTreeMap<Hash, OutstandingRequest>,
    /// Expiry times of outstanding requests, earliest first (min-heap via [`Reverse`]).
    request_timeouts: BinaryHeap<Reverse<(Instant, Hash)>>,
    /// Hashes of requests we have already accepted a response for, retained for
    /// [`COMPLETED_REQUEST_GRACE`] so duplicate responses (from the other peers
    /// a request was fanned out to, or from retries) can be told apart from
    /// responses to requests we never sent.
    recently_completed: BTreeSet<Hash>,
    /// Expiry queue for `recently_completed`, ordered by insertion (= expiry) time.
    completed_expiry: VecDeque<(Instant, Hash)>,
    network: N,
    sampler: StakeWeightedSampler,
    epoch_info: Arc<ValidatorEpochInfo>,
}

/// Bookkeeping for a repair request that has been sent but not yet fulfilled.
#[derive(Debug)]
struct OutstandingRequest {
    /// The request that was sent, kept so it can be retried.
    req_type: RepairRequestType,
    /// Validators this request was fanned out to that have not yet responded.
    ///
    /// A NACK retires the responding peer from this set; the request is only
    /// retried once the set is empty (every peer bailed) or it times out. This
    /// collapses the up-to-[`REPAIR_FANOUT`] concurrent NACKs for a single
    /// request into one retry, instead of each NACK spawning a fresh fan-out
    /// (which would amplify request volume geometrically).
    pending: HashSet<ValidatorIndex>,
}

impl<N> Repair<N>
where
    N: RepairRequesterNetwork,
{
    /// Creates a new repair instance.
    ///
    /// Given `network` will be used for sending repair requests and receiving repair responses.
    /// Any repaired shreds will be written into the provided `blockstore`.
    pub fn new(
        blockstore: SharedBlockstore,
        pool: SharedPool,
        network: N,
        epoch_info: Arc<ValidatorEpochInfo>,
    ) -> Self {
        let validators = epoch_info.epoch_info().validators().to_vec();
        let sampler = StakeWeightedSampler::new(validators);
        Self {
            blockstore,
            pool,
            slice_roots: BTreeMap::new(),
            outstanding_requests: BTreeMap::new(),
            request_timeouts: BinaryHeap::new(),
            recently_completed: BTreeSet::new(),
            completed_expiry: VecDeque::new(),
            network,
            sampler,
            epoch_info,
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
                    // `send_request` re-arms the entry and pushes a fresh timeout,
                    // so just look it up rather than removing it here.
                    if let Some(req) = self.outstanding_requests.get(&hash) {
                        let req_type = req.req_type.clone();
                        debug!("retrying timed-out repair request {req_type:?}");
                        if let Err(err) = self.send_request(req_type).await {
                            warn!("sending timed-out repair request failed: {err}");
                        }
                    }
                }
            }
        }
    }

    /// Starts repair process for the block specified by `slot` and `block_hash`.
    pub async fn repair_block(&mut self, block_id: BlockId) {
        let (slot, block_hash) = &block_id;
        if self.blockstore.read().await.get_block(&block_id).is_some() {
            trace!(
                "ignoring repair for block {} in slot {slot}, already have the block",
                block_hash.short_hex()
            );
            return;
        }

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
    ///
    /// The request is only marked completed (see [`Repair::mark_completed`])
    /// once a response has been *accepted*, i.e. after its variant-specific
    /// validation passes. A malformed or invalid response is ignored without
    /// touching `outstanding_requests`, so the request stays in flight: the
    /// pending timeout can still retry it and a valid response from one of the
    /// other peers it was fanned out to can still be accepted. A `Nack` is not
    /// marked completed either; that path retires the peer and may retry.
    #[hotpath::measure]
    async fn handle_response(&mut self, response: RepairResponse) {
        trace!("handling repair response: {response:?}");
        let RepairResponse { responder, payload } = response;
        let request_hash = payload.request_type().hash();

        // check whether we are (still) waiting on a response to this request
        if !self.outstanding_requests.contains_key(&request_hash) {
            self.prune_completed();
            if self.recently_completed.contains(&request_hash) {
                // Expected: each request is fanned out to several peers and
                // retried on timeout, so the first accepted response completes
                // it and the rest arrive as duplicates.
                debug!("ignoring duplicate repair response for answered request {payload:?}");
            } else {
                warn!("received repair response for unknown request {payload:?}");
            }
            return;
        }

        // A NACK only retires the responding peer from the request's pending
        // set. We retry just once the whole fan-out has bailed (so the
        // up-to-`REPAIR_FANOUT` concurrent NACKs for one request collapse into a
        // single retry); any positive response completes the request outright.
        if let RepairResponsePayload::Nack(req_type) = &payload {
            let req = self
                .outstanding_requests
                .get_mut(&request_hash)
                .expect("presence checked above");
            // NOTE: `responder` is unauthenticated at this layer, so a malicious
            // peer can spoof another validator's id to retire it from `pending`,
            // making us retry sooner (a bounded request amplification) — or, if
            // the id was never sampled, waste the NACK. We deliberately do not
            // sign NACKs to close this: the intended fix is to authenticate the
            // repair transport itself, so every message (not just NACKs) is
            // bound to a verified sender without per-message signature overhead
            // on the data path.
            //
            // TODO: authenticate the repair socket (e.g. QUIC datagram-mode with
            // per-peer connections), then key `pending` retirement on the
            // connection's verified identity rather than the self-reported
            // `responder` field. Data responses already self-validate via their
            // Merkle proof + leader signature, so this only hardens NACKs.
            req.pending.remove(&responder);
            if !req.pending.is_empty() {
                return;
            }
            let req_type = req_type.clone();
            debug!("all peers NACKed repair request {req_type:?}, retrying");
            if let Err(err) = self.send_request(req_type).await {
                warn!("retrying NACKed repair request failed: {err}");
            }
            return;
        }

        // Positive response. Validate it before completing the request: only a
        // response we actually accept retires the request (via `mark_completed`
        // in the arms below), so an invalid one leaves it outstanding for a
        // retry or for a valid response from one of the other fanned-out peers.
        match payload {
            RepairResponsePayload::Nack(_) => unreachable!("handled above"),
            RepairResponsePayload::LastSliceRoot(req_type, last_slice, root, proof) => {
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
                self.mark_completed(request_hash);

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
            RepairResponsePayload::SliceRoot(req_type, root, proof) => {
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
                self.mark_completed(request_hash);

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
            RepairResponsePayload::Shred(req_type, shred) => {
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
                self.mark_completed(request_hash);

                // store shred
                let res = self
                    .blockstore
                    .write()
                    .await
                    .add_shred_from_repair(block_hash.clone(), validated)
                    .await;
                if let Ok(Some(block_info)) = res {
                    assert_eq!(block_info.hash, *block_hash);
                    self.pool
                        .write()
                        .await
                        .add_block((*slot, block_info.hash), block_info.parent)
                        .await;
                    debug!(
                        "successfully repaired block {} in slot {}",
                        block_hash.short_hex(),
                        slot
                    );
                }
            }
        }
    }

    /// Marks the request identified by `hash` as completed once its response
    /// has been accepted: stops tracking it as outstanding and remembers it for
    /// [`COMPLETED_REQUEST_GRACE`], so any further responses for it (from the
    /// other peers it was fanned out to, or from retries) are recognised as
    /// duplicates rather than mistaken for responses we never asked for.
    ///
    /// The stale timeout entry is left in `request_timeouts`; it is skipped
    /// harmlessly when it pops (the request is no longer outstanding) or purged
    /// if the same hash is later re-armed by [`Repair::send_request`].
    fn mark_completed(&mut self, hash: Hash) {
        self.outstanding_requests.remove(&hash);
        self.prune_completed();
        if self.recently_completed.insert(hash.clone()) {
            let expiry = Instant::now() + COMPLETED_REQUEST_GRACE;
            self.completed_expiry.push_back((expiry, hash));
        }
    }

    /// Drops `recently_completed` entries whose grace period has elapsed.
    fn prune_completed(&mut self) {
        let now = Instant::now();
        while self
            .completed_expiry
            .front()
            .is_some_and(|(expiry, _)| *expiry <= now)
        {
            if let Some((_, hash)) = self.completed_expiry.pop_front() {
                self.recently_completed.remove(&hash);
            }
        }
    }

    /// Samples a fresh set of peers and fans `req_type` out to all of them.
    ///
    /// (Re)arms the outstanding-request and timeout bookkeeping for the request,
    /// overwriting any previous entry, so a retry replaces the prior fan-out.
    #[hotpath::measure]
    async fn send_request(&mut self, req_type: RepairRequestType) -> std::io::Result<()> {
        let hash = req_type.hash();
        let peers = self.pick_random_peers();
        let addrs: Vec<SocketAddr> = {
            let epoch = self.epoch_info.epoch_info();
            peers
                .iter()
                .map(|id| epoch.validator(*id).repair_responder_address)
                .collect()
        };

        let expiry = Instant::now() + REPAIR_TIMEOUT;
        self.outstanding_requests.insert(
            hash.clone(),
            OutstandingRequest {
                req_type: req_type.clone(),
                pending: peers,
            },
        );
        self.request_timeouts.retain(|Reverse((_, h))| h != &hash);
        self.request_timeouts.push(Reverse((expiry, hash)));

        let request = RepairRequest {
            sender: self.epoch_info.own_id(),
            req_type,
        };
        self.network.send_to_many(&request, addrs).await?;
        Ok(())
    }

    /// Samples up to [`REPAIR_FANOUT`] distinct peers to fan a request out to.
    fn pick_random_peers(&self) -> HashSet<ValidatorIndex> {
        let mut peers = HashSet::new();
        // HACK: magic number to fix high-failure scenarios
        for _ in 0..10 {
            peers.insert(self.pick_random_peer());
            if peers.len() == REPAIR_FANOUT {
                break;
            }
        }
        peers
    }

    fn pick_random_peer(&self) -> ValidatorIndex {
        let mut rng = rand::rng();
        let mut peer_info = self.sampler.sample_info(&mut rng);
        while peer_info.id == self.epoch_info.own_id() {
            peer_info = self.sampler.sample_info(&mut rng);
        }
        peer_info.id
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use tokio::sync::RwLock;
    use tokio::sync::mpsc::Sender;

    use super::*;
    use crate::ValidatorIndex;
    use crate::consensus::{BlockstoreImpl, EpochInfo, PoolImpl};
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::crypto::signature::SecretKey;
    use crate::network::simulated::SimulatedNetworkCore;
    use crate::network::{SimulatedNetwork, localhost_ip_sockaddr};
    use crate::shredder::TOTAL_SHREDS;
    use crate::test_utils::{create_random_shredded_block, generate_validators, random_block_id};
    use crate::types::Slot;
    use crate::types::slice_index::MAX_SLICES_PER_BLOCK;

    /// Test context for repair tests.
    ///
    /// Sets up a small network of 2 validators:
    /// - Validator 0: leader of the genesis window, no repair instance.
    /// - Validator 1: has repair set up, is not the leader.
    struct TestContext {
        repair_tx: Sender<BlockId>,
        blockstore: SharedBlockstore,
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

        let core = Arc::new(SimulatedNetworkCore::new(1, 0.0, 0.0));
        let v0_repair_requester_network = core.join_unlimited(ValidatorIndex::new(0)).await;
        let v0_repair_responder_network = core.join_unlimited(ValidatorIndex::new(1)).await;
        let v1_repair_requester_network = core.join_unlimited(ValidatorIndex::new(2)).await;
        let v1_repair_responder_network = core.join_unlimited(ValidatorIndex::new(3)).await;

        let epoch_info = EpochInfo::new(validators);
        let epoch_info = Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(1), epoch_info));

        // set up blockstore
        let (blockstore_tx, blockstore_rx) = tokio::sync::mpsc::channel(100);
        let blockstore: SharedBlockstore =
            Arc::new(RwLock::new(BlockstoreImpl::new(blockstore_tx)));

        // set up pool
        let (pool_tx, pool_rx) = tokio::sync::mpsc::channel(100);
        let (repair_tx, repair_rx) = tokio::sync::mpsc::channel(100);
        let pool: SharedPool = Arc::new(RwLock::new(PoolImpl::new(
            epoch_info.clone(),
            pool_tx,
            repair_tx.clone(),
        )));

        // create and start Repair instance
        let mut repair = Repair::new(
            Arc::clone(&blockstore),
            pool,
            v1_repair_requester_network,
            epoch_info.clone(),
        );
        tokio::spawn(async move {
            repair.repair_loop(repair_rx).await;
            // keep event receivers alive so sends from blockstore/pool don't fail
            drop(blockstore_rx);
            drop(pool_rx);
        });
        let repair_request_handler =
            RepairRequestHandler::new(epoch_info, blockstore.clone(), v1_repair_responder_network);
        tokio::spawn(async move {
            repair_request_handler.run().await;
        });
        TestContext {
            repair_tx,
            blockstore,
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
        let response = RepairResponse {
            responder: ValidatorIndex::new(0),
            payload: RepairResponsePayload::LastSliceRoot(
                req_type,
                SliceIndex::new_for_test(num_slices - 1),
                shreds.last().unwrap()[0].slice_root().clone(),
                merkle_tree.create_proof(num_slices - 1),
            ),
        };
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
            let response = RepairResponse {
                responder: ValidatorIndex::new(0),
                payload: RepairResponsePayload::SliceRoot(req_type, root, proof),
            };
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
                let response = RepairResponse {
                    responder: ValidatorIndex::new(0),
                    payload: RepairResponsePayload::Shred(req_type, shred.into_shred()),
                };
                ctx.v0_request_net.send(&response, port1).await.unwrap();
            }
        }

        // block should be repaired shortly; poll until it lands rather than
        // relying on a fixed sleep, which is racy under CI load
        let repaired = tokio::time::timeout(Duration::from_secs(10), async {
            while ctx
                .blockstore
                .read()
                .await
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

    /// A single repair request is fanned out to multiple peers. If each peer's
    /// NACK triggered its own retry, the up-to-[`REPAIR_FANOUT`] NACKs for one
    /// request would each spawn a fresh fan-out, amplifying request volume
    /// geometrically. This drives the requester directly and asserts that NACKs
    /// from a whole fan-out collapse into exactly one retry round.
    #[tokio::test]
    async fn nack_collapses_into_single_retry() {
        // four validators so the requester (own = 1) can fan a request out to
        // more than one peer (the eligible-peer set is {0, 2, 3}).
        let (_, epoch_info) = generate_validators(4);
        let mut validators = epoch_info.validators().to_vec();

        // route every peer's repair-responder address to one shared endpoint, so
        // the test observes the complete fan-out (and every retry) on one socket.
        const SHARED: u16 = 100;
        const REQUESTER: u16 = 101;
        for v in &mut validators {
            v.repair_responder_address = localhost_ip_sockaddr(SHARED);
        }

        let core = Arc::new(SimulatedNetworkCore::new(1, 0.0, 0.0));
        let peers_net: SimulatedNetwork<RepairResponse, RepairRequest> = core
            .join_unlimited(ValidatorIndex::new(SHARED.into()))
            .await;
        let requester_net: SimulatedNetwork<RepairRequest, RepairResponse> = core
            .join_unlimited(ValidatorIndex::new(REQUESTER.into()))
            .await;

        let epoch_info = EpochInfo::new(validators);
        let epoch_info = Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(1), epoch_info));

        // blockstore/pool are unused by NACK handling, but needed to construct
        // `Repair`; keep the receivers alive for the duration of the test.
        let (blockstore_tx, _blockstore_rx) = tokio::sync::mpsc::channel(100);
        let blockstore: SharedBlockstore =
            Arc::new(RwLock::new(BlockstoreImpl::new(blockstore_tx)));
        let (pool_tx, _pool_rx) = tokio::sync::mpsc::channel(100);
        let (repair_tx, _repair_rx) = tokio::sync::mpsc::channel(100);
        let pool: SharedPool = Arc::new(RwLock::new(PoolImpl::new(
            epoch_info.clone(),
            pool_tx,
            repair_tx,
        )));

        // drive `Repair` directly (no `repair_loop`), so the only requests sent
        // are the ones triggered by our explicit calls -- no timeout retries.
        let mut repair = Repair::new(blockstore, pool, requester_net, epoch_info);

        let block_id = (Slot::genesis().next(), GENESIS_BLOCK_HASH);
        let req_type = RepairRequestType::LastSliceRoot(block_id);
        let hash = req_type.hash();

        // initial fan-out
        repair.send_request(req_type.clone()).await.unwrap();
        let pending: Vec<ValidatorIndex> = repair
            .outstanding_requests
            .get(&hash)
            .expect("request outstanding after send")
            .pending
            .iter()
            .copied()
            .collect();
        let fanout = pending.len();
        assert!(fanout >= 1);
        for _ in 0..fanout {
            assert_eq!(peers_net.receive().await.unwrap().req_type, req_type);
        }

        // NACKs from all but the last peer must NOT trigger a retry: the request
        // is still pending on the remaining peer(s).
        for &responder in &pending[..fanout - 1] {
            repair
                .handle_response(RepairResponse {
                    responder,
                    payload: RepairResponsePayload::Nack(req_type.clone()),
                })
                .await;
            assert!(
                !repair
                    .outstanding_requests
                    .get(&hash)
                    .expect("still outstanding")
                    .pending
                    .is_empty(),
                "retried before the whole fan-out had NACKed",
            );
        }
        assert!(
            tokio::time::timeout(Duration::from_millis(50), peers_net.receive())
                .await
                .is_err(),
            "a partial set of NACKs triggered a premature retry",
        );

        // the final NACK drains the pending set and triggers exactly one retry.
        repair
            .handle_response(RepairResponse {
                responder: pending[fanout - 1],
                payload: RepairResponsePayload::Nack(req_type.clone()),
            })
            .await;
        let retry_fanout = repair
            .outstanding_requests
            .get(&hash)
            .expect("request re-armed after retry")
            .pending
            .len();

        // exactly one fresh fan-out went out -- not one per NACK.
        let mut retried = 0;
        while tokio::time::timeout(Duration::from_millis(50), peers_net.receive())
            .await
            .is_ok()
        {
            retried += 1;
        }
        assert_eq!(
            retried, retry_fanout,
            "NACKs amplified into more than a single retry round",
        );
    }

    /// A malformed/invalid response must not "poison" an in-flight request: it
    /// is rejected *before* the request is marked completed, so the request
    /// stays outstanding and a valid response arriving afterwards (e.g. from one
    /// of the other peers it was fanned out to, or after a timeout retry) is
    /// still accepted.
    #[tokio::test]
    async fn valid_response_accepted_after_invalid() {
        const SLICES: usize = 1;
        let ctx = setup().await;

        // create a block to repair
        let slot = Slot::genesis().next();
        let (block_hash, merkle_tree, shreds) =
            create_random_shredded_block(slot, SLICES, &ctx.leader_sk);
        let block_to_repair = (slot, block_hash);

        // ask repair instance to repair this block
        ctx.repair_tx.send(block_to_repair.clone()).await.unwrap();

        // expect LastSliceRoot request first
        let msg = ctx.v0_request_net.receive().await.unwrap();
        let req_type = RepairRequestType::LastSliceRoot(block_to_repair.clone());
        assert_eq!(msg.req_type, req_type);
        // responses go to v1's repair requester socket (joined at index 2)
        let port1 = localhost_ip_sockaddr(2);

        // answer with an INVALID response first: a bogus slice root makes the
        // Merkle proof check fail, so the response must be rejected without
        // completing the request.
        let bad_response = RepairResponse {
            responder: ValidatorIndex::new(0),
            payload: RepairResponsePayload::LastSliceRoot(
                req_type.clone(),
                SliceIndex::new_for_test(SLICES - 1),
                SliceRoot::from(hash(b"not the real slice root")),
                merkle_tree.create_proof(SLICES - 1),
            ),
        };
        ctx.v0_request_net.send(&bad_response, port1).await.unwrap();

        // then answer the same request with the correct response
        let good_response = RepairResponse {
            responder: ValidatorIndex::new(0),
            payload: RepairResponsePayload::LastSliceRoot(
                req_type,
                SliceIndex::new_for_test(SLICES - 1),
                shreds.last().unwrap()[0].slice_root().clone(),
                merkle_tree.create_proof(SLICES - 1),
            ),
        };
        ctx.v0_request_net
            .send(&good_response, port1)
            .await
            .unwrap();

        // the valid response must be accepted despite the earlier invalid one:
        // repair proceeds to request the slice root for slice 0.
        let msg = tokio::time::timeout(Duration::from_secs(1), ctx.v0_request_net.receive())
            .await
            .expect("repair did not progress after a valid response followed an invalid one")
            .unwrap();
        let want = RepairRequestType::SliceRoot(block_to_repair, SliceIndex::new_for_test(0));
        assert_eq!(msg.req_type, want);
    }

    /// Two correct responses for the same request (e.g. from two of the peers it
    /// was fanned out to) must be handled gracefully: the first is accepted and
    /// the second is recognised as a duplicate, not reprocessed into a redundant
    /// request.
    #[tokio::test]
    async fn duplicate_correct_responses_are_deduplicated() {
        const SLICES: usize = 1;
        let ctx = setup().await;

        // create a block to repair
        let slot = Slot::genesis().next();
        let (block_hash, merkle_tree, shreds) =
            create_random_shredded_block(slot, SLICES, &ctx.leader_sk);
        let block_to_repair = (slot, block_hash);

        // ask repair instance to repair this block
        ctx.repair_tx.send(block_to_repair.clone()).await.unwrap();

        // expect LastSliceRoot request first
        let msg = ctx.v0_request_net.receive().await.unwrap();
        let req_type = RepairRequestType::LastSliceRoot(block_to_repair.clone());
        assert_eq!(msg.req_type, req_type);
        let port1 = localhost_ip_sockaddr(2);

        // send the same valid response twice
        let response = RepairResponse {
            responder: ValidatorIndex::new(0),
            payload: RepairResponsePayload::LastSliceRoot(
                req_type,
                SliceIndex::new_for_test(SLICES - 1),
                shreds.last().unwrap()[0].slice_root().clone(),
                merkle_tree.create_proof(SLICES - 1),
            ),
        };
        ctx.v0_request_net.send(&response, port1).await.unwrap();
        ctx.v0_request_net.send(&response, port1).await.unwrap();

        // the first response is accepted: repair requests the slice root.
        let msg = ctx.v0_request_net.receive().await.unwrap();
        let want = RepairRequestType::SliceRoot(block_to_repair, SliceIndex::new_for_test(0));
        assert_eq!(msg.req_type, want);

        // the second response is a duplicate: it must not trigger another
        // fan-out of the same request. The window is well below REPAIR_TIMEOUT,
        // so a timeout retry can't account for any further request either.
        let extra =
            tokio::time::timeout(Duration::from_millis(150), ctx.v0_request_net.receive()).await;
        assert!(
            extra.is_err(),
            "duplicate response was reprocessed, causing a redundant request: {:?}",
            extra.ok().map(|m| m.unwrap().req_type),
        );
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
            msg.payload,
            RepairResponsePayload::Nack(RepairRequestType::SliceRoot(..))
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

        // ingest the block into blockstore
        let mut b = ctx.blockstore.write().await;
        for slice_shreds in shreds.clone() {
            for shred in slice_shreds {
                let _ = b.add_shred_from_dissemination(shred).await;
            }
        }
        drop(b);
        assert_eq!(
            ctx.blockstore.read().await.disseminated_block_hash(slot),
            Some(&block_hash)
        );
        assert!(
            ctx.blockstore
                .read()
                .await
                .get_block(&block_to_repair)
                .is_some()
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
        let RepairResponsePayload::LastSliceRoot(req_type, last_slice, root, proof) = msg.payload
        else {
            panic!("not LastSliceRoot response");
        };
        assert_eq!(req_type, request.req_type);
        assert_eq!(last_slice.inner(), SLICES - 1);
        assert_eq!(&root, shreds[last_slice.inner()][0].slice_root());
        let correct_proof = ctx
            .blockstore
            .read()
            .await
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
            let RepairResponsePayload::SliceRoot(req_type, root, proof) = msg.payload else {
                panic!("not SliceRoot response");
            };
            assert_eq!(req_type, request.req_type);
            assert_eq!(&root, shreds[slice.inner()][0].slice_root());
            let correct_proof = ctx
                .blockstore
                .read()
                .await
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
                let RepairResponsePayload::Shred(req_type, shred) = msg.payload else {
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
