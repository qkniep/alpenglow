// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Block repair sub-protocol.
//!
//! This module implements the double-Merkle based block repair protocol.
//! It uses the fact that the block hash is the root of a Merkle tree, where
//! the leaves of this tree are the Merkle roots of each of the block's slices.
//! Each repair response is accompanied by a Merkle proof and can thus be
//! individually verified.

use std::collections::{BTreeMap, BinaryHeap};
use std::sync::Arc;
use std::time::{Duration, Instant};

use log::{debug, trace, warn};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::consensus::{Blockstore, EpochInfo, Pool};
use crate::crypto::{Hash, MerkleTree, hash};
use crate::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use crate::network::{Network, NetworkError, NetworkMessage};
use crate::shredder::{DATA_SHREDS, Shred};
use crate::types::SliceIndex;
use crate::{BlockId, ValidatorId};

/// Maximum time to wait for a response to a repair request.
///
/// After a request times out we retry it from another node.
const REPAIR_TIMEOUT: Duration = Duration::from_secs(2);

/// Message types for the repair sub-protocol.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairMessage {
    /// Request for information from another validator.
    Request(RepairRequest, ValidatorId),
    /// Response to a request from another validator.
    Response(RepairResponse),
}

/// Request messages for the repair sub-protocol.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RepairRequest {
    /// Request for the total number of slices in block with a given hash.
    LastSliceRoot(BlockId),
    /// Request for the root hash of a slice, identified by block hash and slice index.
    SliceRoot(BlockId, SliceIndex),
    /// Request for shred, identified by block hash, slice index and shred index.
    Shred(BlockId, SliceIndex, usize),
}

/// Response messages for the repair sub-protocol.
///
/// Each response type corresponds to a specific request message type.
/// Each response contains the request message that it is a response to.
/// If well-formed, it thus contains the corresponding variant of [`RepairRequest`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairResponse {
    /// Response with the last slice's Merkle root hash, plus corresponding proof.
    LastSliceRoot(RepairRequest, SliceIndex, Hash, Vec<Hash>),
    /// Response with the Merkle root hash of a specific slice, plus corresponding proof.
    SliceRoot(RepairRequest, Hash, Vec<Hash>),
    /// Response with a specific shred.
    Shred(RepairRequest, Shred),
}

/// Instance of double-Merkle based block repair protocol.
pub struct Repair<N: Network> {
    blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
    pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,

    slice_roots: BTreeMap<(BlockId, SliceIndex), Hash>,
    outstanding_requests: BTreeMap<Hash, RepairRequest>,
    request_timeouts: BinaryHeap<(Instant, Hash)>,

    network: N,
    repair_channel: (
        tokio::sync::mpsc::Sender<BlockId>,
        Option<tokio::sync::mpsc::Receiver<BlockId>>,
    ),
    sampler: StakeWeightedSampler,
    epoch_info: Arc<EpochInfo>,
}

impl<N: Network> Repair<N> {
    /// Creates a new repair instance.
    ///
    /// Given `network` will be used for sending and receiving repair messages.
    /// Any repaired shreds will be written into the provided `blockstore`.
    pub fn new(
        blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
        pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,
        network: N,
        repair_channel: (
            tokio::sync::mpsc::Sender<BlockId>,
            tokio::sync::mpsc::Receiver<BlockId>,
        ),
        epoch_info: Arc<EpochInfo>,
    ) -> Self {
        let validators = epoch_info.validators.clone();
        let sampler = StakeWeightedSampler::new(validators);
        let repair_channel = (repair_channel.0, Some(repair_channel.1));
        Self {
            blockstore,
            pool,

            slice_roots: BTreeMap::new(),
            outstanding_requests: BTreeMap::new(),
            request_timeouts: BinaryHeap::new(),

            network,
            repair_channel,
            sampler,
            epoch_info,
        }
    }

    /// Main loop of the repair protocol.
    ///
    /// Listens to incoming requests for blocks to repair on `self.repair_channel`.
    /// Inititates the corresponding repair process and handles ongoing repairs.
    /// Also, listens to incoming repair messages from the network and handles them.
    pub async fn repair_loop(&mut self) {
        let mut repair_receiver = self.repair_channel.1.take().unwrap();
        loop {
            let next_timeout = self.request_timeouts.peek().map(|t| t.0);
            let sleep_duration = match next_timeout {
                None => std::time::Duration::MAX,
                Some(t) => t.duration_since(Instant::now()),
            };
            tokio::select! {
                // handle repair request or response from network
                res = self.receive() => self.handle_repair_message(res.unwrap()).await.unwrap(),
                // handle request for repairing new block
                Some(block_id) = repair_receiver.recv() => {
                    self.repair_block(block_id).await;
                }
                // handle next request timeout
                _ = tokio::time::sleep(sleep_duration) => {
                    let Some((_, hash)) = self.request_timeouts.pop() else {
                        continue;
                    };
                    if let Some(request) = self.outstanding_requests.remove(&hash) {
                        debug!("retrying timed-out repair request {request:?}");
                        self.send_request(request).await.unwrap();
                    }
                }
            }
        }
    }

    /// Starts repair process for the block specified by `slot` and `block_hash`.
    pub async fn repair_block(&mut self, block_id: BlockId) {
        let (slot, block_hash) = block_id;
        let h = &hex::encode(block_hash)[..8];
        if self.blockstore.read().await.get_block(block_id).is_some() {
            trace!("ignoring repair for block {h} in slot {slot}, already have the block");
            return;
        }

        debug!("repairing block {h} in slot {slot}");
        let req = RepairRequest::LastSliceRoot(block_id);
        self.send_request(req).await.unwrap();
    }

    async fn handle_repair_message(&mut self, msg: RepairMessage) -> Result<(), NetworkError> {
        match msg {
            RepairMessage::Request(request, sender) => {
                self.answer_request(request, sender).await?;
            }
            RepairMessage::Response(resposne) => {
                self.handle_response(resposne).await;
            }
        }
        Ok(())
    }

    /// Tries to answer the given repair request.
    ///
    /// If we do not have the block the request refers to, the request is ignored.
    /// Otherwise, the correct response is sent back to the sender of the request.
    async fn answer_request(
        &self,
        request: RepairRequest,
        sender: ValidatorId,
    ) -> Result<(), NetworkError> {
        trace!("answering repair request: {request:?}");
        let block_id = request.block_id();
        let blockstore = self.blockstore.read().await;
        let response = match request {
            RepairRequest::LastSliceRoot(_) => {
                let Some(last_slice) = blockstore.get_last_slice_index(block_id) else {
                    return Ok(());
                };
                let Some(root) = blockstore.get_slice_root(block_id, last_slice) else {
                    return Ok(());
                };
                let Some(proof) = blockstore.create_double_merkle_proof(block_id, last_slice)
                else {
                    return Ok(());
                };
                RepairResponse::LastSliceRoot(request, last_slice, root, proof)
            }
            RepairRequest::SliceRoot(_, slice) => {
                let Some(root) = blockstore.get_slice_root(block_id, slice) else {
                    return Ok(());
                };
                let Some(proof) = blockstore.create_double_merkle_proof(block_id, slice) else {
                    return Ok(());
                };
                RepairResponse::SliceRoot(request, root, proof)
            }
            RepairRequest::Shred(_, slice, shred) => {
                let Some(shred) = blockstore.get_shred(block_id, slice, shred).cloned() else {
                    return Ok(());
                };
                RepairResponse::Shred(request, shred)
            }
        };
        drop(blockstore);
        self.send_response(response, sender).await
    }

    /// Handles a repair response, storing the received data.
    ///
    /// If the response contains a shred, it will be stored in the [`Blockstore`].
    /// Otherwise, metadata is stored in the [`Repair`] struct itself.
    /// Does nothing if the provided `response` is not well-formed.
    async fn handle_response(&mut self, response: RepairResponse) {
        trace!("handling repair response: {response:?}");
        let request_hash = response.request().hash();

        // check whether we are (still) waiting on response to this request
        let Some(_) = self.outstanding_requests.remove(&request_hash) else {
            warn!("received repair response for unknown request {response:?}");
            return;
        };

        let block_id = response.block_id();
        let (slot, block_hash) = block_id;
        match response {
            RepairResponse::LastSliceRoot(req, last_slice, root, proof) => {
                // check validity of response
                let RepairRequest::LastSliceRoot(_) = req else {
                    warn!("repair response (LastSliceRoot) to mismatching request {req:?}");
                    return;
                };
                if !MerkleTree::check_proof_last(&root, last_slice.inner(), block_hash, &proof) {
                    warn!("repair response (LastSliceRoot) with invalid proof");
                    return;
                }

                // store slice Merkle root
                self.slice_roots.insert((block_id, last_slice), root);

                // issue next requests
                // TODO: do not request last slice root again
                // TODO: already requests shreds for last slice here
                for slice in last_slice.until() {
                    let req = RepairRequest::SliceRoot(block_id, slice);
                    self.send_request(req).await.unwrap();
                }
            }
            RepairResponse::SliceRoot(req, root, proof) => {
                // check validity of response
                let RepairRequest::SliceRoot(_, slice) = req else {
                    warn!("repair response (SliceRoot) to mismatching request {req:?}");
                    return;
                };
                if !MerkleTree::check_proof(&root, slice.inner(), block_hash, &proof) {
                    warn!("repair response (SliceRoot) with invalid proof");
                    return;
                }

                // store slice Merkle root
                self.slice_roots.insert((block_id, slice), root);

                // issue next requests
                for shred_index in 0..DATA_SHREDS {
                    let req = RepairRequest::Shred(block_id, slice, shred_index);
                    self.send_request(req).await.unwrap();
                }
            }
            RepairResponse::Shred(req, shred) => {
                // check validity of response
                let RepairRequest::Shred(_, slice, index) = req else {
                    warn!("repair response (Shred) to mismatching request {req:?}");
                    return;
                };
                if shred.payload().header.slot != slot
                    || shred.payload().header.slice_index != slice
                    || shred.payload().index_in_slice != index
                {
                    warn!("repair response (Shred) for mismatching shred index");
                    return;
                }
                let Some(&root) = self.slice_roots.get(&(block_id, slice)) else {
                    unreachable!("issued repair request (Shred) before knowing slice root");
                };
                if !shred.verify_path_only(&root) {
                    warn!("repair response (Shred) with invalid Merkle proof");
                    return;
                }

                // store shred
                let res = self
                    .blockstore
                    .write()
                    .await
                    .add_shred_from_repair(block_hash, shred)
                    .await;
                if let Ok(Some((slot, block_info))) = res {
                    assert_eq!(block_info.hash, block_hash);
                    self.pool
                        .write()
                        .await
                        .add_block((slot, block_info.hash), block_info.parent)
                        .await;
                }
            }
        }
    }

    /// Tries to receive a repair message from the underlying [`Network`].
    ///
    /// Resolves to the next successfully deserialized [`RepairMessage`].
    /// Ignores any potentially received [`NetworkMessage`] of a different type.
    ///
    /// # Errors
    ///
    /// Returns [`NetworkError`] if the underlying network fails.
    async fn receive(&self) -> Result<RepairMessage, NetworkError> {
        loop {
            match self.network.receive().await? {
                NetworkMessage::Repair(r) => return Ok(r),
                m => warn!("unexpected message type for repair: {m:?}"),
            }
        }
    }

    async fn send_request(&mut self, request: RepairRequest) -> Result<(), NetworkError> {
        let hash = request.hash();

        let expiry = Instant::now() + REPAIR_TIMEOUT;
        self.outstanding_requests.insert(hash, request.clone());
        self.request_timeouts.push((expiry, hash));

        let repair = RepairMessage::Request(request, self.epoch_info.own_id);
        let msg: NetworkMessage = repair.into();
        let msg_bytes = msg.to_bytes();
        let to = self.pick_random_peer();
        self.network.send_serialized(&msg_bytes, to).await
    }

    async fn send_response(
        &self,
        response: RepairResponse,
        validator: ValidatorId,
    ) -> Result<(), NetworkError> {
        let msg = RepairMessage::Response(response);
        let to = &self.epoch_info.validator(validator).repair_address;
        self.network.send(&msg.into(), to).await
    }

    fn pick_random_peer(&self) -> &str {
        let mut rng = rand::rng();
        let mut peer_info = self.sampler.sample_info(&mut rng);
        while peer_info.id == self.epoch_info.own_id {
            peer_info = self.sampler.sample_info(&mut rng);
        }
        &peer_info.repair_address
    }
}

impl RepairRequest {
    /// Returns the [`BlockId`] this request refers to.
    #[must_use]
    pub const fn block_id(&self) -> BlockId {
        match self {
            Self::LastSliceRoot(id) | Self::SliceRoot(id, _) | Self::Shred(id, _, _) => *id,
        }
    }

    /// Digests the [`RepairRequest`] into a [`Hash`].
    pub fn hash(&self) -> Hash {
        let repair = RepairMessage::Request(self.clone(), 0);
        let msg: NetworkMessage = repair.into();
        let msg_bytes = msg.to_bytes();
        hash(&msg_bytes)
    }
}

impl RepairResponse {
    /// Returns a reference to the [`RepairRequest`] that this response corresponds to.
    #[must_use]
    pub const fn request(&self) -> &RepairRequest {
        match self {
            Self::LastSliceRoot(req, _, _, _)
            | Self::SliceRoot(req, _, _)
            | Self::Shred(req, _) => req,
        }
    }

    /// Returns the [`BlockId`] this response refers to.
    #[must_use]
    pub const fn block_id(&self) -> BlockId {
        self.request().block_id()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use tokio::sync::mpsc::Sender;

    use super::*;
    use crate::consensus::{BlockstoreImpl, PoolImpl};
    use crate::crypto::signature::SecretKey;
    use crate::network::simulated::{SimulatedNetwork, SimulatedNetworkCore};
    use crate::test_utils::{create_random_shredded_block, generate_validators};
    use crate::types::Slot;
    use crate::types::slice_index::MAX_SLICES_PER_BLOCK;

    /// Creates a small network of 2 validators.
    ///
    /// Validator 0: Is the leader of the genesis window and does not have repair set up.
    /// Validator 1: Has repair set up and is not the leader.
    ///
    /// Returns repair channel sender and blockstore of validator 1.
    /// Also, returns the repair network interface and leader secret key of validator 0.
    async fn create_repair_instance() -> (
        Sender<BlockId>,
        Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
        SimulatedNetwork,
        SecretKey,
    ) {
        // create EpochInfo for 2 validators
        let (_, epoch_info) = generate_validators(2);
        let mut epoch_info = Arc::try_unwrap(epoch_info).unwrap();
        let leader_key = SecretKey::new(&mut rand::rng());
        epoch_info.validators.get_mut(0).unwrap().pubkey = leader_key.to_pk();
        epoch_info.validators.get_mut(0).unwrap().repair_address = "0".to_string();
        epoch_info.validators.get_mut(1).unwrap().repair_address = "1".to_string();
        epoch_info.own_id = 1;
        let epoch_info = Arc::new(epoch_info);

        // set up blockstore
        let (votor_tx, votor_rx) = tokio::sync::mpsc::channel(100);
        let blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>> = Arc::new(RwLock::new(
            Box::new(BlockstoreImpl::new(epoch_info.clone(), votor_tx.clone())),
        ));

        // set up pool
        let (repair_tx, repair_rx) = tokio::sync::mpsc::channel(100);
        let pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>> = Arc::new(RwLock::new(Box::new(
            PoolImpl::new(epoch_info.clone(), votor_tx, repair_tx.clone()),
        )));

        // set up network
        let core = Arc::new(SimulatedNetworkCore::new(1, 0.0, 0.0));
        let network0 = core.join_unlimited(0).await;
        let network1 = core.join_unlimited(1).await;

        // create and start Repair instance
        let mut repair = Repair::new(
            Arc::clone(&blockstore),
            pool,
            network1,
            (repair_tx.clone(), repair_rx),
            epoch_info,
        );
        tokio::spawn(async move {
            repair.repair_loop().await;
            // keep votor_rx alive
            drop(votor_rx);
        });

        (repair_tx, blockstore, network0, leader_key)
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
    async fn repair_large_block() {
        repair_block(MAX_SLICES_PER_BLOCK).await;
    }

    async fn repair_block(num_slices: usize) {
        let (repair_channel, blockstore, other_network, sk) = create_repair_instance().await;

        // create a block to repair
        let slot = Slot::genesis().next();
        let (block_hash, merkle_tree, shreds) = create_random_shredded_block(slot, num_slices, &sk);
        let block_to_repair = (slot, block_hash);

        // ask repair instance to repair this block
        repair_channel.send(block_to_repair).await.unwrap();

        // expect LastSliceRoot request first
        let msg = other_network.receive().await.unwrap();
        let req = RepairRequest::LastSliceRoot(block_to_repair);
        assert!(msg_matches_request(&msg, &req));

        // answer LastSliceRoot request
        let response = RepairResponse::LastSliceRoot(
            req,
            SliceIndex::new_unchecked(num_slices - 1),
            shreds.last().unwrap()[0].merkle_root,
            merkle_tree.create_proof(num_slices - 1),
        );
        let msg = RepairMessage::Response(response).into();
        other_network.send(&msg, "1").await.unwrap();

        // expect SliceRoot requests next
        let mut slice_roots_requested = BTreeSet::new();
        for _ in 0..num_slices {
            let msg = other_network.receive().await.unwrap();

            for slice in SliceIndex::all().take(num_slices) {
                let req = RepairRequest::SliceRoot(block_to_repair, slice);
                if msg_matches_request(&msg, &req) {
                    slice_roots_requested.insert(slice);
                    break;
                }
            }
        }

        // assert all other slice roots requested + answer the requests
        for slice in SliceIndex::all().take(num_slices) {
            assert!(slice_roots_requested.contains(&slice));
            let req = RepairRequest::SliceRoot(block_to_repair, slice);
            let root = shreds[slice.inner()][0].merkle_root;
            let proof = merkle_tree.create_proof(slice.inner());
            let response = RepairResponse::SliceRoot(req, root, proof);
            let msg = RepairMessage::Response(response).into();
            other_network.send(&msg, "1").await.unwrap();

            // expect Shred requests for this slice next
            let mut shreds_requested = BTreeSet::new();
            for _ in 0..DATA_SHREDS {
                let msg = other_network.receive().await.unwrap();
                for shred_index in 0..DATA_SHREDS {
                    let req = RepairRequest::Shred(block_to_repair, slice, shred_index);
                    if msg_matches_request(&msg, &req) {
                        shreds_requested.insert(shred_index);
                        break;
                    }
                }
            }

            // assert all shreds requested + answer the requests
            let slice_shreds = shreds[slice.inner()].clone();
            for (shred_index, shred) in slice_shreds.into_iter().take(DATA_SHREDS).enumerate() {
                assert!(shreds_requested.contains(&shred_index));
                let req = RepairRequest::Shred(block_to_repair, slice, shred_index);
                let response = RepairResponse::Shred(req, shred);
                let msg = RepairMessage::Response(response).into();
                other_network.send(&msg, "1").await.unwrap();
            }
        }

        // after some time block should be repaired
        tokio::time::sleep(Duration::from_millis(100)).await;
        assert!(blockstore.read().await.get_block(block_to_repair).is_some());
    }

    #[tokio::test]
    async fn answer_requests() {
        const SLICES: usize = 2;
        let (_, blockstore, other_network, sk) = create_repair_instance().await;

        // create a block to repair
        let slot = Slot::genesis().next();
        let (block_hash, _, shreds) = create_random_shredded_block(slot, SLICES, &sk);
        let block_to_repair = (slot, block_hash);

        // ingest the block into blockstore
        for slice_shreds in shreds.clone() {
            let mut b = blockstore.write().await;
            for shred in slice_shreds {
                b.add_shred_from_disseminator(shred).await.unwrap();
            }
        }
        assert_eq!(
            blockstore.read().await.canonical_block_hash(slot),
            Some(block_hash)
        );
        assert!(blockstore.read().await.get_block(block_to_repair).is_some());

        // request last slice root to learn how many slices there are
        let request = RepairRequest::LastSliceRoot(block_to_repair);
        let msg = RepairMessage::Request(request.clone(), 0).into();
        other_network.send(&msg, "1").await.unwrap();

        // verify reponse
        let msg = other_network.receive().await.unwrap();
        let RepairResponse::LastSliceRoot(req, last_slice, root, proof) = parse_response(msg)
        else {
            panic!("not LastSliceRoot response");
        };
        assert_eq!(req, request);
        assert_eq!(last_slice.inner(), SLICES - 1);
        assert_eq!(root, shreds[last_slice.inner()][0].merkle_root);
        let correct_proof = blockstore
            .read()
            .await
            .create_double_merkle_proof(block_to_repair, last_slice)
            .unwrap();
        assert_eq!(proof, correct_proof);

        // request slice roots
        for slice in SliceIndex::all().take(SLICES) {
            let request = RepairRequest::SliceRoot(block_to_repair, slice);
            let msg = RepairMessage::Request(request.clone(), 0).into();
            other_network.send(&msg, "1").await.unwrap();

            // verify response
            let msg = other_network.receive().await.unwrap();
            let RepairResponse::SliceRoot(req, root, proof) = parse_response(msg) else {
                panic!("not SliceRoot response");
            };
            assert_eq!(req, request);
            assert_eq!(root, shreds[slice.inner()][0].merkle_root);
            let correct_proof = blockstore
                .read()
                .await
                .create_double_merkle_proof(block_to_repair, slice)
                .unwrap();
            assert_eq!(proof, correct_proof);

            // request slice shreds
            for shred_index in 0..DATA_SHREDS {
                let request = RepairRequest::Shred(block_to_repair, slice, shred_index);
                let msg = RepairMessage::Request(request.clone(), 0).into();
                other_network.send(&msg, "1").await.unwrap();

                // verify response
                let msg = other_network.receive().await.unwrap();
                let RepairResponse::Shred(req, shred) = parse_response(msg) else {
                    panic!("not Shred response");
                };
                assert_eq!(req, request);
                assert_eq!(
                    shred.payload().data,
                    shreds[slice.inner()][shred_index].payload().data
                );
            }
        }
    }

    fn msg_matches_request(msg: &NetworkMessage, request: &RepairRequest) -> bool {
        let NetworkMessage::Repair(repair_msg) = msg else {
            panic!("not a repair msg");
        };
        let RepairMessage::Request(req, _) = repair_msg else {
            panic!("not a request");
        };
        req == request
    }

    fn parse_response(msg: NetworkMessage) -> RepairResponse {
        let NetworkMessage::Repair(repair_msg) = msg else {
            panic!("not a repair msg");
        };
        let RepairMessage::Response(response) = repair_msg else {
            panic!("not a response");
        };
        response
    }
}
