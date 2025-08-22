// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Block repair sub-protocol.
//!
//! This module implements the double-Merkle based block repair protocol.
//! It uses the fact that the block hash is the root of a Merkle tree, where
//! the leaves of this tree are the Merkle roots of each of the block's slices.
//! Each repair response is accompanied by a Merkle proof and can thus be
//! individually verified.

// WARN: this is incomplete!

use std::collections::{BTreeMap, BinaryHeap};
use std::sync::Arc;
use std::time::{Duration, Instant};

use log::{debug, trace, warn};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::BlockId;
use crate::consensus::{Blockstore, EpochInfo, Pool};
use crate::crypto::{Hash, hash};
use crate::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use crate::network::{Network, NetworkError, NetworkMessage};
use crate::shredder::{Shred, TOTAL_SHREDS};
use crate::types::SliceIndex;

/// Message types for the repair sub-protocol.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairMessage {
    /// Request for information from another validator.
    Request(RepairRequest),
    /// Response to a request from another validator.
    Response(RepairResponse),
}

/// Request messages for the repair sub-protocol.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RepairRequest {
    /// Request for the total number of slices in block with a given hash.
    SliceCount(BlockId),
    /// Request for the root hash of a slice, identified by block hash and slice index.
    SliceRoot(BlockId, SliceIndex),
    /// Request for shred, identified by block hash, slice index and shred index.
    Shred(BlockId, SliceIndex, usize),
    // TODO: remove or replace with variant that includes proof
    Parent(BlockId),
}

/// Response messages for the repair sub-protocol.
///
/// Each response type corresponds to a specific request message type.
/// Each response contains the request message that it is a response to.
/// If well-formed, it thus contains the corresponding variant of [`RepairRequest`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairResponse {
    /// Response with the total number of slices for a specific block.
    SliceCount(RepairRequest, usize),
    /// Response with the Merkle root hash of a specific slice, plus corresponding proof.
    SliceRoot(RepairRequest, Hash, Vec<Hash>),
    /// Response with a specific shred.
    Shred(RepairRequest, Shred),
    // TODO: remove or replace with variant that includes proof
    Parent(RepairRequest, BlockId),
}

/// Instance of double-Merkle based block repair protocol.
pub struct Repair<N: Network> {
    blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
    pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,

    outstanding_requests: BTreeMap<Hash, RepairRequest>,
    request_timeouts: BinaryHeap<(Instant, Hash)>,

    network: N,
    repair_channel: (
        tokio::sync::mpsc::Sender<BlockId>,
        Option<tokio::sync::mpsc::Receiver<BlockId>>,
    ),
    sampler: StakeWeightedSampler,
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
            outstanding_requests: BTreeMap::new(),
            request_timeouts: BinaryHeap::new(),
            network,
            repair_channel,
            sampler,
        }
    }

    /// Main loop of the repair protocol.
    ///
    /// Listens to incoming requests for blocks to repair on `self.repair_channel`.
    /// Inititates the corresponding repair process and handles ongoing repairs.
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
        // TODO: perform actual repair
        let req = RepairRequest::Parent(block_id);
        self.send_request(req).await.unwrap();
    }

    async fn handle_repair_message(&mut self, msg: RepairMessage) -> Result<(), NetworkError> {
        match msg {
            RepairMessage::Request(request) => {
                self.answer_request(request).await?;
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
    async fn answer_request(&self, request: RepairRequest) -> Result<(), NetworkError> {
        trace!("answering repair request: {request:?}");
        let (slot, hash) = request.block_id();
        let blockstore = self.blockstore.read().await;
        // TODO: answer repair requests for non-canonical blocks
        if blockstore.canonical_block_hash(slot) != Some(hash) {
            return Ok(());
        }
        let response = match request {
            RepairRequest::SliceCount(_) => {
                let k = blockstore.stored_shreds_for_slot(slot) / TOTAL_SHREDS;
                RepairResponse::SliceCount(request, k)
            }
            RepairRequest::SliceRoot(_, slice) => {
                let shred_index = slice.inner() * TOTAL_SHREDS;
                let Some(shred) = blockstore.get_shred(slot, slice, shred_index) else {
                    return Ok(());
                };
                let root = shred.merkle_root;
                let proof = blockstore.create_double_merkle_proof(slot, slice);
                RepairResponse::SliceRoot(request, root, proof)
            }
            RepairRequest::Shred(_, slice, shred) => {
                let Some(shred) = blockstore.get_shred(slot, slice, shred).cloned() else {
                    return Ok(());
                };
                RepairResponse::Shred(request, shred)
            }
            // TODO: remove this
            RepairRequest::Parent(block_id) => {
                let Some(block) = blockstore.get_block(block_id) else {
                    return Ok(());
                };
                let parent = (block.parent, block.parent_hash);
                RepairResponse::Parent(request, parent)
            }
        };
        drop(blockstore);
        self.send_response(response).await
    }

    /// Handles a repair response, storing the received data.
    ///
    /// If the response contains a shred, it will be stored in the [`Blockstore`].
    /// Otherwise, metadata is stored in the [`Repair`] struct itself.
    /// Does nothing if the provided `response` is not well-formed.
    async fn handle_response(&mut self, response: RepairResponse) {
        trace!("handling repair response: {response:?}");
        // TODO: expose `hash()` function for `RepairRequest` instead?
        let repair = RepairMessage::Request(response.request().clone());
        let msg: NetworkMessage = repair.into();
        let msg_bytes = msg.to_bytes();
        let request_hash = hash(&msg_bytes);

        let block_id = response.block_id();
        let (slot, block_hash) = block_id;
        // TODO: check whether we actually sent the request
        match response {
            RepairResponse::SliceCount(req, count) => {
                let RepairRequest::SliceCount(_) = req else {
                    warn!("repair response (SliceCount) to mismatching request {req:?}");
                    return;
                };
                // TODO: include & check proof:
                // self.slice_counts.insert((slot, block_hash), count);
                for slice in SliceIndex::all().take(count) {
                    let req = RepairRequest::SliceRoot(block_id, slice);
                    self.send_request(req).await.unwrap();
                }
            }
            RepairResponse::SliceRoot(req, _slice_root, _proof) => {
                let RepairRequest::SliceRoot(_, _slice) = req else {
                    warn!("repair response (SliceRoot) to mismatching request {req:?}");
                    return;
                };
                // TODO: check Merkle proof & cache it:
                // if !MerkleTree::check_hash_proof(slice_root, slice, block_hash, &proof) {
                //     return;
                // }
                // self.slice_roots
                //     .insert((slot, block_hash, slice), slice_root);
            }
            RepairResponse::Shred(req, shred) => {
                let RepairRequest::Shred(_, slice, index) = req else {
                    warn!("repair response (Shred) to mismatching request {req:?}");
                    return;
                };
                if shred.payload().header.slot != slot
                    || shred.payload().header.slice_index != slice
                    || shred.payload().index_in_slice != index
                {
                    return;
                }
                // TODO: make sure shred is checked against correct merkle_root:
                // if !shred.merkle_root ... { return; }
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
            // TODO: remove this
            RepairResponse::Parent(req, parent) => {
                let RepairRequest::Parent(_) = req else {
                    warn!("repair response (Parent) to mismatching request {req:?}");
                    return;
                };
                self.pool.write().await.add_block(block_id, parent).await;

                // request repair of the parent block if necessary
                if self.blockstore.read().await.get_block(parent).is_none() {
                    self.repair_channel.0.send(parent).await.unwrap();
                }
            }
        }
        self.outstanding_requests.remove(&request_hash);
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
        let repair = RepairMessage::Request(request.clone());
        let msg: NetworkMessage = repair.into();
        let msg_bytes = msg.to_bytes();
        let hash = hash(&msg_bytes);

        let expiry = Instant::now() + Duration::from_secs(10);
        self.outstanding_requests.insert(hash, request);
        self.request_timeouts.push((expiry, hash));

        let to = &self.sampler.sample_info(&mut rand::rng()).repair_address;
        self.network.send_serialized(&msg_bytes, to).await
    }

    async fn send_response(&self, response: RepairResponse) -> Result<(), NetworkError> {
        let repair = RepairMessage::Response(response);
        // TODO: send back to correct validator
        let to = &self.sampler.sample_info(&mut rand::rng()).repair_address;
        self.network.send(&repair.into(), to).await
    }
}

impl RepairRequest {
    /// Returns the [`BlockId`] this request refers to.
    #[must_use]
    pub const fn block_id(&self) -> BlockId {
        match self {
            Self::SliceCount(block_id)
            | Self::SliceRoot(block_id, _)
            | Self::Shred(block_id, _, _)
            | Self::Parent(block_id) => *block_id,
        }
    }
}

impl RepairResponse {
    /// Returns a reference to the [`RepairRequest`] that this response corresponds to.
    #[must_use]
    pub const fn request(&self) -> &RepairRequest {
        match self {
            Self::SliceCount(req, _)
            | Self::SliceRoot(req, _, _)
            | Self::Shred(req, _)
            | Self::Parent(req, _) => req,
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
    use super::*;

    use crate::consensus::{BlockstoreImpl, PoolImpl};
    use crate::network::simulated::{SimulatedNetwork, SimulatedNetworkCore};
    use crate::test_utils::generate_validators;
    use crate::types::Slot;

    use tokio::sync::mpsc::Sender;

    async fn create_repair_instance() -> (
        Sender<BlockId>,
        SimulatedNetwork,
        Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
    ) {
        let (_, epoch_info) = generate_validators(2);
        let mut epoch_info = Arc::try_unwrap(epoch_info).unwrap();
        epoch_info.validators.get_mut(0).unwrap().repair_address = "0".to_string();
        epoch_info.validators.get_mut(1).unwrap().repair_address = "1".to_string();
        let epoch_info = Arc::new(epoch_info);

        let (votor_tx, _) = tokio::sync::mpsc::channel(100);
        let blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>> = Arc::new(RwLock::new(
            Box::new(BlockstoreImpl::new(epoch_info.clone(), votor_tx.clone())),
        ));

        let (repair_tx, repair_rx) = tokio::sync::mpsc::channel(100);
        let pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>> = Arc::new(RwLock::new(Box::new(
            PoolImpl::new(epoch_info.clone(), votor_tx, repair_tx.clone()),
        )));

        let core = Arc::new(SimulatedNetworkCore::new(100, 0.0, 0.0));
        let network0 = core.join_unlimited(0).await;
        let network1 = core.join_unlimited(1).await;

        let mut repair = Repair::new(
            Arc::clone(&blockstore),
            pool,
            network0,
            (repair_tx.clone(), repair_rx),
            epoch_info,
        );

        tokio::spawn(async move { repair.repair_loop().await });

        (repair_tx, network1, blockstore)
    }

    #[tokio::test]
    async fn basic() {
        let (repair_channel, other_network, _) = create_repair_instance().await;
        let block_to_repair = (Slot::genesis().next(), [1; 32]);
        repair_channel.send(block_to_repair).await.unwrap();
        let Ok(msg) = other_network.receive().await else {
            panic!("failed to receive");
        };
        // ...
    }

    #[tokio::test]
    async fn shred_based_repair() {
        let (repair_channel, other_network, blockstore) = create_repair_instance().await;
        let block_to_repair = (Slot::genesis().next(), [1; 32]);
        let req = RepairRequest::Shred(block_to_repair, SliceIndex::first(), 0);
        let msg = RepairMessage::Request(req).into();
        other_network.send(&msg, "0").await.unwrap();
        // ...
    }

    // TODO: remove this
    #[tokio::test]
    async fn parent_based_repair() {
        let (repair_channel, other_network, _) = create_repair_instance().await;
        let block_to_repair = (Slot::genesis().next(), [1; 32]);
        repair_channel.send(block_to_repair).await.unwrap();
        let Ok(msg) = other_network.receive().await else {
            panic!("failed to receive");
        };
        let req = RepairRequest::Parent(block_to_repair);
        assert_msg_matches_request(&msg, &req);
        let parent = (Slot::genesis(), Hash::default());
        let response = RepairResponse::Parent(req, parent);
        let msg = RepairMessage::Response(response).into();
        other_network.send(&msg, "0").await.unwrap();
    }

    fn assert_msg_matches_request(msg: &NetworkMessage, request: &RepairRequest) {
        let NetworkMessage::Repair(repair_msg) = msg else {
            panic!("not a repair msg");
        };
        let RepairMessage::Request(req) = repair_msg else {
            panic!("not a request");
        };
        assert_eq!(req, request);
    }
}
