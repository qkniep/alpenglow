// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Block repair sub-protocol.
//!
//!
// WARN: this is incomplete!

use std::collections::BTreeMap;
use std::sync::Arc;

use log::warn;
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::Slot;
use crate::consensus::{Blockstore, EpochInfo};
use crate::crypto::{Hash, MerkleTree};
use crate::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use crate::network::{Network, NetworkError, NetworkMessage};
use crate::shredder::{Shred, TOTAL_SHREDS};

/// Message types for the repair sub-protocol.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairMessage {
    /// Request for information from another validator.
    Request(RepairRequest),
    /// Response to a request from another validator.
    Response(RepairResponse),
}

/// Request messages for the repair sub-protocol.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairRequest {
    /// Request for the total number of slices in block with a given hash.
    SliceCount(Slot, Hash),
    /// Request for the root hash of a slice, identified by block hash and slice index.
    SliceRoot(Slot, Hash, usize),
    /// Request for shred, identified by block hash, slice index and shred index.
    Shred(Slot, Hash, usize, usize),
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
}

/// Instance of double-Merkle based block repair protocol.
pub struct Repair<N: Network> {
    blockstore: Arc<RwLock<Blockstore>>,
    network: N,
    sampler: StakeWeightedSampler,
    slice_counts: BTreeMap<(Slot, Hash), usize>,
    slice_roots: BTreeMap<(Slot, Hash, usize), Hash>,
}

impl<N: Network> Repair<N> {
    /// Creates a new repair instance.
    ///
    /// Given `network` will be used for sending and receiving repair messages.
    /// Any repaired shreds will be written into the provided `blockstore`.
    pub fn new(
        blockstore: Arc<RwLock<Blockstore>>,
        network: N,
        epoch_info: Arc<EpochInfo>,
    ) -> Self {
        let validators = epoch_info.validators.clone();
        let sampler = StakeWeightedSampler::new(validators);
        Self {
            blockstore,
            network,
            sampler,
            slice_counts: BTreeMap::new(),
            slice_roots: BTreeMap::new(),
        }
    }

    /// Starts repair process for the block specified by `slot` and `block_hash`.
    pub async fn repair_block(&self, slot: Slot, block_hash: Hash) {
        unimplemented!()
    }

    /// Tries to answer the given repair request.
    ///
    /// If we do not have the block the request refers to, the request is ignored.
    /// Otherwise, the correct response is sent back to the sender of the request.
    pub async fn answer_request(&self, request: RepairRequest) -> Result<(), NetworkError> {
        let slot = request.slot();
        let hash = request.block_hash();
        let blockstore = self.blockstore.read().await;
        if blockstore.canonical_block_hash(slot) != Some(hash) {
            return Ok(());
        }
        let response = match request {
            RepairRequest::SliceCount(_, _) => {
                let k = blockstore.stored_shreds_for_slot(slot) / TOTAL_SHREDS;
                RepairResponse::SliceCount(request, k)
            }
            RepairRequest::SliceRoot(_, _, slice) => {
                let shred_index = slice * TOTAL_SHREDS;
                let shred = blockstore.get_shred(slot, slice, shred_index).unwrap();
                let root = shred.merkle_root();
                let proof = blockstore.create_double_merkle_proof(slot, slice);
                RepairResponse::SliceRoot(request, root, proof)
            }
            RepairRequest::Shred(_, _, slice, shred) => {
                let shred = blockstore.get_shred(slot, slice, shred).unwrap().clone();
                RepairResponse::Shred(request, shred)
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
    pub async fn handle_response(&mut self, response: RepairResponse) {
        let slot = response.slot();
        let block_hash = response.block_hash();
        match response {
            RepairResponse::SliceCount(req, count) => {
                let RepairRequest::SliceCount(_, _) = req else {
                    return;
                };
                // TODO: include & check proof
                self.slice_counts.insert((slot, block_hash), count);
            }
            RepairResponse::SliceRoot(req, slice_root, proof) => {
                let RepairRequest::SliceRoot(_, _, slice) = req else {
                    return;
                };
                if !MerkleTree::check_hash_proof(slice_root, slice, block_hash, &proof) {
                    return;
                }
                self.slice_roots
                    .insert((slot, block_hash, slice), slice_root);
            }
            RepairResponse::Shred(req, shred) => {
                let RepairRequest::Shred(_, _, slice, index) = req else {
                    return;
                };
                if shred.slot() != slot || shred.slice() == slice || shred.index_in_slice() == index
                {
                    return;
                }
                // TODO: make sure shred is checked against correct merkle_root
                //
                /* if !shred.merkle_root ... { return; } */
                self.blockstore.write().await.add_shred(shred).await;
            }
        };
    }

    /// Tries to receive and deserialize messages from the underlying network.
    ///
    /// Resolves to the next successfully deserialized [`RepairMessage`].
    /// Ignores any potentially received [`NetworkMessage`] of a different type.
    ///
    /// # Errors
    ///
    /// Returns [`NetworkError`] if the underlying network fails.
    pub async fn receive(&self) -> Result<RepairMessage, NetworkError> {
        loop {
            match self.network.receive().await? {
                NetworkMessage::Repair(r) => return Ok(r),
                m => warn!("unexpected message type for repair: {:?}", m),
            }
        }
    }

    async fn request_slice_count(&self, slot: Slot, hash: Hash) -> Result<(), NetworkError> {
        let req = RepairRequest::SliceCount(slot, hash);
        self.send_request(req).await
    }

    async fn request_slice_root(
        &self,
        slot: Slot,
        hash: Hash,
        slice: usize,
    ) -> Result<(), NetworkError> {
        let req = RepairRequest::SliceRoot(slot, hash, slice);
        self.send_request(req).await
    }

    async fn request_shred(
        &self,
        slot: Slot,
        hash: Hash,
        slice: usize,
        shred: usize,
    ) -> Result<(), NetworkError> {
        let req = RepairRequest::Shred(slot, hash, slice, shred);
        self.send_request(req).await
    }

    async fn send_request(&self, request: RepairRequest) -> Result<(), NetworkError> {
        let repair = RepairMessage::Request(request);
        let msg = NetworkMessage::Repair(repair);
        let to = &self.sampler.sample_info(&mut rand::rng()).repair_address;
        self.network.send(&msg, to).await
    }

    async fn send_response(&self, response: RepairResponse) -> Result<(), NetworkError> {
        let repair = RepairMessage::Response(response);
        let msg = NetworkMessage::Repair(repair);
        // TODO: send back to correct validator
        let to = &self.sampler.sample_info(&mut rand::rng()).repair_address;
        self.network.send(&msg, to).await
    }
}

impl RepairRequest {
    /// Returns the slot number this request refers to.
    pub fn slot(&self) -> Slot {
        match self {
            Self::SliceCount(slot, _)
            | Self::SliceRoot(slot, _, _)
            | Self::Shred(slot, _, _, _) => *slot,
        }
    }

    /// Returns the block hash this response refers to.
    pub fn block_hash(&self) -> Hash {
        match self {
            Self::SliceCount(_, hash)
            | Self::SliceRoot(_, hash, _)
            | Self::Shred(_, hash, _, _) => *hash,
        }
    }
}

impl RepairResponse {
    /// Returns a reference to the [`RepairRequest`] that this response corresponds to.
    pub fn request(&self) -> &RepairRequest {
        match self {
            Self::SliceCount(req, _) | Self::SliceRoot(req, _, _) | Self::Shred(req, _) => req,
        }
    }

    /// Returns the slot number this response refers to.
    pub fn slot(&self) -> Slot {
        self.request().slot()
    }

    /// Returns the block hash this response refers to.
    pub fn block_hash(&self) -> Hash {
        self.request().block_hash()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {}
}
