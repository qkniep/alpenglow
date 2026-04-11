// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Block repair sub-protocol.
//!
//! This module implements the double-Merkle based block repair protocol.
//! It uses the fact that the block hash is the root of a Merkle tree, where
//! the leaves of this tree are the Merkle roots of each of the block's slices.
//! Each repair response is accompanied by a Merkle proof and can thus be
//! individually verified.

use std::collections::{BTreeMap, BinaryHeap, HashSet};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use log::{debug, trace, warn};
use tokio::sync::RwLock;
use wincode::{SchemaRead, SchemaWrite};

use crate::consensus::{Blockstore, DELTA, EpochInfo, Pool};
use crate::crypto::merkle::{DoubleMerkleProof, DoubleMerkleTree, MerkleRoot, SliceRoot};
use crate::crypto::{Hash, hash};
use crate::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use crate::network::{Network, RepairNetwork, RepairRequestNetwork};
use crate::shredder::{Shred, ShredIndex};
use crate::types::SliceIndex;
use crate::{BlockId, ValidatorId};

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
            sender: 0,
        };
        let msg_bytes = wincode::serialize(&repair).unwrap();
        hash(&msg_bytes)
    }
}

/// Request messages for the repair sub-protocol.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub struct RepairRequest {
    /// The validator that sent the message.
    sender: ValidatorId,
    /// The type of repair message sent.
    req_type: RepairRequestType,
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
}

impl RepairResponse {
    /// Returns a reference to the [`RepairRequestType`] that this response corresponds to.
    #[must_use]
    const fn request_type(&self) -> &RepairRequestType {
        match self {
            Self::LastSliceRoot(req_type, _, _, _)
            | Self::SliceRoot(req_type, _, _)
            | Self::Shred(req_type, _) => req_type,
        }
    }
}

/// Handle repair requests from other nodes.
///
/// This is separated from [`Repair`] to handle repair requests and responses on separate sockets and tokio tasks.
/// This allows us to prioritise repairing blocks for ourselves over serving repair requests for other nodes.
pub struct RepairRequestHandler<N: Network> {
    epoch_info: Arc<EpochInfo>,
    blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
    network: N,
}

impl<N> RepairRequestHandler<N>
where
    N: RepairRequestNetwork,
{
    /// Creates a new repair request handler instance.
    ///
    /// Given `network` instance will be used for receiving repair requests and sending repair responses.
    /// The blockstore will be used to handle the repair requests.
    pub fn new(
        epoch_info: Arc<EpochInfo>,
        blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
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
            let request = self.network.receive().await.unwrap();
            self.answer_request(request).await.unwrap();
        }
    }

    /// Tries to answer the given repair request.
    ///
    /// If we do not have the necessary information in blockstore, the request is ignored.
    /// Otherwise, the correct response is sent back to the sender of the request.
    async fn answer_request(&self, request: RepairRequest) -> std::io::Result<()> {
        trace!("answering repair request: {request:?}");
        let response = match &request.req_type {
            RepairRequestType::LastSliceRoot(block_id) => {
                let blockstore = self.blockstore.read().await;
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
                RepairResponse::LastSliceRoot(request.req_type, last_slice, root.clone(), proof)
            }
            RepairRequestType::SliceRoot(block_id, slice) => {
                let blockstore = self.blockstore.read().await;
                let Some(root) = blockstore.get_slice_root(block_id, *slice) else {
                    return Ok(());
                };
                let Some(proof) = blockstore.create_double_merkle_proof(block_id, *slice) else {
                    return Ok(());
                };
                RepairResponse::SliceRoot(request.req_type, root.clone(), proof)
            }
            RepairRequestType::Shred(block_id, slice, shred) => {
                let blockstore = self.blockstore.read().await;
                let Some(shred) = blockstore.get_shred(block_id, *slice, *shred).cloned() else {
                    return Ok(());
                };
                RepairResponse::Shred(request.req_type, shred.into_shred())
            }
        };
        self.send_response(response, request.sender).await
    }

    async fn send_response(
        &self,
        response: RepairResponse,
        validator: ValidatorId,
    ) -> std::io::Result<()> {
        let to = self.epoch_info.validator(validator).repair_response_address;
        self.network.send(&response, to).await
    }
}

/// Instance of double-Merkle based block repair protocol.
///
/// This is used by the node to repair blocks that it is missing.
/// This does not answer repair requests from other nodes, that is handled by [`RepairRequestHandler`].
pub struct Repair<N: Network> {
    blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
    pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,
    slice_roots: BTreeMap<(BlockId, SliceIndex), SliceRoot>,
    outstanding_requests: BTreeMap<Hash, RepairRequestType>,
    request_timeouts: BinaryHeap<(Instant, Hash)>,
    network: N,
    sampler: StakeWeightedSampler,
    epoch_info: Arc<EpochInfo>,
}

impl<N> Repair<N>
where
    N: RepairNetwork,
{
    /// Creates a new repair instance.
    ///
    /// Given `network` will be used for sending repair requests and receiving repair responses.
    /// Any repaired shreds will be written into the provided `blockstore`.
    pub fn new(
        blockstore: Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
        pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,
        network: N,
        epoch_info: Arc<EpochInfo>,
    ) -> Self {
        let validators = epoch_info.validators.clone();
        let sampler = StakeWeightedSampler::new(validators);
        Self {
            blockstore,
            pool,
            slice_roots: BTreeMap::new(),
            outstanding_requests: BTreeMap::new(),
            request_timeouts: BinaryHeap::new(),
            network,
            sampler,
            epoch_info,
        }
    }

    /// Main loop of the repair protocol.
    ///
    /// Listens to incoming requests for blocks to repair on `self.repair_channel`.
    /// Inititates the corresponding repair process and handles ongoing repairs.
    pub async fn repair_loop(&mut self, mut repair_receiver: tokio::sync::mpsc::Receiver<BlockId>) {
        loop {
            let next_timeout = self.request_timeouts.peek().map(|(t, _)| t);
            let sleep_duration = match next_timeout {
                None => std::time::Duration::MAX,
                Some(t) => t.duration_since(Instant::now()),
            };
            tokio::select! {
                // handle repair response from network
                res = self.network.receive() => self.handle_response(res.unwrap()).await,
                // handle request for repairing new block
                Some(block_id) = repair_receiver.recv() => {
                    self.repair_block(block_id).await;
                }
                // handle next request timeout
                () = tokio::time::sleep(sleep_duration) => {
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
        let (slot, block_hash) = &block_id;
        let h = &hex::encode(block_hash.as_hash())[..8];
        if self.blockstore.read().await.get_block(&block_id).is_some() {
            trace!("ignoring repair for block {h} in slot {slot}, already have the block");
            return;
        }

        debug!("repairing block {h} in slot {slot}");
        let req = RepairRequestType::LastSliceRoot(block_id);
        self.send_request(req).await.unwrap();
    }

    /// Handles a repair response, storing the received data.
    ///
    /// If the response contains a shred, it will be stored in the [`Blockstore`].
    /// Otherwise, metadata is stored in the [`Repair`] struct itself.
    /// Does nothing if the provided `response` is not well-formed.
    async fn handle_response(&mut self, response: RepairResponse) {
        trace!("handling repair response: {response:?}");
        let request_hash = response.request_type().hash();

        // check whether we are (still) waiting on response to this request
        let Some(_) = self.outstanding_requests.remove(&request_hash) else {
            warn!("received repair response for unknown request {response:?}");
            return;
        };

        match response {
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
                    self.send_request(req_type).await.unwrap();
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
                    self.send_request(req).await.unwrap();
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
                if !shred.verify_path_only(root) {
                    warn!("repair response (Shred) with invalid Merkle proof");
                    return;
                }

                // store shred
                let res = self
                    .blockstore
                    .write()
                    .await
                    .add_shred_from_repair(block_hash.clone(), shred)
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
                        &hex::encode(block_hash.as_hash())[..8],
                        slot
                    );
                }
            }
        }
    }

    async fn send_request(&mut self, req_type: RepairRequestType) -> std::io::Result<()> {
        let hash = req_type.hash();

        let expiry = Instant::now() + REPAIR_TIMEOUT;
        self.outstanding_requests
            .insert(hash.clone(), req_type.clone());
        self.request_timeouts.retain(|(_, h)| h != &hash);
        self.request_timeouts.push((expiry, hash));

        let request = RepairRequest {
            sender: self.epoch_info.own_id,
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
        self.network
            .send_to_many(&request, to_all.into_iter())
            .await?;
        Ok(())
    }

    fn pick_random_peer(&self) -> SocketAddr {
        let mut rng = rand::rng();
        let mut peer_info = self.sampler.sample_info(&mut rng);
        while peer_info.id == self.epoch_info.own_id {
            peer_info = self.sampler.sample_info(&mut rng);
        }
        peer_info.repair_request_address
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use tokio::sync::mpsc::Sender;

    use super::*;
    use crate::consensus::{BlockstoreImpl, PoolImpl};
    use crate::crypto::signature::SecretKey;
    use crate::network::simulated::SimulatedNetworkCore;
    use crate::network::{SimulatedNetwork, localhost_ip_sockaddr};
    use crate::shredder::TOTAL_SHREDS;
    use crate::test_utils::{create_random_shredded_block, generate_validators};
    use crate::types::Slot;
    use crate::types::slice_index::MAX_SLICES_PER_BLOCK;

    /// Creates a small network of 2 validators.
    ///
    /// Validator 0: Is the leader of the genesis window and does not have repair set up.
    /// Validator 1: Has repair set up and is not the leader.
    ///
    /// Returns:
    /// - sender side of the repair channel for validator 1
    /// - blockstore of validator 1
    /// - network interface where validator 0 should accept [`RepairRequest`] messages
    /// - network interface where validator 0 should accept [`RepairResponse`] messages
    /// - leader secret key of validator 0
    async fn create_repair_instance() -> (
        Sender<BlockId>,
        Arc<RwLock<Box<dyn Blockstore + Send + Sync>>>,
        SimulatedNetwork<RepairResponse, RepairRequest>,
        SimulatedNetwork<RepairRequest, RepairResponse>,
        SecretKey,
    ) {
        // create EpochInfo for 2 validators and the corresponding network
        let (_, epoch_info) = generate_validators(2);
        let mut epoch_info = Arc::try_unwrap(epoch_info).unwrap();
        let leader_key = SecretKey::new(&mut rand::rng());
        let v0 = epoch_info.validators.get_mut(0).unwrap();
        v0.pubkey = leader_key.to_pk();
        v0.repair_request_address = localhost_ip_sockaddr(0);
        v0.repair_response_address = localhost_ip_sockaddr(1);

        let core = Arc::new(SimulatedNetworkCore::new(1, 0.0, 0.0));
        let v0_repair_request_network = core
            .join_unlimited(v0.repair_request_address.port() as u64)
            .await;
        let v0_repair_network = core
            .join_unlimited(v0.repair_response_address.port() as u64)
            .await;

        let v1 = epoch_info.validators.get_mut(1).unwrap();
        v1.repair_request_address = localhost_ip_sockaddr(2);
        v1.repair_response_address = localhost_ip_sockaddr(3);
        epoch_info.own_id = 1;

        let v1_repair_request_network = core
            .join_unlimited(v1.repair_request_address.port() as u64)
            .await;
        let v1_repair_network = core
            .join_unlimited(v1.repair_response_address.port() as u64)
            .await;

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

        // create and start Repair instance
        let mut repair = Repair::new(
            Arc::clone(&blockstore),
            pool,
            v1_repair_network,
            epoch_info.clone(),
        );
        tokio::spawn(async move {
            repair.repair_loop(repair_rx).await;
            // keep votor_rx alive
            drop(votor_rx);
        });
        let repair_request_handler =
            RepairRequestHandler::new(epoch_info, blockstore.clone(), v1_repair_request_network);
        tokio::spawn(async move {
            repair_request_handler.run().await;
        });
        (
            repair_tx,
            blockstore,
            v0_repair_request_network,
            v0_repair_network,
            leader_key,
        )
    }

    #[tokio::test]
    async fn repair_tiny_block() {
        repair_block(1).await;
    }

    #[tokio::test]
    async fn repair_regular_block() {
        repair_block(10).await;
    }

    // test takes a long time to run in debug mode.
    // so ignored for normal runs and ran as part of sequential tests
    #[tokio::test]
    #[ignore]
    async fn repair_large_block() {
        repair_block(MAX_SLICES_PER_BLOCK).await;
    }

    async fn repair_block(num_slices: usize) {
        let (repair_channel, blockstore, other_network_request, _other_network_reply, sk) =
            create_repair_instance().await;

        // create a block to repair
        let slot = Slot::genesis().next();
        let (block_hash, merkle_tree, shreds) = create_random_shredded_block(slot, num_slices, &sk);
        let block_to_repair = (slot, block_hash);

        // ask repair instance to repair this block
        repair_channel.send(block_to_repair.clone()).await.unwrap();

        // expect LastSliceRoot request first
        let msg = other_network_request.receive().await.unwrap();
        let req_type = RepairRequestType::LastSliceRoot(block_to_repair.clone());
        assert_eq!(msg.req_type, req_type);

        // answer LastSliceRoot request
        let response = RepairResponse::LastSliceRoot(
            req_type,
            SliceIndex::new_unchecked(num_slices - 1),
            shreds.last().unwrap()[0].merkle_root.clone(),
            merkle_tree.create_proof(num_slices - 1),
        );
        let port1 = localhost_ip_sockaddr(3);
        other_network_request.send(&response, port1).await.unwrap();

        // expect SliceRoot requests next
        let mut slice_roots_requested = BTreeSet::new();
        for _ in 0..num_slices {
            let msg = other_network_request.receive().await.unwrap();

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
            let root = shreds[slice.inner()][0].merkle_root.clone();
            let proof = merkle_tree.create_proof(slice.inner());
            let response = RepairResponse::SliceRoot(req_type, root, proof);
            other_network_request.send(&response, port1).await.unwrap();

            // expect Shred requests for this slice next
            let mut shreds_requested = BTreeSet::new();
            for _ in ShredIndex::all() {
                let msg = other_network_request.receive().await.unwrap();
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
                other_network_request.send(&response, port1).await.unwrap();
            }
        }

        // after some time block should be repaired
        tokio::time::sleep(Duration::from_millis(100)).await;
        assert!(
            blockstore
                .read()
                .await
                .get_block(&block_to_repair)
                .is_some()
        );
    }

    #[tokio::test]
    async fn answer_requests() {
        const SLICES: usize = 2;
        let (_sender, blockstore, _other_network_request, other_network, sk) =
            create_repair_instance().await;

        // create a block to repair
        let slot = Slot::genesis().next();
        let (block_hash, _, shreds) = create_random_shredded_block(slot, SLICES, &sk);
        let block_to_repair = (slot, block_hash.clone());

        // ingest the block into blockstore
        for slice_shreds in shreds.clone() {
            let mut b = blockstore.write().await;
            for shred in slice_shreds {
                let _ = b.add_shred_from_disseminator(shred.into_shred()).await;
            }
        }
        assert_eq!(
            blockstore.read().await.disseminated_block_hash(slot),
            Some(&block_hash)
        );
        assert!(
            blockstore
                .read()
                .await
                .get_block(&block_to_repair)
                .is_some()
        );

        // request last slice root to learn how many slices there are
        let request = RepairRequest {
            req_type: RepairRequestType::LastSliceRoot(block_to_repair.clone()),
            sender: 0,
        };
        let port1 = localhost_ip_sockaddr(2);
        other_network.send(&request, port1).await.unwrap();

        // verify reponse
        let msg = other_network.receive().await.unwrap();
        let RepairResponse::LastSliceRoot(req_type, last_slice, root, proof) = msg else {
            panic!("not LastSliceRoot response");
        };
        assert_eq!(req_type, request.req_type);
        assert_eq!(last_slice.inner(), SLICES - 1);
        assert_eq!(root, shreds[last_slice.inner()][0].merkle_root);
        let correct_proof = blockstore
            .read()
            .await
            .create_double_merkle_proof(&block_to_repair, last_slice)
            .unwrap();
        assert_eq!(proof, correct_proof);

        // request slice roots
        for slice in SliceIndex::all().take(SLICES) {
            let request = RepairRequest {
                req_type: RepairRequestType::SliceRoot(block_to_repair.clone(), slice),
                sender: 0,
            };
            other_network.send(&request, port1).await.unwrap();

            // verify response
            let msg = other_network.receive().await.unwrap();
            let RepairResponse::SliceRoot(req_type, root, proof) = msg else {
                panic!("not SliceRoot response");
            };
            assert_eq!(req_type, request.req_type);
            assert_eq!(root, shreds[slice.inner()][0].merkle_root);
            let correct_proof = blockstore
                .read()
                .await
                .create_double_merkle_proof(&block_to_repair, slice)
                .unwrap();
            assert_eq!(proof, correct_proof);

            // request slice shreds
            for shred_index in ShredIndex::all() {
                let request = RepairRequest {
                    req_type: RepairRequestType::Shred(block_to_repair.clone(), slice, shred_index),
                    sender: 0,
                };
                other_network.send(&request, port1).await.unwrap();

                // verify response
                let msg = other_network.receive().await.unwrap();
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
