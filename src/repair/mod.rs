// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use tracing::warn;

use crate::crypto::Hash;
use crate::disseminator::rotor::{SamplingStrategy, StakeWeightedSampler};
use crate::network::{Network, NetworkError, NetworkMessage};
use crate::shredder::Shred;
use crate::{Slot, ValidatorId, ValidatorInfo};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairMessage {
    Request(RepairRequest),
    Response(RepairResponse),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairRequest {
    SliceCount(Hash),
    SliceRoot(Hash, u64),
    Shred(Hash, u64, u64),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepairResponse {
    SliceCount(RepairRequest, usize),
    SliceRoot(RepairRequest, Hash),
    Shred(RepairRequest, Shred),
}

/// Implementation of double-Merkle based block repair protocol.
pub struct Repair<N: Network> {
    own_id: ValidatorId,
    validators: Vec<ValidatorInfo>,
    network: N,
    sampler: StakeWeightedSampler,
}

impl<N: Network> Repair<N> {
    pub fn new(own_id: ValidatorId, validators: Vec<ValidatorInfo>, network: N) -> Self {
        let sampler = StakeWeightedSampler::new(validators.clone());
        Self {
            own_id,
            validators,
            network,
            sampler,
        }
    }

    pub async fn repair_block(&self, slot: Slot, block_hash: Hash) {
        let k = self.request_slice_count(block_hash).await;
    }

    pub async fn answer_request(&self, request: RepairRequest) -> Result<(), NetworkError> {
        let response = match request {
            RepairRequest::SliceCount(hash) => RepairResponse::SliceCount(request, 0),
            RepairRequest::SliceRoot(hash, slice) => {
                RepairResponse::SliceRoot(request, Hash::default())
            }
            RepairRequest::Shred(_, _, _) => unimplemented!(),
            // RepairRequest::Shred(hash, slice, shred) => RepairResponse::Shred(request, Shred::default()),
        };
        self.send_response(response).await
    }

    /// Tries to receive and deserialize messages from the underlying network.
    /// Resolves to the next successfully deserialized `RepairMessage`.
    ///
    /// # Errors
    ///
    /// Returns `NetworkError` if the underlying network fails.
    pub async fn receive(&self) -> Result<RepairMessage, NetworkError> {
        loop {
            match self.network.receive().await? {
                NetworkMessage::Repair(r) => return Ok(r),
                m => warn!("unexpected message type for repair: {:?}", m),
            }
        }
    }

    async fn request_slice_count(&self, hash: Hash) -> Result<(), NetworkError> {
        let req = RepairRequest::SliceCount(hash);
        self.send_request(req).await
    }

    async fn request_slice_root(&self, hash: Hash, slice: u64) -> Result<(), NetworkError> {
        let req = RepairRequest::SliceRoot(hash, slice);
        self.send_request(req).await
    }

    async fn request_shred(&self, hash: Hash, slice: u64, shred: u64) -> Result<(), NetworkError> {
        let req = RepairRequest::Shred(hash, slice, shred);
        self.send_request(req).await
    }

    async fn send_request(&self, request: RepairRequest) -> Result<(), NetworkError> {
        let repair = RepairMessage::Request(request);
        let msg = NetworkMessage::Repair(repair);
        let to = &self.sampler.sample(&mut rand::rng()).repair_address;
        self.network.send(&msg, to).await
    }

    async fn send_response(&self, response: RepairResponse) -> Result<(), NetworkError> {
        let repair = RepairMessage::Response(response);
        let msg = NetworkMessage::Repair(repair);
        let to = &self.sampler.sample(&mut rand::rng()).repair_address;
        self.network.send(&msg, to).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {}
}
