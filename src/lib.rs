// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Alpenglow: Global High-Performance Proof-of-Stake Blockchain with Erasure Coding
//!
//! Research reference implementation of the Alpenglow consensus protocol.

#![deny(rustdoc::broken_intra_doc_links)]

pub mod all2all;
pub mod consensus;
pub mod crypto;
pub mod disseminator;
pub mod execution;
pub mod logging;
pub mod network;
pub mod repair;
pub mod shredder;
#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;
pub mod types;
pub mod validator;

use std::net::SocketAddr;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use wincode::config::DefaultConfig;
use wincode::{SchemaRead, SchemaWrite};

pub use self::all2all::All2All;
pub use self::consensus::Alpenglow;
use self::crypto::{aggsig, signature};
pub use self::disseminator::Disseminator;
use self::types::Slot;
pub use self::types::{Stake, ValidatorIndex};
pub use self::validator::Validator;
use crate::all2all::TrivialAll2All;
use crate::consensus::{ConsensusMessage, EpochInfo, ValidatorEpochInfo};
use crate::crypto::merkle::BlockHash;
use crate::crypto::signature::SecretKey;
use crate::disseminator::Rotor;
use crate::disseminator::rotor::{IidQuorumSampler, StakeWeightedSampler};
use crate::network::{UdpNetwork, localhost_ip_sockaddr};
use crate::repair::{RepairRequest, RepairResponse};
use crate::shredder::Shred;

// NOTE: In many places we assume that `usize` is 64 bits wide.
// So, for now, we only support 64-bit architectures.
const _: () = assert!(std::mem::size_of::<usize>() == 8);

/// Serializes an in-memory value with [`wincode`].
///
/// Panics on encoder failure,
/// which can't happen with a `Vec` writer:
/// wincode only fails on writer I/O errors, and a `Vec` never errors.
pub(crate) fn serialize<T>(value: &T) -> Vec<u8>
where
    T: SchemaWrite<DefaultConfig, Src = T> + ?Sized,
{
    wincode::serialize(value).expect("serializing an in-memory value should not fail")
}

/// Block identifier type.
pub type BlockId = (Slot, BlockHash);

/// Maximum number of bytes a transaction payload can contain.
pub const MAX_TRANSACTION_SIZE: usize = 512;

/// Parsed block with information about parent and transactions as payload.
#[derive(Clone, Debug)]
pub struct Block {
    // TODO: unused
    _slot: Slot,
    hash: BlockHash,
    parent: Slot,
    parent_hash: BlockHash,
    // TODO: unused
    _transactions: Vec<Transaction>,
}

/// Dummy transaction containing payload bytes.
///
/// A transaction cannot hold more than [`MAX_TRANSACTION_SIZE`] payload bytes.
#[derive(Clone, Debug, SchemaRead, SchemaWrite)]
pub struct Transaction(pub Vec<u8>);

/// Validator information as known about other validators.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ValidatorInfo {
    pub id: ValidatorIndex,
    pub stake: Stake,
    pub pubkey: signature::PublicKey,
    #[serde(deserialize_with = "aggsig::PublicKey::from_array_of_bytes")]
    pub voting_pubkey: aggsig::PublicKey,
    pub all2all_address: SocketAddr,
    pub disseminator_address: SocketAddr,
    /// Address of the node's repair requester; send [`RepairResponse`] messages here when replying to its [`RepairRequest`].
    pub repair_requester_address: SocketAddr,
    /// Address of the node's repair responder; send [`RepairRequest`] messages here to ask it to repair a block.
    pub repair_responder_address: SocketAddr,
}

type TestNode = Alpenglow<
    TrivialAll2All<UdpNetwork<ConsensusMessage, ConsensusMessage>>,
    Rotor<UdpNetwork<Shred, Shred>, IidQuorumSampler<StakeWeightedSampler>>,
    UdpNetwork<Transaction, Transaction>,
>;

struct Networks {
    all2all: UdpNetwork<ConsensusMessage, ConsensusMessage>,
    disseminator: UdpNetwork<Shred, Shred>,
    repair_requester: UdpNetwork<RepairRequest, RepairResponse>,
    repair_responder: UdpNetwork<RepairResponse, RepairRequest>,
    txs: UdpNetwork<Transaction, Transaction>,
}

impl Networks {
    fn new() -> Self {
        Self {
            all2all: UdpNetwork::new_with_any_port(),
            disseminator: UdpNetwork::new_with_any_port(),
            repair_requester: UdpNetwork::new_with_any_port(),
            repair_responder: UdpNetwork::new_with_any_port(),
            txs: UdpNetwork::new_with_any_port(),
        }
    }
}

/// Creates [`Alpenglow`] instances for testing and benchmarking purposes.
///
/// This code lives here to enable sharing between different testing and benchmarking.
/// It should not be used in production code.
#[must_use]
pub fn create_test_nodes(count: u64) -> Vec<TestNode> {
    // open sockets with arbitrary ports
    let networks = (0..count).map(|_| Networks::new()).collect::<Vec<_>>();

    // prepare validator info for all nodes
    let mut rng = rand::rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut validators = Vec::new();
    for (id, network) in networks.iter().enumerate() {
        sks.push(SecretKey::new(&mut rng));
        voting_sks.push(aggsig::SecretKey::new(&mut rng));
        let all2all_address = localhost_ip_sockaddr(network.all2all.port());
        let disseminator_address = localhost_ip_sockaddr(network.disseminator.port());
        let repair_requester_address = localhost_ip_sockaddr(network.repair_requester.port());
        let repair_responder_address = localhost_ip_sockaddr(network.repair_responder.port());
        validators.push(ValidatorInfo {
            id: ValidatorIndex::new(id as u64),
            stake: Stake::new(1),
            pubkey: sks[id].to_pk(),
            voting_pubkey: voting_sks[id].to_pk(),
            all2all_address,
            disseminator_address,
            repair_requester_address,
            repair_responder_address,
        });
    }

    // turn validator info into actual nodes
    let shared_epoch = EpochInfo::new(validators.clone());
    networks
        .into_iter()
        .enumerate()
        .map(|(id, network)| {
            let v = ValidatorIndex::new(id as u64);
            let epoch_info = Arc::new(ValidatorEpochInfo::new(v, shared_epoch.clone()));
            let all2all = TrivialAll2All::new(validators.clone(), network.all2all);
            let disseminator = Rotor::new(network.disseminator, epoch_info.clone());
            let repair_requester_network = network.repair_requester;
            let repair_responder_network = network.repair_responder;
            let txs_receiver = network.txs;
            Alpenglow::new(
                sks[id].clone(),
                voting_sks[id].clone(),
                all2all,
                disseminator,
                repair_requester_network,
                repair_responder_network,
                epoch_info,
                txs_receiver,
            )
        })
        .collect()
}
