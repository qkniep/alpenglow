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
pub mod logging;
pub mod network;
pub mod repair;
pub mod shredder;
#[cfg(test)]
pub mod test_utils;
pub mod types;
pub mod validator;

use std::net::SocketAddr;
use std::sync::Arc;

use derive_more::{Add, From, Into, Sum};
use serde::{Deserialize, Serialize};
use static_assertions::const_assert_eq;
use wincode::{SchemaRead, SchemaWrite};

pub use self::all2all::All2All;
pub use self::consensus::Alpenglow;
pub use self::consensus::votor::VotorEvent;
use self::crypto::{aggsig, signature};
pub use self::disseminator::Disseminator;
use self::types::Slot;
pub use self::validator::Validator;
use crate::all2all::TrivialAll2All;
use crate::consensus::{ConsensusMessage, EpochInfo};
use crate::crypto::merkle::BlockHash;
use crate::crypto::signature::SecretKey;
use crate::disseminator::Rotor;
use crate::disseminator::rotor::StakeWeightedSampler;
use crate::network::{UdpNetwork, localhost_ip_sockaddr};
use crate::repair::{RepairRequest, RepairResponse};
use crate::shredder::Shred;

// NOTE: In many places we assume that `usize` is 64 bits wide.
// So, for now, we only support 64-bit architectures.
const_assert_eq!(std::mem::size_of::<usize>(), 8);

/// Validator ID number type.
pub type ValidatorId = u64;
/// Validator stake type.
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Add,
    Sum,
    From,
    Into,
    SchemaRead,
    SchemaWrite,
    Serialize,
    Deserialize,
)]
#[repr(transparent)]
pub struct Stake(u64);
/// Block identifier type.
pub type BlockId = (Slot, BlockHash);

/// Maximum number of bytes a transaction payload can contain.
const MAX_TRANSACTION_SIZE: usize = 512;

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
    pub id: ValidatorId,
    pub stake: Stake,
    pub pubkey: signature::PublicKey,
    #[serde(deserialize_with = "aggsig::PublicKey::from_array_of_bytes")]
    pub voting_pubkey: aggsig::PublicKey,
    pub all2all_address: SocketAddr,
    pub disseminator_address: SocketAddr,
    /// Send [`RepairRequest`] messages to this address to ask the node to repair a block.
    pub repair_request_address: SocketAddr,
    /// Send [`RepairResponse`] messages to this address when replying to a node's [`RepairRequest`] message.
    pub repair_response_address: SocketAddr,
}

type TestNode = Alpenglow<
    TrivialAll2All<UdpNetwork<ConsensusMessage, ConsensusMessage>>,
    Rotor<UdpNetwork<Shred, Shred>, StakeWeightedSampler>,
    UdpNetwork<Transaction, Transaction>,
>;

struct Networks {
    all2all: UdpNetwork<ConsensusMessage, ConsensusMessage>,
    disseminator: UdpNetwork<Shred, Shred>,
    repair: UdpNetwork<RepairRequest, RepairResponse>,
    repair_request: UdpNetwork<RepairResponse, RepairRequest>,
    txs: UdpNetwork<Transaction, Transaction>,
}

impl Networks {
    fn new() -> Self {
        Self {
            all2all: UdpNetwork::new_with_any_port(),
            disseminator: UdpNetwork::new_with_any_port(),
            repair: UdpNetwork::new_with_any_port(),
            repair_request: UdpNetwork::new_with_any_port(),
            txs: UdpNetwork::new_with_any_port(),
        }
    }
}

/// Creates [`TestNode`] for testing and benchmarking purposes.
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
        let repair_response_address = localhost_ip_sockaddr(network.repair.port());
        let repair_request_address = localhost_ip_sockaddr(network.repair_request.port());
        validators.push(ValidatorInfo {
            id: id as u64,
            stake: 1.into(),
            pubkey: sks[id].to_pk(),
            voting_pubkey: voting_sks[id].to_pk(),
            all2all_address,
            disseminator_address,
            repair_request_address,
            repair_response_address,
        });
    }

    // turn validator info into actual nodes
    networks
        .into_iter()
        .enumerate()
        .map(|(id, network)| {
            let epoch_info = Arc::new(EpochInfo::new(id as u64, validators.clone()));
            let all2all = TrivialAll2All::new(validators.clone(), network.all2all);
            let disseminator = Rotor::new(network.disseminator, epoch_info.clone());
            let repair_network = network.repair;
            let repair_request_network = network.repair_request;
            let txs_receiver = network.txs;
            Alpenglow::new(
                sks[id].clone(),
                voting_sks[id].clone(),
                all2all,
                disseminator,
                repair_network,
                repair_request_network,
                epoch_info,
                txs_receiver,
            )
        })
        .collect()
}
