// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Alpenglow: Global High-Performance Proof-of-Stake Blockchain with Erasure Coding
//!
//! Research reference implementation of the Alpenglow consensus protocol.

pub mod all2all;
pub mod consensus;
pub mod crypto;
pub mod disseminator;
pub mod network;
pub mod repair;
pub mod shredder;
#[cfg(test)]
pub mod test_utils;
pub mod validator;

use serde::{Deserialize, Serialize};

pub use all2all::All2All;
pub use consensus::Alpenglow;
use crypto::{Hash, aggsig, signature};
pub use disseminator::Disseminator;
pub use validator::Validator;

/// Slot number type.
pub type Slot = u64;
/// Validator ID number type.
pub type ValidatorId = u64;
/// Validator stake type.
pub type Stake = u64;

const MAX_TRANSACTION_SIZE: usize = 512;

/// Parsed block with information about parent and transactions as payload.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Block {
    slot: Slot,
    block_hash: Hash,
    parent: Slot,
    parent_hash: Hash,
    transactions: Vec<Transaction>,
}

/// Dummy transaction containing payload bytes.
///
/// A transaction cannot be bigger than `MAX_TRANSACTION_SIZE`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Transaction(Vec<u8>);

/// Validator information as known about other validators.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ValidatorInfo {
    pub id: ValidatorId,
    pub stake: Stake,
    pub pubkey: signature::PublicKey,
    #[serde(deserialize_with = "aggsig::PublicKey::from_array_of_bytes")]
    pub voting_pubkey: aggsig::PublicKey,
    pub all2all_address: String,
    pub disseminator_address: String,
    pub repair_address: String,
}
