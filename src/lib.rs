// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Alpenglow: Global High-Performance Proof-of-Stake Blockchain with Erasure Coding
//!
//! Research reference implementation of the Alpenglow consensus protocol.

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

use serde::{Deserialize, Serialize};

pub use self::all2all::All2All;
pub use self::consensus::Alpenglow;
pub use self::consensus::votor::VotorEvent;
use self::crypto::{aggsig, signature};
pub use self::disseminator::Disseminator;
use self::types::Slot;
use self::types::block_hash::BlockHash;
pub use self::validator::Validator;

/// Validator ID number type.
pub type ValidatorId = u64;
/// Validator stake type.
pub type Stake = u64;
/// Block identifier type.
pub type BlockId = (Slot, BlockHash);

const MAX_TRANSACTION_SIZE: usize = 512;

const MAX_TRANSACTIONS_PER_SLICE: usize = 255;

/// Parsed block with information about parent and transactions as payload.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Block {
    slot: Slot,
    block_hash: BlockHash,
    parent: Slot,
    parent_hash: BlockHash,
    transactions: Vec<Transaction>,
}

/// Dummy transaction containing payload bytes.
///
/// A transaction cannot be bigger than [`MAX_TRANSACTION_SIZE`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Transaction(pub Vec<u8>);

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

/// Returns the highest non-zero byte in `val`.
pub(crate) fn highest_non_zero_byte(mut val: usize) -> usize {
    let mut cnt = 0;
    while val != 0 {
        val /= 256;
        cnt += 1;
    }
    cnt
}
