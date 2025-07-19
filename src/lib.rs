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
pub mod validator;

use network::{MTU_BYTES, NetworkError, SerializableMessage};
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

impl SerializableMessage for Transaction {
    /// Tries to deserialize a `NetworkMessage` from bytes using [`bincode`].
    ///
    /// # Errors
    ///
    /// Returns [`NetworkError::Deserialization`] if bincode decoding fails.
    /// This includes the case where `bytes` exceed the limit of [`MTU_BYTES`].
    fn from_bytes(bytes: &[u8]) -> Result<Self, NetworkError> {
        if bytes.len() > MTU_BYTES {
            return Err(NetworkError::Deserialization(
                bincode::error::DecodeError::LimitExceeded,
            ));
        }
        // FIXME add limits similar to https://github.com/anza-xyz/agave/blob/8a77fc39fda83fc528bf032c7cbff6063aafb5c5/core/src/banking_stage/latest_validator_vote_packet.rs#L54
        let (msg, _) = bincode::serde::decode_from_slice(bytes, bincode::config::standard())?;
        Ok(msg)
    }

    fn to_bytes(&self) -> Vec<u8> {
        let bytes = bincode::serde::encode_to_vec(self, bincode::config::standard())
            .expect("serialization should not panic");
        assert!(bytes.len() <= MTU_BYTES, "each message should fit in MTU");
        bytes
    }
}

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
