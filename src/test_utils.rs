// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Utility types and functions for tests and benchmarks.

use std::sync::Arc;

use rand::RngCore;
use wincode::{SchemaRead, SchemaWrite};

use crate::all2all::TrivialAll2All;
use crate::consensus::{ConsensusMessage, EpochInfo};
use crate::crypto::aggsig::SecretKey;
use crate::crypto::merkle::{BlockHash, DoubleMerkleTree};
use crate::crypto::{Hash, signature};
use crate::network::simulated::SimulatedNetworkCore;
use crate::network::{SimulatedNetwork, localhost_ip_sockaddr};
use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, ValidatedShred};
use crate::types::{Slice, SliceHeader, SliceIndex, SlicePayload};
use crate::{
    BlockId, MAX_TRANSACTION_SIZE, Slot, Transaction, ValidatorId, ValidatorInfo, VotorEvent,
};

/// A simple ping network message.
#[derive(Clone, Debug, Default, SchemaRead, SchemaWrite)]
pub struct Ping(pub [u8; 32]);

/// A simple pong network message.
#[derive(Clone, Debug, Default, SchemaRead, SchemaWrite)]
pub struct Pong(pub [u8; 32]);

/// A simple network message that can be either a ping or a pong.
#[derive(Clone, Debug, PartialEq, Eq, SchemaRead, SchemaWrite)]
pub enum PingOrPong {
    Ping([u8; 32]),
    Pong([u8; 32]),
}

/// Generates [`ValidatorInfo`] for the given number of validators.
///
/// Returns the voting secret keys of all validators and the [`EpochInfo`] of validator 0.
pub fn generate_validators(num_validators: u64) -> (Vec<SecretKey>, Arc<EpochInfo>) {
    let mut rng = rand::rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut validators = Vec::new();
    for i in 0..num_validators {
        sks.push(signature::SecretKey::new(&mut rng));
        voting_sks.push(SecretKey::new(&mut rng));
        validators.push(ValidatorInfo {
            id: i,
            stake: 1,
            pubkey: sks[i as usize].to_pk(),
            voting_pubkey: voting_sks[i as usize].to_pk(),
            all2all_address: localhost_ip_sockaddr(0),
            disseminator_address: localhost_ip_sockaddr(0),
            repair_request_address: localhost_ip_sockaddr(0),
            repair_response_address: localhost_ip_sockaddr(0),
        });
    }
    let epoch_info = Arc::new(EpochInfo::new(0, validators));
    (voting_sks, epoch_info)
}

/// Creates [`TrivialAll2All`] instances for the given validators.
///
/// These are connected via a [`SimulatedNetworkCore`].
pub async fn generate_all2all_instances(
    mut validators: Vec<ValidatorInfo>,
) -> Vec<TrivialAll2All<SimulatedNetwork<ConsensusMessage, ConsensusMessage>>> {
    let core = Arc::new(
        SimulatedNetworkCore::default()
            .with_jitter(0.0)
            .with_packet_loss(0.0),
    );
    for (i, val) in validators.iter_mut().enumerate() {
        val.all2all_address = localhost_ip_sockaddr(i.try_into().unwrap());
    }
    let mut all2all = Vec::new();
    for i in 0..validators.len() {
        let network = core.join_unlimited(i as ValidatorId).await;
        all2all.push(TrivialAll2All::new(validators.clone(), network));
    }
    all2all
}

/// Creates a random block with the given number of slices and shreds it.
///
/// Returns the block hash, the double-Merkle tree, and all shreds by slice.
pub fn create_random_shredded_block(
    slot: Slot,
    num_slices: usize,
    sk: &signature::SecretKey,
) -> (BlockHash, DoubleMerkleTree, Vec<Vec<ValidatedShred>>) {
    let mut shredder = RegularShredder::default();
    let mut shreds = Vec::with_capacity(num_slices);
    for slice in create_random_block(slot, num_slices) {
        shreds.push(shredder.shred(slice.clone(), sk).unwrap().to_vec());
    }
    let merkle_roots = shreds
        .iter()
        .map(|slice_shreds| slice_shreds[0].merkle_root.clone())
        .collect::<Vec<_>>();
    let tree = DoubleMerkleTree::new(&merkle_roots);
    let block_hash = tree.get_root();
    (block_hash, tree, shreds)
}

/// Creates a random block with the given number of slices.
///
/// In most cases, you should use [`create_random_shredded_block`] instead.
///
/// Returns all slices, as [`Slice`].
pub fn create_random_block(slot: Slot, num_slices: usize) -> Vec<Slice> {
    let final_slice_index = SliceIndex::new_unchecked(num_slices - 1);
    let parent_slot = Slot::genesis();
    assert_ne!(slot, parent_slot);
    let mut slices = Vec::new();
    for slice_index in final_slice_index.until() {
        let parent = if slice_index.is_first() {
            Some((parent_slot, Hash::random_for_test().into()))
        } else {
            None
        };
        let payload = create_random_slice_payload_valid_txs(parent);
        let header = SliceHeader {
            slot,
            slice_index,
            is_last: slice_index == final_slice_index,
        };
        slices.push(Slice::from_parts(header, payload, None));
    }
    slices
}

/// Asserts that two [`VotorEvent`]s are equal.
///
/// Panics if they are not equal.
pub fn assert_votor_events_match(ev0: VotorEvent, ev1: VotorEvent) {
    match (ev0, ev1) {
        (
            VotorEvent::ParentReady {
                slot: s0,
                parent_slot: ps0,
                parent_hash: ph0,
            },
            VotorEvent::ParentReady {
                slot: s1,
                parent_slot: ps1,
                parent_hash: ph1,
            },
        ) => {
            assert_eq!(s0, s1);
            assert_eq!(ps0, ps1);
            assert_eq!(ph0, ph1);
        }
        (VotorEvent::CertCreated(c0), VotorEvent::CertCreated(c1)) => assert_eq!(c0, c1),
        (VotorEvent::Standstill(s0, c0, v0), VotorEvent::Standstill(s1, c1, v1)) => {
            assert_eq!(s0, s1);
            assert_eq!(c0, c1);
            assert_eq!(v0, v1);
        }
        (VotorEvent::SafeToNotar(s0, h0), VotorEvent::SafeToNotar(s1, h1)) => {
            assert_eq!(s0, s1);
            assert_eq!(h0, h1);
        }
        (
            VotorEvent::Block {
                slot: s0,
                block_info: b0,
            },
            VotorEvent::Block {
                slot: s1,
                block_info: b1,
            },
        ) => {
            assert_eq!(s0, s1);
            assert_eq!(b0, b1);
        }

        (VotorEvent::Timeout(s0), VotorEvent::Timeout(s1))
        | (VotorEvent::TimeoutCrashedLeader(s0), VotorEvent::TimeoutCrashedLeader(s1))
        | (VotorEvent::SafeToSkip(s0), VotorEvent::SafeToSkip(s1)) => assert_eq!(s0, s1),
        (VotorEvent::FirstShred(s0), VotorEvent::FirstShred(s1)) => assert_eq!(s0, s1),

        (ev0, ev1) => {
            panic!("{ev0:?} does not match {ev1:?}");
        }
    }
}

/// Creates a valid [`SlicePayload`] which contains valid transactions that can be decoded.
fn create_random_slice_payload_valid_txs(parent: Option<BlockId>) -> SlicePayload {
    // HACK: manually picked number of maximally sized transactions that fit in the slice
    // without going over the [`MAX_DATA_PER_SLICE`] limit.
    const NUM_TXS_PER_SLICE: usize = 61;

    let mut data = vec![0; MAX_TRANSACTION_SIZE];
    rand::rng().fill_bytes(&mut data);
    let tx = Transaction(data);
    let tx = wincode::serialize(&tx).expect("serialization should not panic");
    let txs = vec![tx; NUM_TXS_PER_SLICE];
    let txs = wincode::serialize(&txs).expect("serialization should not panic");
    let payload = SlicePayload::new(parent, txs);
    let payload: Vec<u8> = payload.into();
    assert!(payload.len() <= MAX_DATA_PER_SLICE);
    SlicePayload::from(payload.as_slice())
}
