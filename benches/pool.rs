// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Micro-benchmark for the per-slot vote-counting hot path.
//!
//! This drives [`alpenglow::consensus::bench_replay_votes`],
//! which replays a batch of pre-signed votes into a fresh `SlotState`.
//! It deliberately bypasses the consensus loop and signature verification
//! (which would otherwise dominate)
//! so that changes to the per-slot data structures
//! — the `BlockHash`-keyed maps/sets that track notar/notar-fallback stake,
//! parents, and the safe-to-notar bookkeeping —
//! show up in the measurement.
//!
//! Requires the `test-utils` feature:
//! `cargo bench --features test-utils --bench pool`.

use std::sync::Arc;

use alpenglow::consensus::{ValidatorEpochInfo, Vote, bench_replay_votes};
use alpenglow::crypto::Hash;
use alpenglow::crypto::merkle::BlockHash;
use alpenglow::test_utils::generate_validators;
use alpenglow::types::Slot;
use alpenglow::{Stake, ValidatorIndex};
use divan::counter::ItemsCount;

fn main() {
    divan::main();
}

/// One slot's worth of pre-signed votes plus the parents to mark certified.
struct Workload {
    slot: Slot,
    epoch_info: Arc<ValidatorEpochInfo>,
    parents: Vec<BlockHash>,
    votes: Vec<(Vote, Stake)>,
}

/// Builds a realistic single-slot vote mix for `num_validators` validators.
///
/// Roughly half notarize one block, a quarter skip,
/// and a quarter cast notar-fallback votes for a competing block
/// — enough to exercise all of the converted per-slot structures
/// (notar / notar-fallback stake maps, the parents map,
/// and the pending/sent safe-to-notar sets).
fn build_workload(num_validators: u64) -> Workload {
    let (sks, epoch_info) = generate_validators(num_validators);
    let epoch_info = Arc::new(ValidatorEpochInfo::new(ValidatorIndex::new(0), epoch_info));
    let slot = Slot::new(1);
    let hash_a: BlockHash = Hash::random_for_test().into();
    let hash_b: BlockHash = Hash::random_for_test().into();

    let mut votes = Vec::with_capacity(num_validators as usize);
    for (i, sk) in sks.iter().enumerate() {
        let v = ValidatorIndex::new(i as u64);
        let vote = match i % 4 {
            0 | 1 => Vote::new_notar(slot, hash_a.clone(), sk, v),
            2 => Vote::new_skip(slot, sk, v),
            _ => Vote::new_notar_fallback(slot, hash_b.clone(), sk, v),
        };
        votes.push((vote, Stake::new(1)));
    }

    Workload {
        slot,
        epoch_info,
        parents: vec![hash_a, hash_b],
        votes,
    }
}

#[divan::bench(args = [10, 100, 1000])]
fn add_vote_replay(bencher: divan::Bencher, num_validators: u64) {
    let workload = build_workload(num_validators);
    bencher
        .counter(ItemsCount::new(workload.votes.len()))
        .bench(|| {
            divan::black_box(bench_replay_votes(
                workload.slot,
                workload.epoch_info.clone(),
                &workload.parents,
                &workload.votes,
            ))
        });
}
