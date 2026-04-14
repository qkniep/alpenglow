// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Execution engine interface and placeholder implementation.
//!
//! The central trait is [`ExecutionEngine`], which supports five operations:
//! - [`begin_block`]: called when the first slice of a block arrives.
//! - [`execute_transactions`]: called once per decoded slice (streaming).
//! - [`end_block`]: called when the full block is reconstructed; checks the
//!   proposer's state hash against the locally computed one.
//! - [`compute_state_hash`]: called by the proposer to obtain the state hash
//!   for embedding in the last slice.
//! - [`finalize`]: called when a block is finalized.
//!
//! Blocks are identified during execution by [`InProgressBlock`], which
//! distinguishes between blocks arriving via dissemination (hash unknown until
//! fully reconstructed, keyed by [`Slot`] only) and blocks arriving via repair
//! (hash known upfront, keyed by full [`BlockId`]). At most one dissemination-
//! path block is in-progress per slot at any time, so the slot alone is an
//! unambiguous key for that case.
//!
//! [`begin_block`]: ExecutionEngine::begin_block
//! [`execute_transactions`]: ExecutionEngine::execute_transactions
//! [`end_block`]: ExecutionEngine::end_block
//! [`compute_state_hash`]: ExecutionEngine::compute_state_hash
//! [`finalize`]: ExecutionEngine::finalize

use std::collections::BTreeMap;

use log::{debug, info};
use tokio::sync::oneshot;

use crate::crypto::Hash;
use crate::types::Slot;
use crate::{BlockId, Transaction};

/// Identifies a block that is currently being executed.
///
/// During dissemination, the block hash is unknown until the block is fully
/// reconstructed. The slot alone identifies it since at most one such block
/// is in-progress per slot on this path. For blocks received via repair, the
/// hash is known upfront, so the full [`BlockId`] is available from the start.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum InProgressBlock {
    /// Block received via dissemination (or being produced); hash not yet known.
    Pending(Slot),
    /// Block received via repair; hash known upfront.
    Known(BlockId),
}

/// Whether the execution engine considers a block valid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionOutcome {
    /// State hash matched the proposer's; block is valid.
    Valid,
    /// State hash did not match; block is invalid.
    Invalid,
}

/// Events sent from consensus to the execution engine.
///
/// Both the validator path (receiving via dissemination) and the proposer path
/// (this node is the leader) share the [`BeginBlock`] and [`Transactions`]
/// variants, using [`InProgressBlock`] as the identifier.
///
/// The paths diverge at the end of the block:
/// - Validators receive [`EndBlock`], which carries the proposer's expected
///   state hash for verification.
/// - The proposer sends [`ComputeStateHash`] to obtain the state hash for
///   embedding in the last slice.
///
/// [`BeginBlock`]: ExecutionEvent::BeginBlock
/// [`Transactions`]: ExecutionEvent::Transactions
/// [`EndBlock`]: ExecutionEvent::EndBlock
/// [`ComputeStateHash`]: ExecutionEvent::ComputeStateHash
pub enum ExecutionEvent {
    /// First slice of `id` decoded; `parent` is the block to execute on top of.
    BeginBlock {
        id: InProgressBlock,
        parent: Option<BlockId>,
    },
    /// A slice of `id` was decoded; apply these transactions.
    Transactions {
        id: InProgressBlock,
        transactions: Vec<Transaction>,
    },
    /// All slices of a block received and the block is fully reconstructed.
    ///
    /// `block_id` contains the block hash (Merkle root over slice Merkle roots),
    /// which is a consensus integrity check distinct from `expected_state_hash`.
    /// `expected_state_hash` is a SHA-256 commitment to the execution state
    /// after applying all transactions, embedded by the proposer in the last
    /// slice. The engine should verify its locally computed state hash matches
    /// `expected_state_hash` and return the outcome to the votor.
    EndBlock {
        block_id: BlockId,
        parent_id: BlockId,
        expected_state_hash: Hash,
    },
    /// The proposer requests the current state hash for `slot`.
    ///
    /// The hash is returned via the oneshot `reply` channel and will be
    /// embedded in the last slice before shredding.
    ComputeStateHash {
        slot: Slot,
        reply: oneshot::Sender<Hash>,
    },
    /// `block_id` is finalized; commit state and prune non-ancestor heads.
    Finalized(BlockId),
}

/// Interface for an execution engine.
pub trait ExecutionEngine {
    /// Called when the first slice of `id` arrives, establishing `parent`.
    fn begin_block(&mut self, id: InProgressBlock, parent: Option<BlockId>);

    /// Streams transactions from a decoded slice of `id`.
    ///
    /// [`begin_block`] must have been called for `id` first.
    ///
    /// [`begin_block`]: Self::begin_block
    fn execute_transactions(&mut self, id: InProgressBlock, transactions: Vec<Transaction>);

    /// Called when the full block at `block_id` is reconstructed.
    ///
    /// The engine should compare its computed state hash against
    /// `expected_state_hash` and return the outcome. For blocks that were
    /// [`Pending`] (dissemination path), the engine may now re-key its
    /// in-progress state from slot to the full [`BlockId`].
    ///
    /// [`Pending`]: InProgressBlock::Pending
    fn end_block(&mut self, block_id: BlockId, expected_state_hash: &Hash) -> ExecutionOutcome;

    /// Called by the proposer to retrieve the state hash for `slot`.
    ///
    /// The returned hash is embedded in the last slice before shredding.
    fn compute_state_hash(&mut self, slot: Slot) -> Hash;

    /// Called when `block_id` is finalized.
    ///
    /// The engine may commit the state for `block_id` and prune any heads
    /// that are not ancestors of `block_id`.
    fn finalize(&mut self, block_id: BlockId);
}

/// Placeholder execution engine that counts and logs transactions.
///
/// Does not perform any actual state transitions or state hash verification.
/// [`end_block`] always reports [`ExecutionOutcome::Valid`].
///
/// [`end_block`]: ExecutionEngine::end_block
pub struct DummyExecution {
    /// Running transaction count per in-flight block.
    tx_counts: BTreeMap<InProgressBlock, usize>,
}

impl DummyExecution {
    pub fn new() -> Self {
        Self {
            tx_counts: BTreeMap::new(),
        }
    }
}

impl Default for DummyExecution {
    fn default() -> Self {
        Self::new()
    }
}

impl ExecutionEngine for DummyExecution {
    fn begin_block(&mut self, id: InProgressBlock, parent: Option<BlockId>) {
        debug!("begin block {id:?} on parent {parent:?}");
        self.tx_counts.insert(id, 0);
    }

    fn execute_transactions(&mut self, id: InProgressBlock, transactions: Vec<Transaction>) {
        debug!(
            "execute {} transactions for block {id:?}",
            transactions.len()
        );
        *self.tx_counts.entry(id).or_default() += transactions.len();
    }

    fn end_block(&mut self, block_id: BlockId, _expected_state_hash: &Hash) -> ExecutionOutcome {
        // Re-key from Pending(slot) to Known(block_id), carrying over the count.
        let slot = block_id.0;
        let count = self
            .tx_counts
            .remove(&InProgressBlock::Pending(slot))
            .or_else(|| {
                self.tx_counts
                    .remove(&InProgressBlock::Known(block_id.clone()))
            })
            .unwrap_or(0);
        debug!("end block {block_id:?} ({count} transactions); skipping state hash check");
        ExecutionOutcome::Valid
    }

    fn compute_state_hash(&mut self, slot: Slot) -> Hash {
        debug!("compute state hash for slot {slot} (dummy: returning zero hash)");
        crate::crypto::hash::hash(&[])
    }

    fn finalize(&mut self, block_id: BlockId) {
        let slot = block_id.0;
        let count = self
            .tx_counts
            .remove(&InProgressBlock::Pending(slot))
            .or_else(|| {
                self.tx_counts
                    .remove(&InProgressBlock::Known(block_id.clone()))
            })
            .unwrap_or(0);
        // Prune any in-flight states at or before the finalized slot.
        self.tx_counts.retain(|id, _| match id {
            InProgressBlock::Pending(s) => *s > slot,
            InProgressBlock::Known((s, _)) => *s > slot,
        });
        info!("finalized block {block_id:?} ({count} transactions)");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;

    fn block_id(slot: u64) -> BlockId {
        (Slot::new(slot), GENESIS_BLOCK_HASH.clone())
    }

    #[test]
    fn dummy_counts_transactions_across_slices() {
        let mut engine = DummyExecution::new();
        let id = InProgressBlock::Pending(Slot::new(1));

        engine.begin_block(id.clone(), None);
        engine.execute_transactions(id.clone(), vec![Transaction(vec![1, 2, 3])]);
        engine.execute_transactions(id.clone(), vec![Transaction(vec![4]), Transaction(vec![5])]);

        assert_eq!(engine.tx_counts[&id], 3);
    }

    #[test]
    fn end_block_rekeys_pending_to_known() {
        let mut engine = DummyExecution::new();
        let slot = Slot::new(1);
        let id = InProgressBlock::Pending(slot);

        engine.begin_block(id.clone(), None);
        engine.execute_transactions(id.clone(), vec![Transaction(vec![0])]);

        let outcome = engine.end_block(block_id(1), &crate::crypto::hash::hash(&[]));
        assert_eq!(outcome, ExecutionOutcome::Valid);
        // Pending entry is gone after end_block.
        assert!(!engine.tx_counts.contains_key(&id));
    }

    #[test]
    fn finalize_prunes_older_blocks() {
        let mut engine = DummyExecution::new();

        for s in 1u64..=3 {
            let id = InProgressBlock::Pending(Slot::new(s));
            engine.begin_block(id, Some(block_id(s - 1)));
        }

        engine.finalize(block_id(2));

        assert!(
            !engine
                .tx_counts
                .contains_key(&InProgressBlock::Pending(Slot::new(1)))
        );
        assert!(
            !engine
                .tx_counts
                .contains_key(&InProgressBlock::Pending(Slot::new(2)))
        );
        assert!(
            engine
                .tx_counts
                .contains_key(&InProgressBlock::Pending(Slot::new(3)))
        );
    }
}
