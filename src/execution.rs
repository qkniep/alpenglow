// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Execution engine interface and placeholder implementation.
//!
//! The execution engine sits alongside consensus and processes transactions
//! as they arrive from block dissemination.
//!
//! The central trait is [`ExecutionEngine`], which supports three operations:
//! - [`begin_block`]: called when the first slice of a new block arrives,
//!   establishing which parent state to execute on top of.
//! - [`execute_transactions`]: called once per decoded slice to stream
//!   transactions as they arrive from dissemination.
//! - [`finalize`]: called when a block is finalized, allowing the engine to
//!   commit the corresponding state and prune unreachable execution heads.
//!
//! [`begin_block`]: ExecutionEngine::begin_block
//! [`execute_transactions`]: ExecutionEngine::execute_transactions
//! [`finalize`]: ExecutionEngine::finalize

use std::collections::BTreeMap;

use log::{debug, info};

use crate::{BlockId, Transaction};

/// Interface for an execution engine.
///
/// Driven by the consensus layer with three operations:
///
/// 1. **Streaming**: [`execute_transactions`] is called once per decoded slice
///    as data arrives from dissemination, without waiting for the full block.
/// 2. **Fork awareness**: [`begin_block`] establishes the parent state to
///    execute on top of, allowing the engine to maintain multiple live heads
///    when the block tree branches.
/// 3. **Finality**: [`finalize`] signals that a block's state is canonical and
///    durable, so the engine can commit it and prune all non-ancestor heads.
///
/// [`begin_block`]: ExecutionEngine::begin_block
/// [`execute_transactions`]: ExecutionEngine::execute_transactions
/// [`finalize`]: ExecutionEngine::finalize
pub trait ExecutionEngine {
    /// Prepares to execute a new block on top of `parent`'s state.
    ///
    /// Called when the first slice of `block_id` is received from dissemination.
    /// The engine should fork its execution state from `parent` (or from the
    /// genesis state if `parent` is `None`). Subsequent calls to
    /// [`execute_transactions`] for this `block_id` apply against that forked state.
    ///
    /// [`execute_transactions`]: Self::execute_transactions
    fn begin_block(&mut self, block_id: BlockId, parent: Option<BlockId>);

    /// Streams transactions from a single decoded slice of `block_id`.
    ///
    /// Called once per slice as data arrives from dissemination.
    /// [`begin_block`] must have been called for `block_id` beforehand.
    ///
    /// [`begin_block`]: Self::begin_block
    fn execute_transactions(&mut self, block_id: BlockId, transactions: Vec<Transaction>);

    /// Notifies the engine that `block_id` has been finalized.
    ///
    /// The engine may durably commit the execution state for `block_id` and
    /// prune any execution heads that are not ancestors of `block_id`.
    fn finalize(&mut self, block_id: BlockId);
}

/// Placeholder execution engine that counts and logs transactions.
///
/// Tracks the running transaction count per in-flight block and logs a summary
/// when each block is finalized. Does not perform any actual state transitions.
pub struct DummyExecution {
    /// Running transaction count for each in-flight block.
    tx_counts: BTreeMap<BlockId, usize>,
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
    fn begin_block(&mut self, block_id: BlockId, parent: Option<BlockId>) {
        debug!("begin block {block_id:?} on parent {parent:?}");
        self.tx_counts.insert(block_id, 0);
    }

    fn execute_transactions(&mut self, block_id: BlockId, transactions: Vec<Transaction>) {
        debug!(
            "execute {} transactions for block {block_id:?}",
            transactions.len()
        );
        *self.tx_counts.entry(block_id).or_default() += transactions.len();
    }

    fn finalize(&mut self, block_id: BlockId) {
        let total = self.tx_counts.remove(&block_id).unwrap_or(0);
        // Prune any in-flight states at or before the finalized slot; they are
        // either the finalized block itself (already removed) or forks that can
        // no longer become canonical.
        self.tx_counts.retain(|id, _| id.0 > block_id.0);
        info!("finalized block {block_id:?} ({total} transactions)");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::merkle::GENESIS_BLOCK_HASH;
    use crate::types::Slot;

    fn block_id(slot: u64) -> BlockId {
        (Slot::new(slot), GENESIS_BLOCK_HASH.clone())
    }

    #[test]
    fn dummy_counts_transactions_across_slices() {
        let mut engine = DummyExecution::new();
        let id = block_id(1);

        engine.begin_block(id.clone(), None);
        engine.execute_transactions(id.clone(), vec![Transaction(vec![1, 2, 3])]);
        engine.execute_transactions(id.clone(), vec![Transaction(vec![4]), Transaction(vec![5])]);

        assert_eq!(engine.tx_counts[&id], 3);
    }

    #[test]
    fn finalize_prunes_older_blocks() {
        let mut engine = DummyExecution::new();

        let id1 = block_id(1);
        let id2 = block_id(2);
        let id3 = block_id(3);

        engine.begin_block(id1.clone(), None);
        engine.begin_block(id2.clone(), Some(id1.clone()));
        engine.begin_block(id3.clone(), Some(id2.clone()));

        // Finalizing slot 2 should prune slot 1 and slot 2 itself, but keep slot 3.
        engine.finalize(id2.clone());

        assert!(!engine.tx_counts.contains_key(&id1));
        assert!(!engine.tx_counts.contains_key(&id2));
        assert!(engine.tx_counts.contains_key(&id3));
    }
}
