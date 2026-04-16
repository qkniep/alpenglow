// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Execution engine interface and placeholder implementation.
//!
//! The execution engine sits alongside consensus and processes transactions
//! as they arrive from block dissemination.
//!
//! The central trait is [`ExecutionEngine`], which supports four operations:
//! - [`begin_block`]: Called when the first slice of a new block arrives.
//!   Establishes which parent state to execute on top of.
//! - [`execute_transactions`]: Called once per reconstructed slice.
//!   Allows pipelined execution of transactions as they arrive from dissemination.
//! - [`end_block`]: Called when last slice of a block has been received.
//!   Provides the block hash and allows the engine to emit a [`ExecutionEvent`].
//! - [`finalize`]: Called when a block is finalized by consensus.
//!   Allows the engine to commit the state changes and prune unreachable forks.
//!
//! The engine communicates results asynchronously through an [`ExecutionEvent`] channel.
//!
//! [`begin_block`]: ExecutionEngine::begin_block
//! [`execute_transactions`]: ExecutionEngine::execute_transactions
//! [`end_block`]: ExecutionEngine::end_block
//! [`finalize`]: ExecutionEngine::finalize

use std::collections::BTreeMap;

use log::{debug, info};
use tokio::sync::mpsc;

use crate::{BlockId, Slot, Transaction};

/// Events emitted by the execution engine.
///
/// Each variant carries the [`BlockId`] of the block it refers to.
/// Events are sent through the channel provided at construction time;
/// callers consume them via the matching [`mpsc::Receiver`].
#[derive(Clone, Debug)]
pub enum ExecutionEvent {
    /// Execution of a block has completed successfully.
    BlockExecuted {
        block_id: BlockId,
        result: ExecutionResult,
    },
    /// Execution of a block has failed.
    BlockFailed {
        block_id: BlockId,
        error: ExecutionError,
    },
}

/// Result of a successful block execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecutionResult {
    /// Number of transactions executed in this block.
    pub tx_count: usize,
}

/// Error that can occur during block execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecutionError {
    /// A transaction at the given index was invalid.
    InvalidTransaction { index: usize },
    /// Conflicting state accesses prevented parallel execution.
    StateConflict,
}

/// Event emitted by the blockstore when a slice is reconstructed.
///
/// Carries the decoded transactions for one slice, along with enough metadata
/// for the execution engine to track block state. The first slice of a block
/// includes the parent block identifier.
///
/// This type is deliberately kept separate from [`crate::consensus::votor::VotorEvent`]
/// so that the blockstore can feed execution independently of the voting logic.
/// The blockstore will hold a [`mpsc::Sender<SliceEvent>`] alongside the existing
/// Votor channel; the corresponding receiver is consumed by whichever task
/// drives the [`ExecutionEngine`].
#[derive(Clone, Debug)]
pub struct SliceEvent {
    /// Slot this slice belongs to.
    pub slot: Slot,
    /// Whether this is the last slice of the block.
    pub is_last: bool,
    /// Parent block, if this is the first slice.
    pub parent: Option<BlockId>,
    /// Decoded transactions from the slice payload.
    pub transactions: Vec<Transaction>,
}

/// Interface for an execution engine.
///
/// Driven by the consensus layer and blockstore through four operations:
///
/// 1. **Fork awareness**: [`begin_block`] establishes the parent state to
///    execute on top of, allowing the engine to maintain multiple live heads
///    when the block tree branches.
/// 2. **Streaming**: [`execute_transactions`] is called once per decoded slice
///    as data arrives from dissemination, without waiting for the full block.
/// 3. **Completion**: [`end_block`] signals that all slices for a block have
///    been received, providing the block hash. The engine should emit a
///    [`ExecutionEvent::BlockExecuted`] or [`ExecutionEvent::BlockFailed`]
///    event through its channel.
/// 4. **Finality**: [`finalize`] signals that a block's state is canonical and
///    durable, so the engine can commit it and prune all non-ancestor heads.
///
/// [`begin_block`]: ExecutionEngine::begin_block
/// [`execute_transactions`]: ExecutionEngine::execute_transactions
/// [`end_block`]: ExecutionEngine::end_block
/// [`finalize`]: ExecutionEngine::finalize
pub trait ExecutionEngine {
    /// Prepares to execute a new block on top of `parent`'s state.
    ///
    /// Called when the first slice of `slot` is received from dissemination.
    /// The engine should fork its execution state from `parent` (or from the
    /// genesis state if `parent` is `None`). Subsequent calls to
    /// [`execute_transactions`] for this `slot` apply against that forked state.
    ///
    /// [`execute_transactions`]: Self::execute_transactions
    fn begin_block(&mut self, slot: Slot, parent: Option<BlockId>);

    /// Streams transactions from a single decoded slice of `slot`.
    ///
    /// Called once per slice as data arrives from dissemination.
    /// [`begin_block`] must have been called for `slot` beforehand.
    ///
    /// [`begin_block`]: Self::begin_block
    fn execute_transactions(&mut self, slot: Slot, transactions: Vec<Transaction>);

    /// Notifies the engine that all slices for `slot` have been received.
    ///
    /// Provides the full [`BlockId`] (including the block hash), which is only
    /// known after the double-Merkle tree has been computed over all slices.
    /// The engine should emit a [`ExecutionEvent`] through its channel to
    /// signal the outcome of execution for this block.
    fn end_block(&mut self, slot: Slot, block_id: BlockId);

    /// Notifies the engine that `block_id` has been finalized by consensus.
    ///
    /// The engine may durably commit the execution state for `block_id` and
    /// prune any execution heads that are not ancestors of `block_id`.
    fn finalize(&mut self, block_id: BlockId);
}

/// Placeholder execution engine that counts and logs transactions.
///
/// Tracks the running transaction count per in-flight block and emits
/// [`ExecutionEvent`] summaries when each block is completed via
/// [`end_block`](ExecutionEngine::end_block). Does not perform any actual
/// state transitions.
pub struct DummyExecution {
    /// Running transaction count for each in-flight block, keyed by slot.
    tx_counts: BTreeMap<Slot, usize>,
    /// Channel for emitting execution events.
    event_sender: mpsc::Sender<ExecutionEvent>,
}

impl DummyExecution {
    /// Creates a new `DummyExecution` that emits events on the given channel.
    ///
    /// The matching [`mpsc::Receiver`] should be consumed by whichever task
    /// handles execution events (e.g. the main validator loop).
    pub fn new(event_sender: mpsc::Sender<ExecutionEvent>) -> Self {
        Self {
            tx_counts: BTreeMap::new(),
            event_sender,
        }
    }
}

impl ExecutionEngine for DummyExecution {
    fn begin_block(&mut self, slot: Slot, parent: Option<BlockId>) {
        debug!("begin block in slot {slot} on parent {parent:?}");
        self.tx_counts.insert(slot, 0);
    }

    fn execute_transactions(&mut self, slot: Slot, transactions: Vec<Transaction>) {
        debug!(
            "execute {} transactions for slot {slot}",
            transactions.len()
        );
        *self.tx_counts.entry(slot).or_default() += transactions.len();
    }

    fn end_block(&mut self, slot: Slot, block_id: BlockId) {
        let total = self.tx_counts.remove(&slot).unwrap_or(0);
        let _ = self.event_sender.try_send(ExecutionEvent::BlockExecuted {
            block_id,
            result: ExecutionResult { tx_count: total },
        });
    }

    fn finalize(&mut self, block_id: BlockId) {
        self.tx_counts.remove(&block_id.0);
        self.tx_counts.retain(|slot, _| *slot > block_id.0);
        info!("finalized block {block_id:?}");
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
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);
        let slot = Slot::new(1);

        engine.begin_block(slot, None);
        engine.execute_transactions(slot, vec![Transaction(vec![1, 2, 3])]);
        engine.execute_transactions(slot, vec![Transaction(vec![4]), Transaction(vec![5])]);
        assert_eq!(engine.tx_counts[&slot], 3);

        let id = block_id(1);
        engine.end_block(slot, id);

        let event = rx.try_recv().unwrap();
        match event {
            ExecutionEvent::BlockExecuted { block_id, result } => {
                assert_eq!(block_id, (Slot::new(1), GENESIS_BLOCK_HASH.clone()));
                assert_eq!(result.tx_count, 3);
            }
            ExecutionEvent::BlockFailed { .. } => panic!("expected BlockExecuted"),
        }
    }

    #[test]
    fn finalize_prunes_older_blocks() {
        let (tx, _rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let id1 = block_id(1);
        let id2 = block_id(2);

        engine.begin_block(Slot::new(1), None);
        engine.begin_block(Slot::new(2), Some(id1));
        engine.begin_block(Slot::new(3), Some(id2.clone()));

        // Finalizing slot 2 should prune slot 1 and slot 2, but keep slot 3.
        engine.finalize(id2);

        assert!(!engine.tx_counts.contains_key(&Slot::new(1)));
        assert!(!engine.tx_counts.contains_key(&Slot::new(2)));
        assert!(engine.tx_counts.contains_key(&Slot::new(3)));
    }

    #[test]
    fn end_block_emits_event() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let slot = Slot::new(5);
        engine.begin_block(slot, Some(block_id(4)));
        engine.execute_transactions(slot, vec![Transaction(vec![0]); 7]);

        let bid = block_id(5);
        engine.end_block(slot, bid.clone());

        let event = rx.try_recv().unwrap();
        match event {
            ExecutionEvent::BlockExecuted { block_id, result } => {
                assert_eq!(block_id, bid);
                assert_eq!(result.tx_count, 7);
            }
            ExecutionEvent::BlockFailed { .. } => panic!("expected BlockExecuted"),
        }
    }
}
