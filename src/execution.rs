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
//! Execution is intentionally *decoupled* from consensus: the engine reports the
//! state root it computed via [`ExecutionResult::state_hash`] but never gates
//! voting on it. Whether that root agrees with the block's claimed root (or with
//! a quorum of peers) is a consensus-layer decision left to whoever consumes the
//! [`ExecutionEvent`]s. This keeps consensus measurements clean: with the
//! always-on [`DummyExecution`] the only added work is counting transactions and
//! folding a rolling hash.
//!
//! [`begin_block`]: ExecutionEngine::begin_block
//! [`execute_transactions`]: ExecutionEngine::execute_transactions
//! [`end_block`]: ExecutionEngine::end_block
//! [`finalize`]: ExecutionEngine::finalize

use std::collections::BTreeMap;

use log::{debug, info};
use tokio::sync::mpsc;

use crate::crypto::Hash;
use crate::crypto::hash::hash_all;
use crate::crypto::merkle::GENESIS_BLOCK_HASH;
use crate::{BlockId, Slot, Transaction};

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

impl InProgressBlock {
    /// Returns the slot of this in-progress block.
    pub(crate) fn slot(&self) -> Slot {
        match self {
            InProgressBlock::Pending(slot) => *slot,
            InProgressBlock::Known((slot, _)) => *slot,
        }
    }
}

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
    /// Post-state root this node computed for the block.
    ///
    /// The caller compares this against the block's claimed root (or a quorum
    /// of peers) to detect divergence; the engine itself does not.
    pub state_hash: Hash,
}

/// Error that can occur during block execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecutionError {
    /// A transaction at the given index was invalid.
    InvalidTransaction { index: usize },
    /// Conflicting state accesses prevented parallel execution.
    StateConflict,
}

/// Transactions of one reconstructed slice, handed to the execution engine.
///
/// Carries the decoded transactions for one slice, along with enough metadata
/// for the execution engine to track block state. The first slice of a block
/// carries the (post-handover) parent block identifier in [`Self::parent`].
///
/// This type is intentionally separate from [`crate::consensus::BlockstoreEvent`]
/// so that the blockstore can feed execution independently of the voting logic.
#[derive(Clone, Debug)]
pub struct SliceEvent {
    /// Slot this slice belongs to.
    pub slot: Slot,
    /// Whether this is the last slice of the block.
    pub is_last: bool,
    /// Parent block, set only on the first slice of a block.
    pub parent: Option<BlockId>,
    /// Decoded transactions from the slice payload.
    pub transactions: Vec<Transaction>,
}

/// A message driving the execution engine for one block on the dissemination path.
///
/// The blockstore emits these in order once a block has fully reconstructed: one
/// [`Slice`](Self::Slice) per slice in slice-index order, followed by a single
/// [`Complete`](Self::Complete) carrying the now-known block hash. Feeding at
/// reconstruction time (rather than as individual shreds arrive) guarantees the
/// engine sees slices in a deterministic order, which matters for any engine
/// whose state root depends on transaction order (e.g. [`DummyExecution`]).
#[derive(Clone, Debug)]
pub enum ExecutionInput {
    /// Transactions of a single slice; drives `begin_block`/`execute_transactions`.
    Slice(SliceEvent),
    /// All slices received and the block hash is known; drives `end_block`.
    Complete { block_id: BlockId },
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
    fn begin_block(&mut self, id: InProgressBlock, parent: Option<BlockId>);

    /// Streams transactions from a single decoded slice of `slot`.
    ///
    /// Called once per slice as data arrives from dissemination.
    /// [`begin_block`] must have been called for `slot` beforehand.
    ///
    /// [`begin_block`]: Self::begin_block
    fn execute_transactions(&mut self, id: InProgressBlock, transactions: Vec<Transaction>);

    /// Notifies the engine that all slices for `block_id` have been received.
    ///
    /// Provides the full [`BlockId`] (including the block hash), which is only
    /// known after the double-Merkle tree has been computed over all slices.
    /// The engine should emit a [`ExecutionEvent`] through its channel to
    /// signal the outcome of execution for this block, reporting the computed
    /// post-state root in [`ExecutionResult::state_hash`].
    ///
    /// The engine does *not* validate that root against any expected value:
    /// whether the computed root agrees with the block's claimed root (or with
    /// other validators) is a consensus-layer decision, made by whoever consumes
    /// the [`ExecutionEvent`]. This keeps execution independent of consensus and
    /// leaves room for asynchronous execution, where no expected root may be
    /// available when the last slice arrives.
    fn end_block(&mut self, block_id: BlockId);

    /// Notifies the engine that `block_id` has been finalized by consensus.
    ///
    /// The engine may durably commit the execution state for `block_id` and
    /// prune any execution heads that are not ancestors of `block_id`.
    fn finalize(&mut self, block_id: BlockId);
}

/// Per-block execution state tracked by [`DummyExecution`].
struct BlockExec {
    /// Number of transactions executed so far for this block.
    tx_count: usize,
    /// Rolling state hash: seeded from the parent block hash and chained over
    /// each executed transaction. This is the post-state root this node computed.
    state_hash: Hash,
}

/// Placeholder execution engine that counts transactions and chains a state hash.
///
/// Tracks, per in-flight block, the running transaction count and a rolling
/// state hash (seeded from the parent block hash and folded over each executed
/// transaction). Emits an [`ExecutionEvent`] carrying both when a block is
/// completed via [`end_block`](ExecutionEngine::end_block). Does not perform any
/// real state transitions, and does not validate the computed root.
pub struct DummyExecution {
    /// Per-block execution state for each in-flight block.
    blocks: BTreeMap<InProgressBlock, BlockExec>,
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
            blocks: BTreeMap::new(),
            event_sender,
        }
    }
}

impl ExecutionEngine for DummyExecution {
    fn begin_block(&mut self, id: InProgressBlock, parent: Option<BlockId>) {
        match &id {
            InProgressBlock::Pending(slot) => {
                debug!("begin block in slot {slot} on parent {parent:?}");
            }
            InProgressBlock::Known((slot, hash)) => {
                debug!("begin block in slot {slot} (hash {hash:?}) on parent {parent:?}");
            }
        }
        let state_hash = parent
            .map_or(GENESIS_BLOCK_HASH, |(_, block_hash)| block_hash)
            .as_hash()
            .clone();
        self.blocks.insert(
            id,
            BlockExec {
                tx_count: 0,
                state_hash,
            },
        );
    }

    fn execute_transactions(&mut self, id: InProgressBlock, transactions: Vec<Transaction>) {
        match &id {
            InProgressBlock::Pending(slot) => {
                debug!(
                    "execute {} transactions for block in slot {slot}",
                    transactions.len()
                );
            }
            InProgressBlock::Known((slot, hash)) => {
                debug!(
                    "execute {} transactions for block in slot {slot} (hash {hash:?})",
                    transactions.len()
                );
            }
        }
        if let Some(exec) = self.blocks.get_mut(&id) {
            for tx in &transactions {
                exec.state_hash = hash_all(&[exec.state_hash.as_ref(), tx.0.as_slice()]);
            }
            exec.tx_count += transactions.len();
        }
    }

    fn end_block(&mut self, block_id: BlockId) {
        let result = self
            .blocks
            .get(&InProgressBlock::Known(block_id.clone()))
            .or_else(|| self.blocks.get(&InProgressBlock::Pending(block_id.0)))
            .map(|exec| ExecutionResult {
                tx_count: exec.tx_count,
                state_hash: exec.state_hash.clone(),
            });
        if let Some(result) = result {
            self.event_sender
                .try_send(ExecutionEvent::BlockExecuted { block_id, result })
                .unwrap();
        }
    }

    fn finalize(&mut self, block_id: BlockId) {
        self.blocks.retain(|id, _| id.slot() >= block_id.0);
        info!("finalized block {block_id:?}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::merkle::BlockHash;

    fn block_id(slot: u64) -> BlockId {
        (Slot::new(slot), GENESIS_BLOCK_HASH.clone())
    }

    /// Recomputes the rolling state hash the way [`DummyExecution`] does, so
    /// tests can assert against the root reported in an [`ExecutionResult`].
    fn expected_state_hash(parent: &BlockHash, txs: &[Transaction]) -> Hash {
        let mut h = parent.as_hash().clone();
        for tx in txs {
            h = hash_all(&[h.as_ref(), tx.0.as_slice()]);
        }
        h
    }

    #[test]
    fn dummy_counts_transactions_across_slices() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);
        let id = InProgressBlock::Pending(Slot::new(1));

        let txs = vec![
            Transaction(vec![1, 2, 3]),
            Transaction(vec![4]),
            Transaction(vec![5]),
        ];
        engine.begin_block(id.clone(), None);
        engine.execute_transactions(id.clone(), txs[..1].to_vec());
        engine.execute_transactions(id.clone(), txs[1..].to_vec());
        assert_eq!(engine.blocks[&id].tx_count, 3);

        let bid = block_id(1);
        engine.end_block(bid.clone());

        let event = rx.try_recv().unwrap();
        match event {
            ExecutionEvent::BlockExecuted { block_id, result } => {
                assert_eq!(block_id, bid);
                assert_eq!(result.tx_count, 3);
                assert_eq!(
                    result.state_hash,
                    expected_state_hash(&GENESIS_BLOCK_HASH, &txs)
                );
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

        engine.begin_block(InProgressBlock::Pending(Slot::new(1)), None);
        engine.begin_block(InProgressBlock::Pending(Slot::new(2)), Some(id1));
        engine.begin_block(InProgressBlock::Pending(Slot::new(3)), Some(id2.clone()));

        // Finalizing slot 2 should prune slot 1, but keep slots 2 and 3.
        engine.finalize(id2);

        assert!(
            !engine
                .blocks
                .contains_key(&InProgressBlock::Pending(Slot::new(1)))
        );
        assert!(
            engine
                .blocks
                .contains_key(&InProgressBlock::Pending(Slot::new(2)))
        );
        assert!(
            engine
                .blocks
                .contains_key(&InProgressBlock::Pending(Slot::new(3)))
        );
    }

    #[test]
    fn end_block_emits_event() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let id = InProgressBlock::Pending(Slot::new(5));
        engine.begin_block(id.clone(), Some(block_id(4)));
        engine.execute_transactions(id.clone(), vec![Transaction(vec![0]); 7]);

        let bid = block_id(5);
        engine.end_block(bid.clone());

        let event = rx.try_recv().unwrap();
        match event {
            ExecutionEvent::BlockExecuted { block_id, result } => {
                assert_eq!(block_id, bid);
                assert_eq!(result.tx_count, 7);
            }
            ExecutionEvent::BlockFailed { .. } => panic!("expected BlockExecuted"),
        }
    }

    #[test]
    fn end_block_with_known_block() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let bid = block_id(10);
        let id = InProgressBlock::Known(bid.clone());
        engine.begin_block(id.clone(), Some(block_id(9)));
        engine.execute_transactions(id.clone(), vec![Transaction(vec![42]); 2]);

        engine.end_block(bid.clone());

        let event = rx.try_recv().unwrap();
        match event {
            ExecutionEvent::BlockExecuted { block_id, result } => {
                assert_eq!(block_id, bid);
                assert_eq!(result.tx_count, 2);
            }
            ExecutionEvent::BlockFailed { .. } => panic!("expected BlockExecuted"),
        }
    }

    #[test]
    fn child_block_can_begin_after_parent_ends() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let id1 = InProgressBlock::Pending(Slot::new(1));
        let bid1 = block_id(1);
        engine.begin_block(id1.clone(), None);
        engine.execute_transactions(id1, vec![Transaction(vec![1])]);
        engine.end_block(bid1.clone());
        rx.try_recv().unwrap(); // consume the event

        // Slot 2 must be startable with slot 1 as its parent even after end_block.
        let id2 = InProgressBlock::Pending(Slot::new(2));
        engine.begin_block(id2.clone(), Some(bid1));
        engine.execute_transactions(
            id2.clone(),
            vec![Transaction(vec![2]), Transaction(vec![3])],
        );

        let bid2 = block_id(2);
        engine.end_block(bid2.clone());

        let event = rx.try_recv().unwrap();
        match event {
            ExecutionEvent::BlockExecuted { block_id, result } => {
                assert_eq!(block_id, bid2);
                assert_eq!(result.tx_count, 2);
            }
            ExecutionEvent::BlockFailed { .. } => panic!("expected BlockExecuted"),
        }
    }

    #[test]
    fn end_block_unknown_slot_returns_no_event() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let bid = block_id(99);
        engine.end_block(bid);

        assert!(rx.try_recv().is_err());
    }

    #[test]
    fn reports_computed_state_hash() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let id = InProgressBlock::Pending(Slot::new(1));
        let txs = vec![Transaction(vec![1, 2, 3]), Transaction(vec![4])];
        engine.begin_block(id.clone(), None);
        engine.execute_transactions(id, txs.clone());

        let bid = block_id(1);
        engine.end_block(bid.clone());

        let expected = expected_state_hash(&GENESIS_BLOCK_HASH, &txs);
        match rx.try_recv().unwrap() {
            ExecutionEvent::BlockExecuted { block_id, result } => {
                assert_eq!(block_id, bid);
                assert_eq!(result.tx_count, 2);
                assert_eq!(result.state_hash, expected);
            }
            ExecutionEvent::BlockFailed { .. } => panic!("expected BlockExecuted"),
        }
    }

    #[test]
    fn differing_transactions_diverge_state_hash() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let report_root =
            |engine: &mut DummyExecution, slot, tx_bytes, rx: &mut mpsc::Receiver<_>| {
                let id = InProgressBlock::Pending(Slot::new(slot));
                engine.begin_block(id.clone(), None);
                engine.execute_transactions(id, vec![Transaction(tx_bytes)]);
                engine.end_block(block_id(slot));
                match rx.try_recv().unwrap() {
                    ExecutionEvent::BlockExecuted { result, .. } => result.state_hash,
                    ExecutionEvent::BlockFailed { .. } => panic!("expected BlockExecuted"),
                }
            };

        // Same parent seed, different transactions => different computed root.
        // This is the divergence the caller compares against a claimed root.
        let root_a = report_root(&mut engine, 1, vec![1], &mut rx);
        let root_b = report_root(&mut engine, 2, vec![2], &mut rx);
        assert_ne!(root_a, root_b);
    }
}
