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
//! Building blocks for a real execution engine's state handling live in submodules:
//! - [`state`] provides [`State`], a copy-on-write account state that makes
//!   maintaining one state per unfinalized block in the block tree cheap.
//! - [`commitment`] provides [`LtHash`], an incrementally updatable
//!   commitment to the contents of a [`State`].
//!
//! [`begin_block`]: ExecutionEngine::begin_block
//! [`execute_transactions`]: ExecutionEngine::execute_transactions
//! [`end_block`]: ExecutionEngine::end_block
//! [`finalize`]: ExecutionEngine::finalize

pub mod commitment;
pub mod state;

use std::collections::BTreeMap;

use log::{debug, info};
use tokio::sync::mpsc;

pub use self::commitment::{LtHash, StateCommitment};
pub use self::state::{Address, State};
use crate::crypto::Hash;
use crate::crypto::hash::hash_all;
use crate::crypto::merkle::{GENESIS_BLOCK_HASH, MerkleRoot};
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
    /// Execution of a block has completed, successfully or otherwise.
    BlockExecuted {
        block_id: BlockId,
        result: Result<ExecutionResult, ExecutionError>,
    },
}

/// Result of a successful block execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecutionResult {
    /// Number of transactions executed in this block.
    pub tx_count: usize,
    /// Commitment to the post-execution state.
    ///
    /// The caller should check this, based on the execution model:
    /// - Synchronous execution: Check against the block's claimed commitment.
    /// - Asynchronous execution: Check against the commitment finalized by consensus.
    pub state_commitment: StateCommitment,
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
/// This type is intentionally separate from [`crate::consensus::BlockstoreEvent`]
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
///    been received, providing the block hash. The engine should emit an
///    [`ExecutionEvent::BlockExecuted`] event through its channel, carrying the
///    execution outcome as a `Result`.
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
    /// The engine should emit an [`ExecutionEvent::BlockExecuted`] through its
    /// channel to signal the outcome of execution for this block, reporting the
    /// computed post-state commitment in [`ExecutionResult::state_commitment`].
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
    /// Rolling state hash: seeded from the parent's computed state hash (or the
    /// parent block hash / genesis as a fallback) and chained over each executed
    /// transaction. This is the post-state root this node computed.
    state_hash: Hash,
}

/// Placeholder execution engine that counts transactions and chains a state hash.
///
/// Tracks, per in-flight block, the running transaction count and a rolling
/// state hash (seeded from the parent's computed state hash and folded over each
/// executed transaction). Emits an [`ExecutionEvent`] carrying both when a block
/// is completed via [`end_block`](ExecutionEngine::end_block). Does not perform
/// any real state transitions, and does not validate the computed root.
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
        // Seed from the parent's *computed* state hash, so divergence in the
        // parent's execution propagates into every descendant root, the way a
        // real state root compounds upstream changes forward. Fall back to the
        // consensus-agreed parent block hash (or genesis) when we haven't
        // executed the parent ourselves: cold start, repair, or a parent
        // already pruned by finalization.
        let state_hash = parent
            .as_ref()
            .and_then(|p| {
                self.blocks
                    .get(&InProgressBlock::Known(p.clone()))
                    .or_else(|| self.blocks.get(&InProgressBlock::Pending(p.0)))
            })
            .map(|exec| exec.state_hash.clone())
            .unwrap_or_else(|| {
                parent
                    .map_or(GENESIS_BLOCK_HASH, |(_, block_hash)| block_hash)
                    .as_hash()
                    .clone()
            });
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
                state_commitment: exec.state_hash.clone().into(),
            });
        if let Some(result) = result {
            self.event_sender
                .try_send(ExecutionEvent::BlockExecuted {
                    block_id,
                    result: Ok(result),
                })
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
    /// tests can assert against the commitment reported in an [`ExecutionResult`].
    fn expected_state_commitment(parent: &BlockHash, txs: &[Transaction]) -> StateCommitment {
        let mut h = parent.as_hash().clone();
        for tx in txs {
            h = hash_all(&[h.as_ref(), tx.0.as_slice()]);
        }
        h.into()
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

        let ExecutionEvent::BlockExecuted { block_id, result } = rx.try_recv().unwrap();
        let result = result.expect("execution should succeed");
        assert_eq!(block_id, bid);
        assert_eq!(result.tx_count, 3);
        assert_eq!(
            result.state_commitment,
            expected_state_commitment(&GENESIS_BLOCK_HASH, &txs)
        );
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

        let ExecutionEvent::BlockExecuted { block_id, result } = rx.try_recv().unwrap();
        let result = result.expect("execution should succeed");
        assert_eq!(block_id, bid);
        assert_eq!(result.tx_count, 7);
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

        let ExecutionEvent::BlockExecuted { block_id, result } = rx.try_recv().unwrap();
        let result = result.expect("execution should succeed");
        assert_eq!(block_id, bid);
        assert_eq!(result.tx_count, 2);
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

        let ExecutionEvent::BlockExecuted { block_id, result } = rx.try_recv().unwrap();
        let result = result.expect("execution should succeed");
        assert_eq!(block_id, bid2);
        assert_eq!(result.tx_count, 2);
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
    fn reports_computed_state_commitment() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let id = InProgressBlock::Pending(Slot::new(1));
        let txs = vec![Transaction(vec![1, 2, 3]), Transaction(vec![4])];
        engine.begin_block(id.clone(), None);
        engine.execute_transactions(id, txs.clone());

        let bid = block_id(1);
        engine.end_block(bid.clone());

        let expected = expected_state_commitment(&GENESIS_BLOCK_HASH, &txs);
        let ExecutionEvent::BlockExecuted { block_id, result } = rx.try_recv().unwrap();
        let result = result.expect("execution should succeed");
        assert_eq!(block_id, bid);
        assert_eq!(result.tx_count, 2);
        assert_eq!(result.state_commitment, expected);
    }

    #[test]
    fn differing_transactions_diverge_state_commitment() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        let report_root =
            |engine: &mut DummyExecution, slot, tx_bytes, rx: &mut mpsc::Receiver<_>| {
                let id = InProgressBlock::Pending(Slot::new(slot));
                engine.begin_block(id.clone(), None);
                engine.execute_transactions(id, vec![Transaction(tx_bytes)]);
                engine.end_block(block_id(slot));
                let ExecutionEvent::BlockExecuted { result, .. } = rx.try_recv().unwrap();
                result.expect("execution should succeed").state_commitment
            };

        // Same parent seed, different transactions => different computed root.
        // This is the divergence the caller compares against a claimed root.
        let root_a = report_root(&mut engine, 1, vec![1], &mut rx);
        let root_b = report_root(&mut engine, 2, vec![2], &mut rx);
        assert_ne!(root_a, root_b);
    }

    #[test]
    fn parent_state_divergence_propagates_to_child() {
        let (tx, mut rx) = mpsc::channel(16);
        let mut engine = DummyExecution::new(tx);

        // Execute a parent (with `parent_tx`), then an identical child on top.
        let mut child_root = move |parent_slot, parent_tx, child_slot| {
            let parent = InProgressBlock::Pending(Slot::new(parent_slot));
            engine.begin_block(parent.clone(), None);
            engine.execute_transactions(parent, vec![Transaction(parent_tx)]);
            engine.end_block(block_id(parent_slot));
            rx.try_recv().unwrap(); // consume the parent's event

            let child = InProgressBlock::Pending(Slot::new(child_slot));
            engine.begin_block(child.clone(), Some(block_id(parent_slot)));
            engine.execute_transactions(child, vec![Transaction(vec![7])]);
            engine.end_block(block_id(child_slot));
            let ExecutionEvent::BlockExecuted { result, .. } = rx.try_recv().unwrap();
            result.expect("execution should succeed").state_commitment
        };

        // The children share an identical transaction and an identical parent
        // *block hash* (`block_id` always uses the genesis hash), but their
        // parents executed different transactions. Seeding from the parent's
        // computed state hash makes that upstream divergence reach the child;
        // seeding from the parent block hash alone would collide here.
        let child_a = child_root(1, vec![1], 2);
        let child_b = child_root(3, vec![2], 4);
        assert_ne!(child_a, child_b);
    }
}
