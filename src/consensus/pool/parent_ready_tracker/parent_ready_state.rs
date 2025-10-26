// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use either::Either;
use log::warn;
use smallvec::{SmallVec, smallvec};
use tokio::sync::oneshot;

use crate::BlockId;
use crate::crypto::Hash;
use crate::crypto::merkle::BlockHash;

/// Tracks the status of whether an individual slot has a parent ready.
enum IsReady {
    /// Do not have a parent ready for this slot yet.
    ///
    /// Might have someone waiting to hear when the slot does become ready.
    NotReady(Option<oneshot::Sender<BlockId>>),
    /// Have at least one parent ready for this slot.
    ///
    /// We can potentially have multiple parents ready per slot, but we
    /// optimize for the common case where there will only be one.
    Ready(SmallVec<[BlockId; 1]>),
}

impl Default for IsReady {
    fn default() -> Self {
        IsReady::NotReady(None)
    }
}

/// Holds the relevant state for a single slot.
#[derive(Default)]
pub(super) struct ParentReadyState {
    /// Whether this slot is skip-certified.
    skip: bool,
    /// Blocks that are notarized-fallback for this slot, if any.
    ///
    /// We can potentially have multiple notar fallbacks per slot,
    /// but we optimize for the common case where there will only be one.
    notar_fallbacks: SmallVec<[BlockHash; 1]>,
    /// Current status of the parent-ready condition for this slot.
    // NOTE: Do not make this field more visible.
    // Updating it must sometimes produce additional actions.
    is_ready: IsReady,
}

impl ParentReadyState {
    /// Creates a new [`ParentReadyState`] for the genesis block.
    pub(super) fn genesis() -> Self {
        Self {
            skip: false,
            notar_fallbacks: SmallVec::from([Hash::default().into()]),
            is_ready: IsReady::default(),
        }
    }

    /// Marks this slot as skip-certified.
    ///
    /// Returns `true` iff this slot was not already skip-certified.
    pub(super) fn mark_skip(&mut self) -> bool {
        let was_skipped = self.skip;
        self.skip = true;
        !was_skipped
    }

    /// Returns `true` iff this slot is skip-certified.
    pub(super) fn is_skip_certified(&self) -> bool {
        self.skip
    }

    /// Marks the given block as notarized-fallback.
    ///
    /// Returns `true` iff this block was not already marked as notarized-fallback.
    pub(super) fn mark_notar_fallback(&mut self, hash: BlockHash) -> bool {
        let was_certified = self.notar_fallbacks.contains(&hash);
        self.notar_fallbacks.push(hash);
        !was_certified
    }

    /// Returns an iterator over the notarized-fallback block hashes for this slot.
    pub(super) fn notar_fallback_blocks(&self) -> impl Iterator<Item = BlockHash> {
        self.notar_fallbacks.iter().cloned()
    }

    /// Adds a [`BlockId`] to the parents ready list.
    ///
    /// Additionally, will inform any waiters.
    ///
    /// # Panics
    ///
    /// If the specific parent is already marked ready for this slot.
    pub(super) fn add_to_ready(&mut self, id: BlockId) {
        match &mut self.is_ready {
            IsReady::NotReady(sender) => {
                let sender = sender.take();
                match sender {
                    None => (),
                    Some(sender) => match sender.send(id.clone()) {
                        Ok(()) => (),
                        Err(id) => {
                            warn!("sending {id:?} failed, receiver deallocated");
                        }
                    },
                }
                self.is_ready = IsReady::Ready(smallvec![id]);
            }
            IsReady::Ready(ready_ids) => {
                assert!(!ready_ids.contains(&id));
                ready_ids.push(id);
            }
        }
    }

    /// Returns the list of currently valid parents for this slot.
    pub(super) fn ready_block_ids(&self) -> &[BlockId] {
        match &self.is_ready {
            IsReady::NotReady(_) => &[],
            IsReady::Ready(block_ids) => block_ids,
        }
    }

    /// Requests to know a valid parent for this slot.
    ///
    /// Returns either:
    /// - The block ID of a parent if at least one parent is already ready.
    ///   Always returns a parent with minimal slot number if multiple parents are ready.
    /// - A receiver of a oneshot channel that will receive the first parent's block ID.
    pub(super) fn wait_for_parent_ready(&mut self) -> Either<BlockId, oneshot::Receiver<BlockId>> {
        match &mut self.is_ready {
            IsReady::Ready(block_ids) => {
                assert!(!block_ids.is_empty());
                block_ids.sort();
                Either::Left(block_ids[0].clone())
            }
            IsReady::NotReady(maybe_waiter) => {
                assert!(maybe_waiter.is_none());
                let (tx, rx) = oneshot::channel();
                self.is_ready = IsReady::NotReady(Some(tx));
                Either::Right(rx)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Slot;

    #[test]
    fn wait_for_parent_ready_no_blocking() {
        let mut state = ParentReadyState::default();
        assert_eq!(state.ready_block_ids().len(), 0);
        let block_id = (Slot::new(0), [1; 32].into());
        state.add_to_ready(block_id.clone());
        let res = state.wait_for_parent_ready();
        let Either::Left(received_block_id) = res else {
            panic!("unexpected result {res:?}");
        };
        assert_eq!(received_block_id, block_id);
        assert_eq!(state.ready_block_ids().len(), 1);
    }

    #[tokio::test]
    async fn wait_for_parent_ready_blocking() {
        let mut state = ParentReadyState::default();
        assert_eq!(state.ready_block_ids().len(), 0);
        let res = state.wait_for_parent_ready();
        let Either::Right(rx) = res else {
            panic!("unexpected result {res:?}");
        };
        let block_id = (Slot::new(0), [1; 32].into());
        state.add_to_ready(block_id.clone());
        let received_block_id = rx.await.unwrap();
        assert_eq!(received_block_id, block_id);
        assert_eq!(state.ready_block_ids().len(), 1);
    }
}
