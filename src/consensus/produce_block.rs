// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::num::NonZeroUsize;
use std::time::{Duration, Instant};

use color_eyre::Result;
use either::Either;
use fastrace::Span;
use log::info;
use static_assertions::const_assert;
use tokio::pin;
use tokio::sync::oneshot;

use crate::crypto::Hash;
use crate::network::NetworkMessage;
use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
use crate::slice::{Slice, SliceHeader, SlicePayload};
use crate::{All2All, Disseminator, Slot, network::Network};
use crate::{BlockId, MAX_TRANSACTION_SIZE, MAX_TRANSACTIONS_PER_SLICE, highest_non_zero_byte};

use super::{Alpenglow, DELTA_BLOCK};

enum Continue {
    Continue { left: Duration },
    Stop,
}

impl<A, D, R, T> Alpenglow<A, D, R, T>
where
    A: All2All + Sync + Send + 'static,
    D: Disseminator + Sync + Send + 'static,
    R: Network + Sync + Send + 'static,
    T: Network + Sync + Send + 'static,
{
    /// Produces a block in the situation where we have not yet seen the `ParentReady` event.
    ///
    /// The `parent_block_id` refers to the block of the previous slot which may end up not being the actualy parent of the block.
    pub(super) async fn produce_block_parent_not_ready(
        &self,
        slot: Slot,
        parent_block_id: BlockId,
        mut parent_ready_receiver: oneshot::Receiver<BlockId>,
    ) -> Result<BlockId> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = parent_block_id;
        assert_eq!(parent_slot, slot.prev());
        assert!(slot.is_start_of_window());
        info!(
            "optimistically producing block in slot {} with parent {} in slot {}",
            slot,
            &hex::encode(parent_hash)[..8],
            parent_slot,
        );

        let mut sleep_duration = DELTA_BLOCK;
        for i in 0.. {
            let slice_index = match NonZeroUsize::new(i) {
                None => Either::Left((parent_block_id, 0)),
                Some(ind) => Either::Right(ind),
            };

            // If we have not yet received the `ParentReady` event, wait for it concurrently while producing the next slice.
            let produce_slice_future =
                produce_slice(&self.txs_receiver, slot, slice_index, sleep_duration);
            let (slice, cont_prod) = if parent_ready_receiver.is_terminated() {
                produce_slice_future.await
            } else {
                pin!(produce_slice_future);
                tokio::select! {
                    res = &mut produce_slice_future => res,
                    res = &mut parent_ready_receiver => {
                        // Got `ParentReady` event while producing slice.
                        // It's a NOP if we have been using the same parent as before.
                        // TODO: if parent is different, then implement optimistic handover.
                        let (new_slot, new_hash) = res.unwrap();
                        assert_eq!(new_slot, parent_slot);
                        assert_eq!(new_hash, parent_hash);
                        produce_slice_future.await
                  }
                }
            };

            if let Continue::Stop = &cont_prod
                && !parent_ready_receiver.is_terminated()
            {
                let (new_slot, new_hash) = (&mut parent_ready_receiver).await.unwrap();
                // TODO: implement optimistic handover.
                assert_eq!(new_slot, parent_slot);
                assert_eq!(new_hash, parent_hash);
            }

            if i == 0 {
                assert!(slice.parent.is_some());
            }

            let is_last = slice.is_last;
            let maybe_block_hash = self.shred_and_disseminate(slice).await?;
            match cont_prod {
                Continue::Stop => {
                    assert!(is_last);
                    let block_hash = maybe_block_hash.unwrap();
                    return Ok((slot, block_hash));
                }
                Continue::Continue { left } => {
                    assert!(!is_last);
                    assert!(maybe_block_hash.is_none());
                    sleep_duration = left;
                }
            }
        }
        unreachable!()
    }

    pub(crate) async fn produce_block_parent_ready(
        &self,
        slot: Slot,
        parent_block_id: BlockId,
    ) -> Result<BlockId> {
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        let (parent_slot, parent_hash) = parent_block_id;
        info!(
            "producing block in slot {} with ready parent {} in slot {}",
            slot,
            &hex::encode(parent_hash)[..8],
            parent_slot,
        );

        let mut sleep_duration = DELTA_BLOCK;
        for i in 0.. {
            let slice_index = if i == 0 {
                Either::Left((parent_block_id, 0))
            } else {
                Either::Right(NonZeroUsize::new(i).unwrap())
            };
            let (slice, cont_prod) =
                produce_slice(&self.txs_receiver, slot, slice_index, sleep_duration).await;
            if i == 0 {
                assert!(slice.parent.is_some());
            }

            let is_last = slice.is_last;
            let maybe_block_hash = self.shred_and_disseminate(slice).await?;
            match cont_prod {
                Continue::Stop => {
                    assert!(is_last);
                    let block_hash = maybe_block_hash.unwrap();
                    return Ok((slot, block_hash));
                }
                Continue::Continue { left } => {
                    assert!(!is_last);
                    assert!(maybe_block_hash.is_none());
                    sleep_duration = left;
                }
            }
        }
        unreachable!()
    }

    /// Shreds and disseminates the slice.
    ///
    /// Returns Ok(Some(Hash)) if slice.is_last == true.
    /// Returns Ok(None) if slice.is_last == false.
    async fn shred_and_disseminate(&self, slice: Slice) -> Result<Option<Hash>> {
        let mut maybe_block_hash = None;
        let slice_slot = slice.slot;
        let is_last = slice.is_last;
        let shreds = RegularShredder::shred(slice, &self.secret_key).unwrap();
        for s in shreds {
            self.disseminator.send(&s).await?;
            // PERF: move expensive add_shred() call out of block production
            let block = self
                .blockstore
                .write()
                .await
                .add_shred_from_disseminator(s)
                .await;
            if let Ok(Some((slot, block_info))) = block {
                assert_eq!(slot, slice_slot);
                maybe_block_hash = Some(block_info.hash);
                self.pool.write().await.add_block(slot, block_info).await;
            }
        }
        if is_last {
            assert!(maybe_block_hash.is_some());
        } else {
            assert!(maybe_block_hash.is_none());
        }
        Ok(maybe_block_hash)
    }
}

async fn produce_slice<T>(
    txs_receiver: &T,
    slot: Slot,
    slice_index: Either<(BlockId, usize), NonZeroUsize>,
    duration_left: Duration,
) -> (Slice, Continue)
where
    T: Network + Sync + Send + 'static,
{
    let start_time = Instant::now();
    const_assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE);
    let (parent, slice_index) = match slice_index {
        Either::Left((parent_block_id, slice_index)) => (Some(parent_block_id), slice_index),
        Either::Right(ind) => (None, ind.get()),
    };

    let parent_encoded_len = bincode::serde::encode_to_vec(parent, bincode::config::standard())
        .unwrap()
        .len();

    // Super hacky!!!  As long as the size of the txs vec fits in a single byte,
    // bincode encoding seems to take a single byte so account for that here.
    assert_eq!(highest_non_zero_byte(MAX_TRANSACTIONS_PER_SLICE), 1);
    let mut slice_capacity_left = MAX_DATA_PER_SLICE
        .checked_sub(parent_encoded_len)
        .unwrap()
        .checked_sub(1)
        .unwrap();
    let mut txs = Vec::new();

    let cont_prod = loop {
        let sleep_duration = duration_left.saturating_sub(Instant::now() - start_time);
        let res = tokio::select! {
            () = tokio::time::sleep(sleep_duration) => {
                break Continue::Stop;
            }
            res = txs_receiver.receive() => {
                res
            }
        };
        match res.expect("unexpected error") {
            NetworkMessage::Transaction(tx) => {
                let tx = bincode::serde::encode_to_vec(&tx, bincode::config::standard())
                    .expect("serialization should not panic");
                slice_capacity_left = slice_capacity_left.checked_sub(tx.len()).unwrap();
                txs.push(tx);
            }
            msg => {
                panic!("unexpected msg: {msg:?}");
            }
        }
        if slice_capacity_left < MAX_TRANSACTION_SIZE {
            let duration_left = duration_left.saturating_sub(Instant::now() - start_time);
            break Continue::Continue {
                left: duration_left,
            };
        }
    };

    // TODO: not accounting for this potentially expensive operation in duration_left calculation above.
    let txs = bincode::serde::encode_to_vec(&txs, bincode::config::standard())
        .expect("serialization should not panic");

    let is_last = match &cont_prod {
        Continue::Stop => true,
        Continue::Continue { .. } => false,
    };
    let header = SliceHeader {
        slot,
        slice_index,
        is_last,
    };
    let payload = SlicePayload::new(parent, txs);
    let slice = Slice::from_parts(header, payload, None);
    (slice, cont_prod)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::Transaction;
    use crate::crypto::Hash;
    use crate::network::UdpNetwork;

    use std::time::Duration;

    #[tokio::test]
    async fn produce_slice_empty_slices() {
        let txs_receiver = UdpNetwork::new_with_any_port();
        let sleep_duration = Duration::from_micros(1);
        let slot = Slot::new(1);
        // setting != 0 so that parent info is not included in slice
        let slice_index = 123;
        let (slice, cont) = produce_slice(
            &txs_receiver,
            slot,
            Either::Right(NonZeroUsize::new(slice_index).unwrap()),
            sleep_duration,
        )
        .await;
        match cont {
            Continue::Continue { .. } => panic!("Should not happen"),
            Continue::Stop => {
                let Slice {
                    slot,
                    slice_index,
                    is_last,
                    merkle_root,
                    parent,
                    data,
                } = slice;
                assert_eq!(slot, slot);
                assert_eq!(slice_index, slice_index);
                assert!(is_last);
                assert!(merkle_root.is_none());
                assert!(parent.is_none());
                assert_eq!(data.len(), 1);
            }
        }

        let parent_block_id = (slot.prev(), Hash::default());
        let (slice, cont) = produce_slice(
            &txs_receiver,
            slot,
            Either::Left((parent_block_id, 0)),
            sleep_duration,
        )
        .await;
        match cont {
            Continue::Continue { .. } => panic!("Should not happen"),
            Continue::Stop => {
                let Slice {
                    slot,
                    slice_index,
                    is_last,
                    merkle_root,
                    parent,
                    data,
                } = slice;
                assert_eq!(slot, slot);
                assert_eq!(slice_index, 0);
                assert!(is_last);
                assert!(merkle_root.is_none());
                assert_eq!(parent, Some(parent_block_id));
                assert_eq!(data.len(), 1);
            }
        }
    }

    #[tokio::test]
    async fn produce_slice_full_slices() {
        let txs_receiver = UdpNetwork::new_with_any_port();
        let addr = format!("127.0.0.1:{}", txs_receiver.port());
        let txs_sender = UdpNetwork::new_with_any_port();
        // long enough duration so hopefully doesn't fire while collecting txs
        let sleep_duration = Duration::from_secs(100);
        let slot = Slot::new(1);
        let slice_index = 123;

        tokio::spawn(async move {
            for i in 0..255 {
                let data = vec![i; MAX_TRANSACTION_SIZE];
                let msg = NetworkMessage::Transaction(Transaction(data));
                txs_sender.send(&msg, addr.clone()).await.unwrap();
            }
        });

        let (slice, cont) = produce_slice(
            &txs_receiver,
            slot,
            Either::Right(NonZeroUsize::new(slice_index).unwrap()),
            sleep_duration,
        )
        .await;
        match cont {
            Continue::Stop => panic!("Should not happen"),
            Continue::Continue { .. } => {
                let Slice {
                    slot,
                    slice_index,
                    is_last,
                    merkle_root,
                    parent,
                    data,
                } = slice;
                assert_eq!(slot, slot);
                assert_eq!(slice_index, slice_index);
                assert!(!is_last);
                assert!(merkle_root.is_none());
                assert!(parent.is_none());
                assert!(data.len() <= MAX_DATA_PER_SLICE);
                assert!(data.len() > MAX_DATA_PER_SLICE - MAX_TRANSACTION_SIZE);
            }
        }
    }
}
