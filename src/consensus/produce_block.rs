// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

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
use crate::{
    BlockId, MAX_SLICES_PER_BLOCK, MAX_TRANSACTION_SIZE, MAX_TRANSACTIONS_PER_SLICE,
    highest_non_zero_byte,
};

use super::{Alpenglow, DELTA_BLOCK};

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

        let mut duration_left = DELTA_BLOCK;
        for slice_index in 0..MAX_SLICES_PER_BLOCK {
            let parent = if slice_index == 0 {
                Some(parent_block_id)
            } else {
                None
            };

            // If we have not yet received the `ParentReady` event, wait for it concurrently while producing the next slice.
            let produce_slice_future =
                produce_slice_payload(&self.txs_receiver, parent, duration_left);
            let (payload, maybe_duration) = if parent_ready_receiver.is_terminated() {
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

            let is_last = slice_index == MAX_SLICES_PER_BLOCK - 1 || maybe_duration.is_none();
            if is_last && !parent_ready_receiver.is_terminated() {
                let (new_slot, new_hash) = (&mut parent_ready_receiver).await.unwrap();
                // TODO: implement optimistic handover.
                assert_eq!(new_slot, parent_slot);
                assert_eq!(new_hash, parent_hash);
            }

            match self
                .shred_and_disseminate(slice_index, slot, payload, maybe_duration)
                .await?
            {
                Either::Left(block_hash) => return Ok((slot, block_hash)),
                Either::Right(duration) => duration_left = duration,
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

        let mut duration_left = DELTA_BLOCK;
        for slice_index in 0.. {
            let parent = if slice_index == 0 {
                Some(parent_block_id)
            } else {
                None
            };
            let (payload, maybe_duration) =
                produce_slice_payload(&self.txs_receiver, parent, duration_left).await;

            match self
                .shred_and_disseminate(slice_index, slot, payload, maybe_duration)
                .await?
            {
                Either::Left(block_hash) => return Ok((slot, block_hash)),
                Either::Right(duration) => duration_left = duration,
            }
        }
        unreachable!()
    }

    /// Shreds and disseminates the slice payload.
    ///
    /// Returns Ok(Either::Left(hash of the block)) if this is the last slice.
    /// Returns Ok(Either::Right(duration left in block)) if this is not the last slice.
    async fn shred_and_disseminate(
        &self,
        slice_index: usize,
        slot: Slot,
        payload: SlicePayload,
        maybe_duration: Option<Duration>,
    ) -> Result<Either<Hash, Duration>> {
        let is_last = slice_index == MAX_SLICES_PER_BLOCK - 1 || maybe_duration.is_none();
        let header = SliceHeader {
            is_last,
            slot,
            slice_index,
        };
        let slice = Slice::from_parts(header, payload, None);
        let mut maybe_block_hash = None;
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
            if let Ok(Some((block_slot, block_info))) = block {
                assert_eq!(block_slot, slot);
                maybe_block_hash = Some(block_info.hash);
                self.pool.write().await.add_block(slot, block_info).await;
            }
        }
        let ret = if is_last {
            Either::Left(maybe_block_hash.unwrap())
        } else {
            assert!(maybe_block_hash.is_none());
            Either::Right(maybe_duration.unwrap())
        };
        Ok(ret)
    }
}

async fn produce_slice_payload<T>(
    txs_receiver: &T,
    parent: Option<BlockId>,
    duration_left: Duration,
) -> (SlicePayload, Option<Duration>)
where
    T: Network + Sync + Send + 'static,
{
    let start_time = Instant::now();
    const_assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE);

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

    let ret = loop {
        let sleep_duration = duration_left.saturating_sub(Instant::now() - start_time);
        let res = tokio::select! {
            () = tokio::time::sleep(sleep_duration) => {
                break None;
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
            break Some(duration_left);
        }
    };

    // TODO: not accounting for this potentially expensive operation in duration_left calculation above.
    let txs = bincode::serde::encode_to_vec(&txs, bincode::config::standard())
        .expect("serialization should not panic");
    let payload = SlicePayload::new(parent, txs);
    (payload, ret)
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
        let duration_left = Duration::from_micros(1);

        let parent = None;
        let (payload, maybe_duration) =
            produce_slice_payload(&txs_receiver, parent, duration_left).await;
        assert!(maybe_duration.is_none());
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 1 byte
        assert_eq!(payload.data.len(), 1);

        let parent = Some((Slot::genesis(), Hash::default()));
        let (payload, maybe_duration) =
            produce_slice_payload(&txs_receiver, parent, duration_left).await;
        assert!(maybe_duration.is_none());
        assert_eq!(payload.parent, parent);
        // bin encoding an empty Vec takes 1 byte
        assert_eq!(payload.data.len(), 1);
    }

    #[tokio::test]
    async fn produce_slice_full_slices() {
        let txs_receiver = UdpNetwork::new_with_any_port();
        let addr = format!("127.0.0.1:{}", txs_receiver.port());
        let txs_sender = UdpNetwork::new_with_any_port();
        // long enough duration so hopefully doesn't fire while collecting txs
        let duration_left = Duration::from_secs(100);

        tokio::spawn(async move {
            for i in 0..255 {
                let data = vec![i; MAX_TRANSACTION_SIZE];
                let msg = NetworkMessage::Transaction(Transaction(data));
                txs_sender.send(&msg, addr.clone()).await.unwrap();
            }
        });

        let parent = None;
        let (payload, maybe_duration) =
            produce_slice_payload(&txs_receiver, parent, duration_left).await;
        assert!(maybe_duration.is_some());
        assert_eq!(payload.parent, parent);
        assert!(payload.data.len() <= MAX_DATA_PER_SLICE);
        assert!(payload.data.len() > MAX_DATA_PER_SLICE - MAX_TRANSACTION_SIZE);
    }
}
