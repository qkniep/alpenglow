// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::num::NonZeroUsize;
use std::time::{Duration, Instant};

use color_eyre::Result;
use either::Either;
use fastrace::Span;
use log::{info, warn};
use static_assertions::const_assert;

use crate::crypto::Hash;
use crate::network::NetworkMessage;
use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
use crate::slice::{Slice, SliceHeader, SlicePayload};
use crate::{All2All, Disseminator, Slot, network::Network};
use crate::{MAX_TRANSACTION_SIZE, MAX_TRANSACTIONS_PER_SLICE, highest_non_zero_byte};

use super::{Alpenglow, DELTA_BLOCK};

enum Continue {
    Continue { left: Duration },
    Stop,
}

async fn produce_slice<T>(
    txs_receiver: &T,
    slot: Slot,
    slice_index: Either<(Slot, Hash, usize), NonZeroUsize>,
    mut time_left: Duration,
) -> (Slice, Continue)
where
    T: Network + Sync + Send + 'static,
{
    const_assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE);
    let (parent, slice_index) = match slice_index {
        Either::Left((parent_slot, parent_hash, slice_index)) => {
            (Some((parent_slot, parent_hash)), slice_index)
        }
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
        let start_time = Instant::now();
        tokio::select! {
            () = tokio::time::sleep(time_left) => {
                break Continue::Stop;
            }

            val = txs_receiver.receive() => {
                match val {
                    Err(err) => panic!("Unexpected error {err}"),
                    Ok(msg) => match msg {
                        NetworkMessage::Transaction(tx) => {
                            let tx = bincode::serde::encode_to_vec(&tx, bincode::config::standard())
                                .expect("serialization should not panic");
                            slice_capacity_left = slice_capacity_left.checked_sub(tx.len()).unwrap();
                            txs.push(tx);
                            // subtract from time left should be the final action to ensure it accounts for all work done in the loop.
                            time_left = time_left.saturating_sub(Instant::now() - start_time);
                            if slice_capacity_left < MAX_TRANSACTION_SIZE {
                                break Continue::Continue { left: time_left };
                            }
                        }
                        msg => {
                            panic!("Unexpected msg {msg:?}");
                        }
                    },
                }
            }
        }
    };

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

impl<A, D, R, T> Alpenglow<A, D, R, T>
where
    A: All2All + Sync + Send + 'static,
    D: Disseminator + Sync + Send + 'static,
    R: Network + Sync + Send + 'static,
    T: Network + Sync + Send + 'static,
{
    pub(crate) async fn produce_block(
        &self,
        slot: Slot,
        parent: (Slot, Hash),
        parent_ready: bool,
    ) -> Result<()> {
        let (parent_slot, parent_hash) = parent;
        let _slot_span = Span::enter_with_local_parent(format!("slot {slot}"));
        info!(
            "producing block in slot {} with parent {} in slot {} (parent ready: {})",
            slot,
            &hex::encode(parent_hash)[..8],
            parent_slot,
            parent_ready,
        );

        let mut sleep_duration = DELTA_BLOCK;
        for slice_index in 0.. {
            let slice_index = match NonZeroUsize::new(slice_index) {
                None => Either::Left((parent_slot, parent_hash, 0)),
                Some(ind) => Either::Right(ind),
            };
            let (slice, cont_prod) =
                produce_slice(&self.txs_receiver, slot, slice_index, sleep_duration).await;
            // shred and disseminate slice
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
                    self.pool.write().await.add_block(slot, block_info).await;
                }
            }

            // switch parent if necessary (for optimistic handover)
            if !parent_ready {
                let pool = self.pool.read().await;
                if let Some(p) = pool.parents_ready(slot).first()
                    && *p != parent
                {
                    warn!(
                        "switching block production parent from {} in slot {} to {} in slot {}",
                        &hex::encode(parent.1)[..8],
                        parent.0,
                        &hex::encode(p.1)[..8],
                        p.0,
                    );
                    unimplemented!("have to switch parents");
                }
            }

            match cont_prod {
                Continue::Stop => break,
                Continue::Continue {
                    left: left_duration,
                } => sleep_duration = left_duration,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{Transaction, network::UdpNetwork};

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

        let parent_slot = slot.prev();
        let parent_hash = Hash::default();
        let (slice, cont) = produce_slice(
            &txs_receiver,
            slot,
            Either::Left((parent_slot, parent_hash, 0)),
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
                assert_eq!(parent, Some((parent_slot, parent_hash)));
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
