// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::num::NonZeroUsize;
use std::time::{Duration, Instant};

use color_eyre::Result;
use either::Either;
use fastrace::Span;
use log::{info, warn};
use static_assertions::const_assert;

use crate::MAX_TRANSACTION_SIZE;
use crate::crypto::Hash;
use crate::network::NetworkMessage;
use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder, Slice};
use crate::{All2All, Disseminator, Slot, network::Network};

use super::{Alpenglow, DELTA_BLOCK};

enum Continue {
    Continue { left: Duration },
    Stop,
}

async fn produce_slice<T>(
    txs_receiver: &T,
    slot: Slot,
    slice_index: Either<(Slot, Hash, usize), NonZeroUsize>,
    time_left: Duration,
) -> (Slice, Continue)
where
    T: Network + Sync + Send + 'static,
{
    const_assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE);
    let (mut data, slice_index) = match slice_index {
        Either::Left((parent_slot, parent_hash, slice_index)) => {
            let mut data = Vec::with_capacity(MAX_DATA_PER_SLICE);
            // pack parent information in first slice
            data.extend_from_slice(&parent_slot.inner().to_be_bytes());
            data.extend_from_slice(&parent_hash);
            let slice_capacity_left = MAX_DATA_PER_SLICE.checked_sub(data.len()).unwrap();
            assert!(slice_capacity_left >= MAX_TRANSACTION_SIZE);
            // FIXME: add support for optimistic handover. parent can change in middle of block production.
            assert_eq!(slice_index, 0);
            (data, slice_index)
        }
        Either::Right(ind) => (Vec::with_capacity(MAX_DATA_PER_SLICE), ind.get()),
    };
    let mut left = time_left;

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
                            let mut bytes = bincode::serde::encode_to_vec(&tx, bincode::config::standard())
                                .expect("serialization should not panic");
                            data.append(&mut bytes);
                            let slice_capacity_left = MAX_DATA_PER_SLICE.checked_sub(data.len()).unwrap();
                            if slice_capacity_left < MAX_TRANSACTION_SIZE {
                                break Continue::Continue { left };
                            }
                        }
                        msg => {
                            panic!("Unexpected msg {msg:?}");
                        }
                    },
                }
                left = left.saturating_sub(Instant::now() - start_time);
            }
        }
    };

    let is_last = match &cont_prod {
        Continue::Stop => true,
        Continue::Continue { .. } => false,
    };
    (
        Slice {
            slot,
            slice_index,
            is_last,
            merkle_root: None,
            data,
        },
        cont_prod,
    )
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
            "producing block in slot {} with parent {} in slot {}",
            slot,
            &hex::encode(parent_hash)[..8],
            parent_slot
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
            let shreds = RegularShredder::shred(&slice, &self.secret_key).unwrap();
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
                if let Some(p) = pool.parents_ready(slot).first() {
                    if *p != parent {
                        warn!("switching block production parent");
                        unimplemented!("have to switch parents");
                    }
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
                    data,
                } = slice;
                assert_eq!(slot, slot);
                assert_eq!(slice_index, slice_index);
                assert!(is_last);
                assert!(merkle_root.is_none());
                assert_eq!(data.len(), 0);
            }
        }

        let (slice, cont) = produce_slice(
            &txs_receiver,
            slot,
            Either::Left((slot.prev(), Hash::default(), 0)),
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
                    data,
                } = slice;
                assert_eq!(slot, slot);
                assert_eq!(slice_index, 0);
                assert!(is_last);
                assert!(merkle_root.is_none());
                assert_eq!(data.len(), 8 + 32);
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
                    data,
                } = slice;
                assert_eq!(slot, slot);
                assert_eq!(slice_index, slice_index);
                assert!(!is_last);
                assert!(merkle_root.is_none());
                assert!(data.len() <= MAX_DATA_PER_SLICE);
                assert!(data.len() > MAX_DATA_PER_SLICE - MAX_TRANSACTION_SIZE);
            }
        }
    }
}
