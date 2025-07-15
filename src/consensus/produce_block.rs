use std::time::{Duration, Instant};

use color_eyre::Result;
use fastrace::Span;
use log::{info, warn};

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
    slice_index: usize,
    parent: (Slot, Hash),
    sleep_duration: Duration,
) -> (Slice, Continue)
where
    T: Network + Sync + Send + 'static,
{
    let (parent_slot, parent_hash) = parent;
    debug_assert!(MAX_DATA_PER_SLICE >= MAX_TRANSACTION_SIZE);
    let mut data = Vec::with_capacity(MAX_DATA_PER_SLICE);
    // pack parent information in first slice
    if slice_index == 0 {
        data.extend_from_slice(&parent_slot.to_be_bytes());
        data.extend_from_slice(&parent_hash);
        let slice_capacity_left = MAX_DATA_PER_SLICE.checked_sub(data.len()).unwrap();
        assert!(slice_capacity_left >= MAX_TRANSACTION_SIZE);
    }
    let mut left = sleep_duration;

    let cont_prod = loop {
        let start_time = Instant::now();
        tokio::select! {
            () = tokio::time::sleep(sleep_duration) => {
                break Continue::Stop;
            }

            val = txs_receiver.receive() => {
                match val {
                    Err(_e) => unimplemented!(),
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
                            panic!("Unexpected msg {:?}", msg);
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
            let (slice, cont_prod) = produce_slice(
                &self.txs_receiver,
                slot,
                slice_index,
                parent,
                sleep_duration,
            )
            .await;
            // shred and disseminate slice
            let shreds = RegularShredder::shred(&slice, &self.secret_key).unwrap();
            for s in shreds {
                self.disseminator.send(&s).await?;
                // PERF: move expensive add_shred() call out of block production
                let block = self.blockstore.write().await.add_shred(s, true).await;
                if let Some((slot, block_info)) = block {
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
