// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implements Reed-Solomon shreding and deshreding.
//!
//! This is a low-level module that is used in various shredder implementations.
//! It is mostly a wrapper around the [`reed_solomon_simd`] crate.

use reed_solomon_simd::{ReedSolomonDecoder, ReedSolomonEncoder};
use static_assertions::const_assert;
use thiserror::Error;

use super::{DATA_SHREDS, MAX_DATA_PER_SLICE, MAX_DATA_PER_SLICE_AFTER_PADDING, TOTAL_SHREDS};
use crate::shredder::MAX_DATA_PER_SHRED;

/// Errors that may be returned by [`ReedSolomonCoder::shred`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(super) enum ReedSolomonShredError {
    #[error("too much data for slice")]
    TooMuchData,
}

/// Errors that may be returned by [`ReedSolomonCoder::deshred`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(super) enum ReedSolomonDeshredError {
    #[error("not enough shreds to reconstruct")]
    NotEnoughShreds,
    #[error("too much data for slice")]
    TooMuchData,
    #[error("invalid padding detected")]
    InvalidPadding,
}

/// The data and coding shreds returned from [`ReedSolomonCoder::shred`] on success.
pub(super) struct RawShreds {
    /// A list of data shreds.
    pub(super) data: Vec<Vec<u8>>,
    /// A list of coding shreds.
    pub(super) coding: Vec<Vec<u8>>,
}

/// Byte-level input to [`ReedSolomonCoder::reconstruct_data`].
///
/// This is the erasure layer's view of a received shred set: just indices and
/// payload bytes, with none of the wire/Merkle machinery of a
/// [`ValidatedShreds`](super::validated_shreds::ValidatedShreds). The shredder
/// layer builds it via `ValidatedShreds::received`.
pub(super) struct ReceivedShreds<'a> {
    /// Present data shreds as `(global shred index, payload bytes)`.
    pub(super) data: Vec<(usize, &'a [u8])>,
    /// Present coding shreds as `(coding-relative index, payload bytes)`.
    pub(super) coding: Vec<(usize, &'a [u8])>,
    /// Size in bytes of every present shred (the constructor enforces equality).
    pub(super) shred_bytes: usize,
}

/// Reed-Solomon coder for shreds.
///
/// This is a wrapper around both [`ReedSolomonEncoder`] and [`ReedSolomonDecoder`].
/// Therefore, it can be used for both encoding and decoding.
/// Reusing this over multiple slices prevents reallocating working memory.
pub(super) struct ReedSolomonCoder {
    num_coding: usize,
    encoder: ReedSolomonEncoder,
    decoder: ReedSolomonDecoder,
}

impl ReedSolomonCoder {
    /// Creates a new Reed-Solomon coder.
    ///
    /// It is initialized for [`DATA_SHREDS`] data shreds and `num_coding` coding shreds.
    /// It is also initialized for up to [`MAX_DATA_PER_SHRED`] bytes per fragment.
    pub(super) fn new(num_coding: usize) -> ReedSolomonCoder {
        // max shreds supported by RS field
        const_assert!(DATA_SHREDS + TOTAL_SHREDS <= 65536);

        assert!(num_coding <= TOTAL_SHREDS);

        let encoder = ReedSolomonEncoder::new(DATA_SHREDS, num_coding, MAX_DATA_PER_SHRED).unwrap();
        let decoder = ReedSolomonDecoder::new(DATA_SHREDS, num_coding, MAX_DATA_PER_SHRED).unwrap();

        ReedSolomonCoder {
            num_coding,
            encoder,
            decoder,
        }
    }

    /// Reed-Solomon encodes the `payload` into [`RawShreds`].
    ///
    /// For this, it splits the given slice into [`DATA_SHREDS`] data shreds.
    /// Then, it generates and adds `num_coding` additional Reed-Solomon coding shreds.
    ///
    /// First, however, padding is added to the payload to make it a multiple of `2 * DATA_SHREDS`.
    /// Bit padding of one 1bit and as many 0 bits as needed is added.
    /// In the byte representation this looks like `[0x80, 0x00, ..., 0x00]`.
    ///
    /// # Errors
    ///
    /// If the provided payload is larger than [`MAX_DATA_PER_SLICE_AFTER_PADDING`] then returns [`ReedSolomonDeshredError::TooMuchData`].
    pub(super) fn shred(&mut self, payload: &[u8]) -> Result<RawShreds, ReedSolomonShredError> {
        if payload.len() > MAX_DATA_PER_SLICE {
            return Err(ReedSolomonShredError::TooMuchData);
        }

        // determine padding length & configure encoder for shred length
        let padding_bytes = 2 * DATA_SHREDS - payload.len() % (2 * DATA_SHREDS);
        let shred_bytes = (payload.len() + padding_bytes).div_ceil(DATA_SHREDS);
        self.encoder
            .reset(DATA_SHREDS, self.num_coding, shred_bytes)
            .expect("shred size with padding should be supported");

        // add padding to last shreds
        let last_shreds_bytes = (2 * DATA_SHREDS).next_multiple_of(shred_bytes);
        let boundary = payload.len() - (last_shreds_bytes - padding_bytes);
        let mut last_shreds = Vec::with_capacity(last_shreds_bytes);
        last_shreds.extend_from_slice(&payload[boundary..]);
        last_shreds.push(0x80);
        last_shreds.resize(last_shreds_bytes, 0);

        // chunk data
        let mut data = Vec::with_capacity(DATA_SHREDS);
        payload[..boundary]
            .chunks(shred_bytes)
            .chain(last_shreds.chunks(shred_bytes))
            .for_each(|chunk| {
                self.encoder
                    .add_original_shard(chunk)
                    .expect("adding correct number of chunks of correct size");
                data.push(chunk.to_vec());
            });

        // perform coding
        let result = self
            .encoder
            .encode()
            .expect("we just added enough data shreds");
        let coding = result.recovery_iter().map(<[u8]>::to_vec).collect();

        Ok(RawShreds { data, coding })
    }

    /// Reconstructs the raw data and all shreds from the given shreds.
    ///
    /// Returns both the payload (with padding removed) and the complete [`RawShreds`]
    /// (data and coding, with padding intact). The returned [`RawShreds`] can be used
    /// to rebuild the full Merkle tree without re-encoding from the payload.
    ///
    /// # Errors
    ///
    /// If fewer than [`DATA_SHREDS`] elements in `shreds` are `Some()` then returns [`ReedSolomonDeshredError::NotEnoughShreds`].
    /// If the restored payload is larger than [`MAX_DATA_PER_SLICE_AFTER_PADDING`] then returns [`ReedSolomonDeshredError::TooMuchData`].
    pub(super) fn deshred(
        &mut self,
        shreds: ReceivedShreds<'_>,
    ) -> Result<(Vec<u8>, RawShreds), ReedSolomonDeshredError> {
        let raw_shreds = self.reconstruct_data(shreds)?;

        // concatenate the data shreds back into the padded payload
        let mut payload = Vec::with_capacity(MAX_DATA_PER_SLICE_AFTER_PADDING);
        for shred in &raw_shreds.data {
            if payload.len() + shred.len() > MAX_DATA_PER_SLICE_AFTER_PADDING {
                return Err(ReedSolomonDeshredError::TooMuchData);
            }
            payload.extend_from_slice(shred);
        }

        // remove padding from payload
        let padding_bytes = payload.iter().rev().take_while(|b| **b == 0).count() + 1;
        // an all-zero payload has no 0x80 marker at all
        if padding_bytes > payload.len() || payload[payload.len() - padding_bytes] != 0x80 {
            return Err(ReedSolomonDeshredError::InvalidPadding);
        }
        payload.truncate(payload.len().saturating_sub(padding_bytes));

        Ok((payload, raw_shreds))
    }

    /// Reconstructs all [`DATA_SHREDS`] data shreds (and re-encodes coding).
    ///
    /// Unlike [`Self::deshred`], this does not concatenate or unpad the payload;
    /// it only recovers the raw shreds. This lets shredders that impose their own
    /// payload layout (e.g. all-or-nothing transforms) parse the shreds directly.
    ///
    /// # Errors
    ///
    /// Returns [`ReedSolomonDeshredError::NotEnoughShreds`] if fewer than
    /// [`DATA_SHREDS`] elements of `shreds` are present.
    pub(super) fn reconstruct_data(
        &mut self,
        shreds: ReceivedShreds<'_>,
    ) -> Result<RawShreds, ReedSolomonDeshredError> {
        if shreds.data.len() + shreds.coding.len() < DATA_SHREDS {
            return Err(ReedSolomonDeshredError::NotEnoughShreds);
        }

        // configure decoder for shred size
        let shred_bytes = shreds.shred_bytes;
        self.decoder
            .reset(DATA_SHREDS, self.num_coding, shred_bytes)
            .expect("size of validated shred should be supported");

        let data_refs = shreds.data;
        for &(i, d) in &data_refs {
            self.decoder
                .add_original_shard(i, d)
                .expect("validated shred should have correct index and size");
        }
        for (i, c) in shreds.coding {
            self.decoder
                .add_recovery_shard(i, c)
                .expect("validated shred should have correct index and size");
        }
        let restored = self.decoder.decode().expect("just added enough shreds");

        // build complete data shreds array (originals + restored)
        let mut received = [None; DATA_SHREDS];
        for (i, d) in data_refs {
            received[i] = Some(d);
        }
        let mut raw_data_shreds = Vec::with_capacity(DATA_SHREDS);
        for (i, existing) in received.iter().enumerate() {
            let shred_data = match existing {
                Some(d) => d,
                None => restored
                    .restored_original(i)
                    .expect("all non-existing data shreds are restored"),
            };
            raw_data_shreds.push(shred_data.to_vec());
        }
        drop(restored);

        Ok(self.encode_coding_from_data(raw_data_shreds))
    }

    /// Produces coding shreds from pre-split data shreds.
    ///
    /// Takes ownership of `data_shreds` and moves it into the returned
    /// [`RawShreds`], so no data shred is copied here.
    pub(super) fn encode_coding_from_data(&mut self, data_shreds: Vec<Vec<u8>>) -> RawShreds {
        assert_eq!(data_shreds.len(), DATA_SHREDS);
        let shred_bytes = data_shreds[0].len();
        self.encoder
            .reset(DATA_SHREDS, self.num_coding, shred_bytes)
            .expect("shred size should be supported");
        for shred in &data_shreds {
            self.encoder
                .add_original_shard(shred)
                .expect("adding correct number of shreds of correct size");
        }
        let result = self
            .encoder
            .encode()
            .expect("we just added enough data shreds");
        let coding = result.recovery_iter().map(<[u8]>::to_vec).collect();
        RawShreds {
            data: data_shreds,
            coding,
        }
    }
}

#[cfg(test)]
mod tests {
    use static_assertions::const_assert;

    use super::*;
    use crate::Slot;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::validated_shreds::ValidatedShreds;
    use crate::shredder::{ValidatedShred, data_and_coding_to_output_shreds};
    use crate::types::slice::create_slice_with_invalid_txs;
    use crate::types::{SliceHeader, SliceIndex};

    #[test]
    fn restore_full() {
        let (header, payload) = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE).deconstruct();
        shred_deshred_restore(header, payload.into());
    }

    #[test]
    fn restore_tiny() {
        let (header, payload) = create_slice_with_invalid_txs(DATA_SHREDS - 1).deconstruct();
        shred_deshred_restore(header, payload.into());
    }

    #[test]
    fn restore_empty() {
        let header = SliceHeader {
            slot: Slot::new(0),
            slice_index: SliceIndex::first(),
            is_last: true,
        };
        let payload = Vec::new();
        shred_deshred_restore(header, payload);
    }

    #[test]
    fn restore_various() {
        const_assert!(MAX_DATA_PER_SLICE >= 2 * DATA_SHREDS);
        let slice_bytes = MAX_DATA_PER_SLICE / 2;
        for offset in 0..DATA_SHREDS {
            let (header, payload) =
                create_slice_with_invalid_txs(slice_bytes + offset).deconstruct();
            shred_deshred_restore(header, payload.into());
        }
    }

    #[test]
    fn shred_too_much_data() {
        let payload = vec![0; MAX_DATA_PER_SLICE + 1];
        let mut rs = ReedSolomonCoder::new(TOTAL_SHREDS - DATA_SHREDS);
        let res = rs.shred(&payload);
        assert!(res.is_err());
        assert_eq!(res.err().unwrap(), ReedSolomonShredError::TooMuchData);
    }

    #[test]
    fn deshred_not_enough_shreds() {
        let (header, payload) = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE).deconstruct();
        let mut rs = ReedSolomonCoder::new(TOTAL_SHREDS - DATA_SHREDS);
        let shreds = rs.shred(&payload.to_bytes()).unwrap();
        let sk = SecretKey::new(&mut rand::rng());
        let mut shreds = data_and_coding_to_output_shreds(header, shreds, &sk).map(Some);
        for shred in shreds.iter_mut().skip(DATA_SHREDS - 1) {
            *shred = None;
        }
        let validated_shreds =
            ValidatedShreds::try_new(&shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS).unwrap();
        let res = rs.deshred(validated_shreds.received());
        assert!(res.is_err());
        assert_eq!(res.err().unwrap(), ReedSolomonDeshredError::NotEnoughShreds);
    }

    fn shred_deshred_restore(header: SliceHeader, payload: Vec<u8>) {
        let mut rs = ReedSolomonCoder::new(TOTAL_SHREDS - DATA_SHREDS);
        let shreds = rs.shred(&payload).unwrap();
        let shreds = take_and_map_enough_shreds(header, shreds);
        let validated_shreds =
            ValidatedShreds::try_new(&shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS).unwrap();
        let (restored, _raw_shreds) = rs.deshred(validated_shreds.received()).unwrap();
        assert_eq!(restored, payload);
    }

    fn take_and_map_enough_shreds(
        header: SliceHeader,
        shreds: RawShreds,
    ) -> [Option<ValidatedShred>; TOTAL_SHREDS] {
        let sk = SecretKey::new(&mut rand::rng());
        let mut shreds = data_and_coding_to_output_shreds(header, shreds, &sk).map(Some);
        for shred in shreds.iter_mut().skip(TOTAL_SHREDS - DATA_SHREDS) {
            *shred = None;
        }
        shreds
    }
}
