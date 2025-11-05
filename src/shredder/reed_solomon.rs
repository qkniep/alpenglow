// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implements Reed-Solomon shreding and deshreding.
//!
//! This is a low-level module that is used in various shredder implementations.
//! It is mostly a wrapper around the [`reed_solomon_simd`] crate.

use reed_solomon_simd::{ReedSolomonDecoder, ReedSolomonEncoder};
use static_assertions::const_assert;
use thiserror::Error;

use super::{
    DATA_SHREDS, MAX_DATA_PER_SLICE, MAX_DATA_PER_SLICE_AFTER_PADDING, ShredPayloadType,
    TOTAL_SHREDS,
};
use crate::shredder::MAX_DATA_PER_SHRED;
use crate::shredder::validated_shreds::ValidatedShreds;

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
                    .expect("adding correct number of chunks of currect size");
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

    /// Reconstructs the raw data from the given shreds.
    ///
    /// Removes the padding before returning the data.
    /// See [`ReedSolomonCoder::shred`] for details on the padding scheme.
    ///
    /// Errors
    ///
    /// If fewer than [`DATA_SHREDS`] elements in `shreds` are `Some()` then returns [`ReedSolomonDeshredError::NotEnoughShreds`].
    /// If the restored payload is larger than [`MAX_DATA_PER_SLICE_AFTER_PADDING`] then returns [`ReedSolomonDeshredError::TooMuchData`].
    pub(super) fn deshred(
        &mut self,
        shreds: ValidatedShreds,
    ) -> Result<Vec<u8>, ReedSolomonDeshredError> {
        let shreds = shreds.to_shreds();
        let shreds_cnt = shreds.iter().filter(|s| s.is_some()).count();
        if shreds_cnt < DATA_SHREDS {
            return Err(ReedSolomonDeshredError::NotEnoughShreds);
        }

        // configure decoder for shred size
        let shred_bytes = shreds.iter().flatten().next().unwrap().payload().data.len();
        self.decoder
            .reset(DATA_SHREDS, self.num_coding, shred_bytes)
            .expect("size of validated shred should be supported");

        let coding_offset = TOTAL_SHREDS - self.num_coding;

        // filter to split data and coding shreds
        let data = shreds.iter().take(coding_offset).filter_map(|s| {
            s.as_ref().map(|s| match &s.payload_type {
                ShredPayloadType::Data(d) => (*d.shred_index, &d.data),
                ShredPayloadType::Coding(_) => panic!("should be a data shred"),
            })
        });

        let coding = shreds.iter().skip(coding_offset).filter_map(|s| {
            s.as_ref().map(|s| match &s.payload_type {
                ShredPayloadType::Coding(c) => (*c.shred_index - coding_offset, &c.data),
                ShredPayloadType::Data(_) => panic!("should be a coding shred"),
            })
        });

        for (i, d) in data.clone() {
            self.decoder
                .add_original_shard(i, d)
                .expect("validated shred should have correct index and size");
        }
        for (i, c) in coding {
            self.decoder
                .add_recovery_shard(i, c)
                .expect("validated shred should have correct index and size");
        }
        let restored = self.decoder.decode().expect("just added enough shreds");

        let mut data_shreds = vec![None; DATA_SHREDS];
        for (i, d) in data {
            data_shreds[i] = Some(d);
        }

        // restore data from data shreds (from input and restored)
        let mut restored_payload = Vec::with_capacity(MAX_DATA_PER_SLICE_AFTER_PADDING);
        for (i, d) in data_shreds.into_iter().enumerate() {
            let shred_data = match d {
                Some(data_ref) => data_ref,
                None => restored
                    .restored_original(i)
                    .expect("all non-existing data shreds are restored"),
            };
            if restored_payload.len() + shred_data.len() > MAX_DATA_PER_SLICE_AFTER_PADDING {
                return Err(ReedSolomonDeshredError::TooMuchData);
            }
            restored_payload.extend_from_slice(shred_data);
        }

        // remove padding
        let padding_bytes = restored_payload
            .iter()
            .rev()
            .take_while(|b| **b == 0)
            .count()
            + 1;
        if restored_payload[restored_payload.len() - padding_bytes] != 0x80 {
            return Err(ReedSolomonDeshredError::InvalidPadding);
        }
        restored_payload.truncate(restored_payload.len().saturating_sub(padding_bytes));

        Ok(restored_payload)
    }
}

#[cfg(test)]
mod tests {
    use static_assertions::const_assert;

    use super::*;
    use crate::Slot;
    use crate::crypto::signature::SecretKey;
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
        let res = rs.deshred(validated_shreds);
        assert!(res.is_err());
        assert_eq!(res.err().unwrap(), ReedSolomonDeshredError::NotEnoughShreds);
    }

    fn shred_deshred_restore(header: SliceHeader, payload: Vec<u8>) {
        let mut rs = ReedSolomonCoder::new(TOTAL_SHREDS - DATA_SHREDS);
        let shreds = rs.shred(&payload).unwrap();
        let shreds = take_and_map_enough_shreds(header, shreds);
        let validated_shreds =
            ValidatedShreds::try_new(&shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS).unwrap();
        let restored = rs.deshred(validated_shreds).unwrap();
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
