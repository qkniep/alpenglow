// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implements Reed-Solomon shreding and deshreding.

use reed_solomon_simd as rs;
use thiserror::Error;

use super::{
    DATA_SHREDS, MAX_DATA_PER_SLICE, MAX_DATA_PER_SLICE_AFTER_PADDING, ShredPayloadType,
    TOTAL_SHREDS,
};
use crate::shredder::ValidatedShred;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(super) enum ReedSolomonShredError {
    #[error("too much data for slice")]
    TooMuchData,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub(super) enum ReedSolomonDeshredError {
    #[error("not enough shreds to reconstruct")]
    NotEnoughShreds,
    #[error("too much data for slice")]
    TooMuchData,
}

/// The data and coding shreds returned from [`reed_solomon_shred()`] on success.
pub(super) struct RawShreds {
    /// A list of data shreds.
    pub(super) data: Vec<Vec<u8>>,
    /// A list of coding shreds.
    pub(super) coding: Vec<Vec<u8>>,
}

/// Splits the given slice into `num_data` data shreds, then generates `num_coding` additional Reed-Solomon coding shreds.
pub(super) fn reed_solomon_shred(
    mut payload: Vec<u8>,
    num_coding: usize,
) -> Result<RawShreds, ReedSolomonShredError> {
    assert!(num_coding <= TOTAL_SHREDS);
    if payload.len() > MAX_DATA_PER_SLICE {
        return Err(ReedSolomonShredError::TooMuchData);
    }

    // add padding
    // TODO: use a padding scheme that can support larger slices
    let padding_bytes = u8::try_from(2 * DATA_SHREDS - payload.len() % (2 * DATA_SHREDS))
        .expect("cannot fit number of padding bytes in u8");
    payload.resize(payload.len() + padding_bytes as usize, padding_bytes);
    assert!(payload.len() <= MAX_DATA_PER_SLICE_AFTER_PADDING);

    let shred_bytes = payload.len().div_ceil(DATA_SHREDS);
    let data = payload.chunks(shred_bytes).map(|c| c.to_vec()).collect();
    let coding = rs::encode(DATA_SHREDS, num_coding, &data).unwrap();
    Ok(RawShreds { data, coding })
}

/// Reconstructs the raw data from the given shreds.
///
/// Errors
///
/// If fewer than [`DATA_SHREDS`] elements in `shreds` are `Some()` then returns `Err(ReedSolomonDeshredError::NotEnoughShreds)`.
/// If the restored payload is larger than [`MAX_DATA_PER_SLICE_AFTER_PADDING`] then returns `Err(ReedSolomonDeshredError::TooMuchData)`.
pub(super) fn reed_solomon_deshred(
    shreds: &[Option<ValidatedShred>; TOTAL_SHREDS],
    num_coding: usize,
) -> Result<Vec<u8>, ReedSolomonDeshredError> {
    assert!(num_coding <= TOTAL_SHREDS);
    let shreds_cnt = shreds.iter().filter(|s| s.is_some()).count();
    if shreds_cnt < DATA_SHREDS {
        return Err(ReedSolomonDeshredError::NotEnoughShreds);
    }

    let coding_offset = TOTAL_SHREDS - num_coding;

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

    let restored = rs::decode(DATA_SHREDS, num_coding, data.clone(), coding).unwrap();

    let mut data_shreds = vec![None; DATA_SHREDS];
    for (i, d) in data {
        data_shreds[i] = Some(d);
    }

    // restore data from data shreds (from input and restored)
    let mut restored_payload = Vec::with_capacity(MAX_DATA_PER_SLICE_AFTER_PADDING);
    for (i, d) in data_shreds.into_iter().enumerate() {
        let shred_data = match d {
            Some(data_ref) => data_ref.as_ref(),
            None => restored.get(&i).unwrap(),
        };
        if restored_payload.len() + shred_data.len() > MAX_DATA_PER_SLICE_AFTER_PADDING {
            return Err(ReedSolomonDeshredError::TooMuchData);
        }
        restored_payload.extend_from_slice(shred_data);
    }

    // remove padding
    let padding_bytes = restored_payload[restored_payload.len() - 1] as usize;
    restored_payload.truncate(restored_payload.len().saturating_sub(padding_bytes));

    Ok(restored_payload)
}

#[cfg(test)]
mod tests {
    use static_assertions::const_assert;

    use super::*;
    use crate::Slot;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::data_and_coding_to_output_shreds;
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
        let res = reed_solomon_shred(payload, TOTAL_SHREDS - DATA_SHREDS);
        assert!(res.is_err());
        assert_eq!(res.err().unwrap(), ReedSolomonShredError::TooMuchData);
    }

    #[test]
    fn deshred_not_enough_shreds() {
        let (header, payload) = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE).deconstruct();
        let shreds =
            reed_solomon_shred(payload.clone().into(), TOTAL_SHREDS - DATA_SHREDS).unwrap();
        let sk = SecretKey::new(&mut rand::rng());
        let mut shreds = data_and_coding_to_output_shreds(header, shreds, &sk).map(Some);
        for shred in shreds.iter_mut().skip(DATA_SHREDS - 1) {
            *shred = None;
        }
        let res = reed_solomon_deshred(&shreds, DATA_SHREDS);
        assert!(res.is_err());
        assert_eq!(res.err().unwrap(), ReedSolomonDeshredError::NotEnoughShreds);
    }

    fn shred_deshred_restore(header: SliceHeader, payload: Vec<u8>) {
        let shreds = reed_solomon_shred(payload.clone(), TOTAL_SHREDS - DATA_SHREDS).unwrap();
        let shreds = take_and_map_enough_shreds(header, shreds);
        let restored = reed_solomon_deshred(&shreds, DATA_SHREDS).unwrap();
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
