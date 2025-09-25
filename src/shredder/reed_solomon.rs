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
    #[error("more shreds than expected")]
    TooManyShreds,
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

/// Splits the given slice into `num_data` data shreds, then generates
/// `num_coding` additional Reed-Solomon coding shreds.
pub(super) fn reed_solomon_shred(
    mut payload: Vec<u8>,
    num_data: usize,
    num_coding: usize,
) -> Result<RawShreds, ReedSolomonShredError> {
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
    let coding = rs::encode(num_data, num_coding, &data).unwrap();
    Ok(RawShreds { data, coding })
}

/// Reconstructs the raw data from the given shreds.
pub(super) fn reed_solomon_deshred(
    shreds: &[ValidatedShred],
    num_data: usize,
    num_coding: usize,
    coding_offset: usize,
) -> Result<Vec<u8>, ReedSolomonDeshredError> {
    assert!(coding_offset <= DATA_SHREDS);
    if shreds.len() < DATA_SHREDS {
        return Err(ReedSolomonDeshredError::NotEnoughShreds);
    }
    if shreds.len() > TOTAL_SHREDS {
        return Err(ReedSolomonDeshredError::TooManyShreds);
    }

    // filter to split data and coding shreds
    let data = shreds.iter().filter_map(|s| match &s.payload_type {
        ShredPayloadType::Data(d) => Some((d.index_in_slice, &d.data)),
        ShredPayloadType::Coding(_) => None,
    });
    let coding = shreds.iter().filter_map(|s| match &s.payload_type {
        ShredPayloadType::Coding(c) => Some((c.index_in_slice - coding_offset, &c.data)),
        ShredPayloadType::Data(_) => None,
    });

    let restored = rs::decode(num_data, num_coding, data.clone(), coding).unwrap();

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
        let res = reed_solomon_shred(payload, DATA_SHREDS, DATA_SHREDS);
        assert!(res.is_err());
        assert_eq!(res.err().unwrap(), ReedSolomonShredError::TooMuchData);
    }

    #[test]
    fn deshred_too_many_shreds() {
        const CODING_SHREDS: usize = TOTAL_SHREDS - DATA_SHREDS + 1;
        let (header, payload) = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE).deconstruct();
        let shreds =
            reed_solomon_shred(payload.clone().into(), DATA_SHREDS, CODING_SHREDS).unwrap();
        let sk = SecretKey::new(&mut rand::rng());
        let shreds = data_and_coding_to_output_shreds(header, shreds, &sk);
        let res = reed_solomon_deshred(&shreds, DATA_SHREDS, DATA_SHREDS, DATA_SHREDS);
        assert!(res.is_err());
        assert_eq!(res.err().unwrap(), ReedSolomonDeshredError::TooManyShreds);
    }

    #[test]
    fn deshred_not_enough_shreds() {
        let (header, payload) = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE).deconstruct();
        let shreds = reed_solomon_shred(payload.clone().into(), DATA_SHREDS, DATA_SHREDS).unwrap();
        let sk = SecretKey::new(&mut rand::rng());
        let mut shreds = data_and_coding_to_output_shreds(header, shreds, &sk);
        shreds.truncate(DATA_SHREDS - 1);
        let res = reed_solomon_deshred(&shreds, DATA_SHREDS, DATA_SHREDS, DATA_SHREDS);
        assert!(res.is_err());
        assert_eq!(res.err().unwrap(), ReedSolomonDeshredError::NotEnoughShreds);
    }

    fn shred_deshred_restore(header: SliceHeader, payload: Vec<u8>) {
        let shreds = reed_solomon_shred(payload.clone(), DATA_SHREDS, DATA_SHREDS).unwrap();
        let shreds = take_and_map_enough_shreds(header, shreds);
        let restored =
            reed_solomon_deshred(&shreds, DATA_SHREDS, DATA_SHREDS, DATA_SHREDS).unwrap();
        assert_eq!(restored, payload);
    }

    fn take_and_map_enough_shreds(header: SliceHeader, shreds: RawShreds) -> Vec<ValidatedShred> {
        let sk = SecretKey::new(&mut rand::rng());
        let shreds = data_and_coding_to_output_shreds(header, shreds, &sk);
        // reverse order to get coding shreds, not just data shreds
        shreds.into_iter().rev().take(DATA_SHREDS).collect()
    }
}
