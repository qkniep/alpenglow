// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Implements reed solomon shreding and deshreding

use reed_solomon_simd as rs;

use crate::Slot;

use super::{
    CodingShred, DATA_SHREDS, DataShred, MAX_DATA_PER_SLICE, Shred, ShredPayload, ShredPayloadType,
    Slice, TOTAL_SHREDS,
};

pub(super) enum ReedSolomonShredError {
    TooMuchData,
}

pub(super) enum ReedSolomonDeshredError {
    NotEnoughShreds,
    TooManyShreds,
    TooMuchData,
}

/// Splits the given slice into `num_data` data shreds, then generates
/// `num_coding` additional Reed-Solomon coding shreds.
pub(super) fn reed_solomon_shred(
    slice: &Slice,
    num_data: usize,
    num_coding: usize,
) -> Result<(Vec<DataShred>, Vec<CodingShred>), ReedSolomonShredError> {
    let Slice {
        slot,
        slice_index,
        is_last,
        merkle_root: _,
        data,
    } = slice;
    reed_solomon_shred_raw(*slot, *slice_index, *is_last, data, num_data, num_coding)
}

/// Splits the given data into `num_data` data shreds, then generates
/// `num_coding` additional Reed-Solomon coding shreds.
/// The slice-specific fields `slot`, `slice_index`, and `is_last` are included
/// in every `DataShred` or `CodingShred`.
pub(super) fn reed_solomon_shred_raw(
    slot: Slot,
    slice_index: usize,
    is_last_slice: bool,
    data: &[u8],
    num_data: usize,
    num_coding: usize,
) -> Result<(Vec<DataShred>, Vec<CodingShred>), ReedSolomonShredError> {
    if data.len() > MAX_DATA_PER_SLICE {
        return Err(ReedSolomonShredError::TooMuchData);
    }

    let shred_bytes = data.len() / DATA_SHREDS;
    let data_parts = data.chunks(shred_bytes);
    let coding_parts = rs::encode(num_data, num_coding, data_parts.clone()).unwrap();

    // map raw data/coding parts to `DataShred` and `CodingShred`
    let payload_from_index_and_data = |index: usize, data: Vec<u8>| ShredPayload {
        slot,
        slice_index,
        index_in_slice: index,
        is_last_slice,
        data: data.into(),
    };
    let data_shreds = data_parts
        .into_iter()
        .enumerate()
        .map(|(i, p)| DataShred(payload_from_index_and_data(i, p.to_vec())))
        .collect();
    let coding_shreds = coding_parts
        .into_iter()
        .enumerate()
        .map(|(i, p)| CodingShred(payload_from_index_and_data(i, p)))
        .collect();

    Ok((data_shreds, coding_shreds))
}

/// Reconstructs the raw data from the given shreds.
pub(super) fn reed_solomon_deshred(
    shreds: &[Shred],
    num_data: usize,
    num_coding: usize,
) -> Result<Vec<u8>, ReedSolomonDeshredError> {
    if shreds.len() < DATA_SHREDS {
        return Err(ReedSolomonDeshredError::NotEnoughShreds);
    } else if shreds.len() > TOTAL_SHREDS {
        return Err(ReedSolomonDeshredError::TooManyShreds);
    }

    // filter to split data and coding shreds
    let data = shreds.iter().filter_map(|s| match &s.payload_type {
        ShredPayloadType::Data(d) => Some((d.index_in_slice, &d.data)),
        ShredPayloadType::Coding(_) => None,
    });
    let coding = shreds.iter().filter_map(|s| match &s.payload_type {
        ShredPayloadType::Coding(c) => Some((c.index_in_slice, &c.data)),
        ShredPayloadType::Data(_) => None,
    });

    let restored = rs::decode(num_data, num_coding, data.clone(), coding).unwrap();

    let mut data_shreds = vec![None; DATA_SHREDS];
    for (i, d) in data {
        data_shreds[i] = Some(d);
    }

    // restore data from data shreds (from input and restored)
    let mut restored_payload = Vec::with_capacity(MAX_DATA_PER_SLICE);
    for (i, d) in data_shreds.into_iter().enumerate() {
        let shred_data = match d {
            Some(data_ref) => data_ref.as_ref(),
            None => restored.get(&i).unwrap(),
        };
        if restored_payload.len() + shred_data.len() > MAX_DATA_PER_SLICE {
            return Err(ReedSolomonDeshredError::TooMuchData);
        }
        restored_payload.extend_from_slice(shred_data);
    }

    Ok(restored_payload)
}
