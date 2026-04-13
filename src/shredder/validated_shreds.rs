// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatedShreds`] type.

use super::{ShredPayloadType, TOTAL_SHREDS, ValidatedShred};

/// Validated shreds array type.
///
/// Using strong type to enforce certain constraints:
/// - Shreds are in the correct order.
/// - Shred indices match expected shred type.
/// - Shreds are all the same size.
#[derive(Clone, Copy)]
pub struct ValidatedShreds<'a> {
    shreds: &'a [Option<ValidatedShred>; TOTAL_SHREDS],
    data_shreds: usize,
}

impl<'a> ValidatedShreds<'a> {
    /// Creates a new [`ValidatedShreds`].
    ///
    /// Returns `None` if the input array contains:
    /// - a shred with the wrong type for the index, or
    /// - shreds of different sizes.
    ///
    /// # Panics
    ///
    /// - Panics if the input array contains a shred at the wrong index.
    /// - Panics if `shreds` contains no shreds.
    pub(super) fn try_new(
        shreds: &'a [Option<ValidatedShred>; TOTAL_SHREDS],
        data_shreds: usize,
        coding_shreds: usize,
    ) -> Option<Self> {
        assert_eq!(data_shreds + coding_shreds, TOTAL_SHREDS);

        // check all shred sizes match
        let any_shred = shreds.iter().flatten().next().unwrap();
        let shred_size = any_shred.payload().data.len();
        for s in shreds.iter().flatten() {
            if s.payload().data.len() != shred_size {
                return None;
            }
        }

        // check index shred index matches expected shred type
        for (i, shred) in shreds.iter().enumerate() {
            let Some(shred) = shred else {
                continue;
            };
            assert_eq!(*shred.payload().shred_index, i);
            if i < data_shreds && !shred.is_data() || i >= data_shreds && !shred.is_coding() {
                return None;
            }
        }

        Some(Self {
            shreds,
            data_shreds,
        })
    }

    /// Returns the number of present (non-`None`) shreds.
    pub(super) fn shred_count(self) -> usize {
        self.shreds.iter().filter(|s| s.is_some()).count()
    }

    /// Returns a reference to any shred in this set.
    pub(super) fn any_shred(self) -> &'a ValidatedShred {
        // this unwrap is safe because constructor ensures at least one shred
        self.shreds.iter().flatten().next().unwrap()
    }

    /// Returns `(index, payload)` pairs for all present data shreds.
    pub(super) fn data_shred_payloads(self) -> Vec<(usize, &'a [u8])> {
        self.shreds
            .iter()
            .take(self.data_shreds)
            .filter_map(|s| {
                s.as_ref().map(|s| match &s.payload_type {
                    ShredPayloadType::Data(d) => (*d.shred_index, d.data.as_slice()),
                    // SAFETY: ValidatedShreds ensures all shreds up to data_shreds are data
                    ShredPayloadType::Coding(_) => panic!("should be a data shred"),
                })
            })
            .collect()
    }

    /// Returns `(adjusted_index, payload)` pairs for all present coding shreds.
    ///
    /// The index is adjusted to be relative to the start of the coding section.
    pub(super) fn coding_shred_payloads(self) -> impl Iterator<Item = (usize, &'a [u8])> {
        let data_shreds = self.data_shreds;
        self.shreds.iter().skip(data_shreds).filter_map(move |s| {
            s.as_ref().map(|s| match &s.payload_type {
                ShredPayloadType::Coding(c) => (*c.shred_index - data_shreds, c.data.as_slice()),
                // SAFETY: ValidatedShreds ensures all shreds after data_shreds are coding
                ShredPayloadType::Data(_) => panic!("should be a coding shred"),
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use rand::rng;

    use super::*;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{DATA_SHREDS, MAX_DATA_PER_SLICE, RegularShredder, Shredder};
    use crate::types::slice::create_slice_with_invalid_txs;

    #[test]
    fn validity_tests() {
        let mut shredder = RegularShredder::default();
        let sk = SecretKey::new(&mut rng());
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);

        // there are data shreds in coding shred positions in the array
        let shreds = shredder.shred(slice.clone(), &sk).unwrap().map(Some);
        assert!(ValidatedShreds::try_new(&shreds, 1, TOTAL_SHREDS - 1).is_none());

        // there are coding shreds in data shred positions in the array
        let shreds = shredder.shred(slice.clone(), &sk).unwrap().map(Some);
        assert!(ValidatedShreds::try_new(&shreds, TOTAL_SHREDS - 1, 1).is_none());

        // mixing shreds of different sizes
        let small_slice = create_slice_with_invalid_txs(100);
        let small_shreds = shredder.shred(small_slice, &sk).unwrap().map(Some);
        let mut shreds = shreds;
        shreds[0] = small_shreds[0].clone();
        assert!(
            ValidatedShreds::try_new(&shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS).is_none()
        );
    }
}
