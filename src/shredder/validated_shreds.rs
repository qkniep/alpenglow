// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatedShreds`] type.

use crate::shredder::{TOTAL_SHREDS, ValidatedShred};

/// Validated shreds array type.
///
/// Using strong type to enforce certain constraints:
/// - Shreds are in the correct order.
/// - Shred indices match expected shred type.
/// - Shreds are all the same size.
#[derive(Clone, Copy)]
pub struct ValidatedShreds<'a>(&'a [Option<ValidatedShred>; TOTAL_SHREDS]);

impl<'a> ValidatedShreds<'a> {
    /// Creates a new [`ValidatedShreds`].
    ///
    /// # Panics
    ///
    /// Panics if the input array contains a shred at the wrong index.
    pub(super) fn try_new(
        shreds: &'a [Option<ValidatedShred>; TOTAL_SHREDS],
        data_shreds: usize,
        coding_shreds: usize,
    ) -> Option<Self> {
        assert_eq!(data_shreds + coding_shreds, TOTAL_SHREDS);

        // check all shred sizes match
        let some_shred = shreds.iter().flatten().next();
        let shred_size = some_shred.map_or(0, |s| s.payload().data.len());
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

        Some(Self(shreds))
    }

    /// Returns the inner reference to an array of [`ValidatedShred`]s.
    pub(super) fn to_shreds(self) -> &'a [Option<ValidatedShred>; TOTAL_SHREDS] {
        self.0
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
