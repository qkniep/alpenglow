use crate::shredder::{TOTAL_SHREDS, ValidatedShred};

/// Validated shreds array type.
///
/// Using strong type to enforce certain constraints e.g. the shred indexes are valid.
pub struct ValidatedShreds<'a>(&'a [Option<ValidatedShred>; TOTAL_SHREDS]);

impl<'a> ValidatedShreds<'a> {
    /// Creates a new [`ValidatedShreds`].
    pub(super) fn try_new(
        shreds: &'a [Option<ValidatedShred>; TOTAL_SHREDS],
        data_shreds: usize,
        coding_shreds: usize,
    ) -> Option<Self> {
        assert_eq!(data_shreds + coding_shreds, TOTAL_SHREDS);

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

    /// Returns the inner array of [`ValidatedShred`]s.
    pub(super) fn to_shreds(&self) -> &'a [Option<ValidatedShred>; TOTAL_SHREDS] {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use rand::rng;

    use super::*;
    use crate::crypto::signature::SecretKey;
    use crate::shredder::{MAX_DATA_PER_SLICE, RegularShredder, Shredder};
    use crate::types::slice::create_slice_with_invalid_txs;

    #[test]
    fn validity_tests() {
        let sk = SecretKey::new(&mut rng());
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);

        // there are data shreds in coding shred positions in the array
        let shreds = RegularShredder::shred(slice.clone(), &sk)
            .unwrap()
            .map(Some);
        assert!(ValidatedShreds::try_new(&shreds, 1, TOTAL_SHREDS - 1).is_none());

        // there are coding shreds in data shred positions in the array
        let shreds = RegularShredder::shred(slice.clone(), &sk)
            .unwrap()
            .map(Some);
        assert!(ValidatedShreds::try_new(&shreds, TOTAL_SHREDS - 1, 1).is_none());
    }
}
