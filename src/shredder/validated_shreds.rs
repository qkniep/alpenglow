use crate::shredder::{ShredPayloadType, TOTAL_SHREDS, ValidatedShred};

pub struct ValidatedShreds<'a>(&'a [Option<ValidatedShred>; TOTAL_SHREDS]);

impl<'a> ValidatedShreds<'a> {
    pub(super) fn try_new(
        shreds: &'a [Option<ValidatedShred>; TOTAL_SHREDS],
        data_shreds: usize,
        coding_shreds: usize,
    ) -> Option<Self> {
        if data_shreds + coding_shreds != TOTAL_SHREDS {
            return None;
        }

        for (i, shred) in shreds.iter().enumerate() {
            if let Some(shred) = shred
                && *shred.payload().shred_index != i
            {
                return None;
            }
        }
        for shred in shreds.iter().take(data_shreds) {
            if let Some(shred) = shred
                && !matches!(&shred.payload_type, ShredPayloadType::Data(_p))
            {
                return None;
            }
        }
        for shred in shreds.iter().skip(data_shreds) {
            if let Some(shred) = shred
                && !matches!(&shred.payload_type, ShredPayloadType::Coding(_p))
            {
                return None;
            }
        }
        Some(Self(shreds))
    }

    pub(super) fn into_shreds(self) -> &'a [Option<ValidatedShred>; TOTAL_SHREDS] {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use rand::rng;

    use crate::{
        crypto::signature::SecretKey,
        shredder::{DATA_SHREDS, MAX_DATA_PER_SLICE, RegularShredder, ShredIndex, Shredder},
        types::slice::create_slice_with_invalid_txs,
    };

    use super::*;

    #[test]
    fn validity_tests() {
        let sk = SecretKey::new(&mut rng());
        let slice = create_slice_with_invalid_txs(MAX_DATA_PER_SLICE);

        // number of data and coding shreds do not match up
        let shreds = RegularShredder::shred(slice.clone(), &sk)
            .unwrap()
            .map(Some);
        assert!(ValidatedShreds::try_new(&shreds, 10, 10).is_none());

        // the shred index is invalid
        let mut shreds = RegularShredder::shred(slice.clone(), &sk).unwrap();
        shreds[1].payload_mut().shred_index = ShredIndex::new(0).unwrap();
        let shreds = shreds.map(Some);
        assert!(
            ValidatedShreds::try_new(&shreds, DATA_SHREDS, TOTAL_SHREDS - DATA_SHREDS).is_none()
        );

        // there are more data shreds in the array
        let shreds = RegularShredder::shred(slice.clone(), &sk)
            .unwrap()
            .map(Some);
        assert!(ValidatedShreds::try_new(&shreds, 1, TOTAL_SHREDS - 1).is_none());

        // there are fewer data shreds in the array
        let shreds = RegularShredder::shred(slice.clone(), &sk)
            .unwrap()
            .map(Some);
        assert!(ValidatedShreds::try_new(&shreds, TOTAL_SHREDS - 1, 1).is_none());
    }
}
