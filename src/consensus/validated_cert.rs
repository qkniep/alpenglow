// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Defines the [`ValidatedCert`] type.

use thiserror::Error;

use super::{Cert, EpochInfo};
use crate::Slot;

/// Different errors returned from [`ValidatedCert::try_new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum CertVerifyError {
    /// The combined stake of the signers does not meet the required threshold.
    #[error("stake threshold not met")]
    ThresholdNotMet,
    /// The aggregate signature verification failed.
    #[error("invalid signature on the cert")]
    InvalidSignature,
}

/// A verified wrapper around a [`Cert`].
///
/// It uses the new type pattern to encode verification in the type system.
/// The encapsulated [`Cert`] has passed all signature-level checks:
/// - the combined signer stake meets the certificate's quorum threshold
///   (this also sanity-checks the signer bitmask), and
/// - the aggregate signature is valid under the signers' voting keys.
///
/// This mirrors [`ValidatedShred`] on the shred path: the expensive BLS
/// verification is performed once, up front, so that downstream consumers
/// (i.e. the [`Pool`]) can merge the certificate into per-slot state without
/// holding a lock during signature verification.
///
/// [`ValidatedShred`]: crate::shredder::ValidatedShred
/// [`Pool`]: crate::consensus::Pool
#[derive(Clone, Debug)]
pub struct ValidatedCert {
    cert: Cert,
}

impl ValidatedCert {
    /// Verifies the stake threshold and aggregate signature of `cert`.
    ///
    /// Returns a [`ValidatedCert`] on success.
    ///
    /// # Errors
    ///
    /// Returns [`CertVerifyError`] if the [`Cert`] does not pass all verification checks.
    #[hotpath::measure]
    pub fn try_new(cert: Cert, epoch_info: &EpochInfo) -> Result<Self, CertVerifyError> {
        // verify stake threshold (also sanity-checks the signer bitmask) & signature
        if !cert.check_threshold(epoch_info) {
            return Err(CertVerifyError::ThresholdNotMet);
        }
        if !cert.check_sig(epoch_info.validators()) {
            return Err(CertVerifyError::InvalidSignature);
        }

        Ok(Self { cert })
    }

    /// Returns the slot this certificate is for.
    #[must_use]
    pub const fn slot(&self) -> Slot {
        self.cert.slot()
    }

    /// Consumes `self`, returning the inner [`Cert`].
    #[must_use]
    pub fn into_cert(self) -> Cert {
        self.cert
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ValidatorIndex;
    use crate::consensus::cert::NotarCert;
    use crate::consensus::vote::NotarVote;
    use crate::crypto::Hash;
    use crate::crypto::merkle::BlockHash;
    use crate::test_utils::generate_validators;

    #[test]
    fn valid_cert() {
        let (sks, epoch_info) = generate_validators(11);
        let hash: BlockHash = Hash::random_for_test().into();
        // 7/11 meets the 60% notarization threshold
        let votes: Vec<NotarVote> = (0..7)
            .map(|v| {
                NotarVote::new(
                    Slot::new(1),
                    hash.clone(),
                    &sks[v],
                    ValidatorIndex::new(v as u64),
                )
            })
            .collect();
        let cert = Cert::Notar(NotarCert::try_new(&votes, epoch_info.validators()).unwrap());
        let validated = ValidatedCert::try_new(cert.clone(), &epoch_info).unwrap();
        assert_eq!(validated.into_cert(), cert);
    }

    #[test]
    fn threshold_not_met() {
        let (sks, epoch_info) = generate_validators(11);
        let hash: BlockHash = Hash::random_for_test().into();
        // 6/11 does NOT meet the 60% notarization threshold
        let votes: Vec<NotarVote> = (0..6)
            .map(|v| {
                NotarVote::new(
                    Slot::new(1),
                    hash.clone(),
                    &sks[v],
                    ValidatorIndex::new(v as u64),
                )
            })
            .collect();
        let cert = Cert::Notar(NotarCert::try_new(&votes, epoch_info.validators()).unwrap());
        assert!(matches!(
            ValidatedCert::try_new(cert, &epoch_info),
            Err(CertVerifyError::ThresholdNotMet)
        ));
    }

    #[test]
    fn invalid_signature() {
        let (sks, epoch_info) = generate_validators(11);
        let hash: BlockHash = Hash::random_for_test().into();
        // validator 0 signs with the wrong key, so the aggregate signature is invalid
        let mut votes: Vec<NotarVote> = (1..7)
            .map(|v| {
                NotarVote::new(
                    Slot::new(1),
                    hash.clone(),
                    &sks[v],
                    ValidatorIndex::new(v as u64),
                )
            })
            .collect();
        votes.push(NotarVote::new(
            Slot::new(1),
            hash.clone(),
            &sks[1],
            ValidatorIndex::new(0),
        ));
        let cert = Cert::Notar(NotarCert::try_new(&votes, epoch_info.validators()).unwrap());
        assert!(matches!(
            ValidatedCert::try_new(cert, &epoch_info),
            Err(CertVerifyError::InvalidSignature)
        ));
    }
}
