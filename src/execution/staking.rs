// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Minimal on-chain staking model driving epoch validator-set changes.
//!
//! Validators register, change their stake, update their network addresses, or
//! deregister via [`StakeTx`] transactions. These are encoded inside the opaque
//! [`crate::Transaction`] payload (so the wire format, shredder, and blockstore
//! are untouched) and applied to a [`StakeRegistry`] as part of block execution.
//!
//! The registry is part of the *finalized, agreed* execution state: because it
//! is a pure, deterministic function of the finalized chain prefix, every honest
//! node computes the identical registry — and hence, via
//! [`StakeRegistry::derive_epoch_info`], the identical validator set for the next
//! epoch. Determinism here is load-bearing for safety: any divergence would make
//! nodes install different sets and fork.

use std::collections::BTreeMap;
use std::net::SocketAddr;

use serde::{Deserialize, Serialize};

use crate::consensus::EpochInfo;
use crate::crypto::{aggsig, signature};
use crate::{Stake, ValidatorIndex, ValidatorInfo};

/// Marker byte prefixed to encoded [`StakeTx`] payloads.
///
/// Lets execution distinguish staking transactions from ordinary ones without a
/// self-describing format: a transaction whose payload does not start with this
/// tag is simply not a staking transaction and is ignored by the registry.
const STAKE_TX_TAG: u8 = 0xA1;

/// A staking transaction, carried inside a [`crate::Transaction`]'s payload.
///
/// Each variant is authorized by the `pubkey` it names (a validator may only
/// modify its own entry). Authorization is not enforced by this placeholder
/// model, but the shape mirrors a real staking program.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StakeTx {
    /// Register (or re-register) a validator with stake and network addresses.
    Register {
        pubkey: signature::PublicKey,
        voting_pubkey: aggsig::PublicKey,
        stake: Stake,
        all2all_address: SocketAddr,
        disseminator_address: SocketAddr,
        repair_requester_address: SocketAddr,
        repair_responder_address: SocketAddr,
    },
    /// Change the stake of an already-registered validator.
    SetStake {
        pubkey: signature::PublicKey,
        stake: Stake,
    },
    /// Update the advertised network addresses of a registered validator.
    SetAddrs {
        pubkey: signature::PublicKey,
        all2all_address: SocketAddr,
        disseminator_address: SocketAddr,
        repair_requester_address: SocketAddr,
        repair_responder_address: SocketAddr,
    },
    /// Remove a validator from the registry (it leaves at the next epoch).
    Deregister { pubkey: signature::PublicKey },
}

impl StakeTx {
    /// Returns the public key of the validator this transaction concerns.
    #[must_use]
    pub fn pubkey(&self) -> &signature::PublicKey {
        match self {
            Self::Register { pubkey, .. }
            | Self::SetStake { pubkey, .. }
            | Self::SetAddrs { pubkey, .. }
            | Self::Deregister { pubkey } => pubkey,
        }
    }

    /// Encodes this staking transaction into opaque transaction-payload bytes.
    ///
    /// The payload is tagged (see [`STAKE_TX_TAG`]) so it round-trips through
    /// [`Self::decode`] and is distinguishable from non-staking payloads.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = vec![STAKE_TX_TAG];
        bytes.extend(postcard::to_allocvec(self).expect("StakeTx serialization cannot fail"));
        bytes
    }

    /// Decodes a staking transaction from opaque transaction-payload bytes.
    ///
    /// Returns `None` if `bytes` is not a (well-formed) tagged staking payload,
    /// so ordinary transactions are transparently ignored.
    #[must_use]
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        let (&tag, rest) = bytes.split_first()?;
        if tag != STAKE_TX_TAG {
            return None;
        }
        postcard::from_bytes(rest).ok()
    }
}

/// A single validator's staking record.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StakeEntry {
    pub pubkey: signature::PublicKey,
    pub voting_pubkey: aggsig::PublicKey,
    pub stake: Stake,
    pub all2all_address: SocketAddr,
    pub disseminator_address: SocketAddr,
    pub repair_requester_address: SocketAddr,
    pub repair_responder_address: SocketAddr,
}

/// Canonical, deterministic registry of staked validators.
///
/// Part of the finalized execution state. Keyed by the 32-byte signature public
/// key so that iteration order — and therefore the derived validator set — is a
/// total, history-independent function of the contents.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct StakeRegistry {
    entries: BTreeMap<[u8; 32], StakeEntry>,
}

impl StakeRegistry {
    /// Builds a registry mirroring the validator set of `epoch`.
    ///
    /// Used to seed the genesis registry so that, absent any staking
    /// transactions, [`Self::derive_epoch_info`] reproduces the genesis set.
    #[must_use]
    pub fn from_genesis(epoch: &EpochInfo) -> Self {
        let entries = epoch
            .validators()
            .iter()
            .map(|v| (*v.pubkey.as_bytes(), StakeEntry::from(v)))
            .collect();
        Self { entries }
    }

    /// Number of registered validators (including any with zero stake).
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if no validators are registered.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns the registered entry for `pubkey`, if any.
    #[must_use]
    pub fn get(&self, pubkey: &signature::PublicKey) -> Option<&StakeEntry> {
        self.entries.get(pubkey.as_bytes())
    }

    /// Applies a single staking transaction to the registry.
    ///
    /// Application is deterministic and, within a block, performed in block
    /// order. `SetStake`/`SetAddrs`/`Deregister` for an unregistered key are
    /// no-ops.
    pub fn apply(&mut self, tx: &StakeTx) {
        match tx {
            StakeTx::Register { pubkey, .. } => {
                self.entries
                    .insert(*pubkey.as_bytes(), StakeEntry::from(tx));
            }
            StakeTx::SetStake { pubkey, stake } => {
                if let Some(entry) = self.entries.get_mut(pubkey.as_bytes()) {
                    entry.stake = *stake;
                }
            }
            StakeTx::SetAddrs {
                pubkey,
                all2all_address,
                disseminator_address,
                repair_requester_address,
                repair_responder_address,
            } => {
                if let Some(entry) = self.entries.get_mut(pubkey.as_bytes()) {
                    entry.all2all_address = *all2all_address;
                    entry.disseminator_address = *disseminator_address;
                    entry.repair_requester_address = *repair_requester_address;
                    entry.repair_responder_address = *repair_responder_address;
                }
            }
            StakeTx::Deregister { pubkey } => {
                self.entries.remove(pubkey.as_bytes());
            }
        }
    }

    /// Derives the validator set ([`EpochInfo`]) for an upcoming epoch.
    ///
    /// Includes every registered validator with non-zero stake, in ascending
    /// public-key order, assigning each a [`ValidatorIndex`] equal to its
    /// position. This ordering is a total function of the registry contents, so
    /// all honest nodes derive the identical set.
    ///
    /// Returns `None` if the resulting set would be empty (no validator can make
    /// progress); callers apply a carry-over policy in that case.
    #[must_use]
    pub fn derive_epoch_info(&self) -> Option<EpochInfo> {
        // `BTreeMap::values` already yields entries in ascending key (public-key)
        // order, so no explicit sort is needed for determinism.
        let validators: Vec<ValidatorInfo> = self
            .entries
            .values()
            .filter(|entry| entry.stake.inner() > 0)
            .enumerate()
            .map(|(i, entry)| entry.to_validator_info(ValidatorIndex::new(i as u64)))
            .collect();
        if validators.is_empty() {
            return None;
        }
        Some(EpochInfo::new(validators))
    }
}

impl StakeEntry {
    /// Builds a validator info for this entry at the given canonical index.
    fn to_validator_info(&self, id: ValidatorIndex) -> ValidatorInfo {
        ValidatorInfo {
            id,
            stake: self.stake,
            pubkey: self.pubkey,
            voting_pubkey: self.voting_pubkey,
            all2all_address: self.all2all_address,
            disseminator_address: self.disseminator_address,
            repair_requester_address: self.repair_requester_address,
            repair_responder_address: self.repair_responder_address,
        }
    }
}

impl From<&ValidatorInfo> for StakeEntry {
    fn from(v: &ValidatorInfo) -> Self {
        Self {
            pubkey: v.pubkey,
            voting_pubkey: v.voting_pubkey,
            stake: v.stake,
            all2all_address: v.all2all_address,
            disseminator_address: v.disseminator_address,
            repair_requester_address: v.repair_requester_address,
            repair_responder_address: v.repair_responder_address,
        }
    }
}

impl From<&StakeTx> for StakeEntry {
    /// Builds an entry from a `Register` transaction.
    ///
    /// # Panics
    ///
    /// Panics if `tx` is not a [`StakeTx::Register`].
    fn from(tx: &StakeTx) -> Self {
        match tx {
            StakeTx::Register {
                pubkey,
                voting_pubkey,
                stake,
                all2all_address,
                disseminator_address,
                repair_requester_address,
                repair_responder_address,
            } => Self {
                pubkey: *pubkey,
                voting_pubkey: *voting_pubkey,
                stake: *stake,
                all2all_address: *all2all_address,
                disseminator_address: *disseminator_address,
                repair_requester_address: *repair_requester_address,
                repair_responder_address: *repair_responder_address,
            },
            _ => panic!("StakeEntry can only be built from a Register transaction"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::generate_validators;

    /// Builds a `Register` transaction reproducing a validator's info.
    fn register(v: &ValidatorInfo) -> StakeTx {
        StakeTx::Register {
            pubkey: v.pubkey,
            voting_pubkey: v.voting_pubkey,
            stake: v.stake,
            all2all_address: v.all2all_address,
            disseminator_address: v.disseminator_address,
            repair_requester_address: v.repair_requester_address,
            repair_responder_address: v.repair_responder_address,
        }
    }

    /// Compares two epoch infos by `(pubkey, stake)` at each index.
    fn same_set(a: &EpochInfo, b: &EpochInfo) -> bool {
        a.validators().len() == b.validators().len()
            && a.validators().iter().zip(b.validators()).all(|(x, y)| {
                x.pubkey.as_bytes() == y.pubkey.as_bytes() && x.stake == y.stake && x.id == y.id
            })
    }

    #[test]
    fn encode_decode_round_trips_and_tags() {
        let (_, epoch) = generate_validators(1);
        let tx = register(&epoch.validators()[0]);
        let bytes = tx.encode();
        let decoded = StakeTx::decode(&bytes).expect("should decode");
        assert_eq!(decoded.pubkey().as_bytes(), tx.pubkey().as_bytes());

        // ordinary (untagged) payloads are not mistaken for staking txs
        assert!(StakeTx::decode(&[]).is_none());
        assert!(StakeTx::decode(b"hello world").is_none());
    }

    #[test]
    fn derive_is_deterministic_regardless_of_apply_order() {
        let (_, epoch) = generate_validators(5);
        let vs = epoch.validators();

        let mut forward = StakeRegistry::default();
        for v in vs {
            forward.apply(&register(v));
        }
        let mut reverse = StakeRegistry::default();
        for v in vs.iter().rev() {
            reverse.apply(&register(v));
        }

        let a = forward.derive_epoch_info().unwrap();
        let b = reverse.derive_epoch_info().unwrap();
        assert!(
            same_set(&a, &b),
            "registration order must not affect the set"
        );
        // and the derived set is internally consistent (id == index)
        for (i, v) in a.validators().iter().enumerate() {
            assert_eq!(v.id, ValidatorIndex::new(i as u64));
        }
    }

    #[test]
    fn derive_round_trips_genesis() {
        let (_, epoch) = generate_validators(4);
        let registry = StakeRegistry::from_genesis(&epoch);
        let derived = registry.derive_epoch_info().unwrap();

        // same multiset of (pubkey, stake), and re-deriving is stable
        assert_eq!(derived.validators().len(), epoch.validators().len());
        assert_eq!(derived.total_stake(), epoch.total_stake());
        let again = StakeRegistry::from_genesis(&derived)
            .derive_epoch_info()
            .unwrap();
        assert!(same_set(&derived, &again));
    }

    #[test]
    fn set_stake_and_deregister_change_the_set() {
        let (_, epoch) = generate_validators(3);
        let vs = epoch.validators();
        let mut registry = StakeRegistry::from_genesis(&epoch);

        // drop validator 0 to zero stake -> excluded from the derived set
        registry.apply(&StakeTx::SetStake {
            pubkey: vs[0].pubkey,
            stake: Stake::new(0),
        });
        // deregister validator 1 -> removed entirely
        registry.apply(&StakeTx::Deregister {
            pubkey: vs[1].pubkey,
        });

        let derived = registry.derive_epoch_info().unwrap();
        assert_eq!(derived.validators().len(), 1);
        assert_eq!(
            derived.validators()[0].pubkey.as_bytes(),
            vs[2].pubkey.as_bytes()
        );
    }

    #[test]
    fn empty_or_zero_stake_registry_derives_none() {
        assert!(StakeRegistry::default().derive_epoch_info().is_none());

        let (_, epoch) = generate_validators(2);
        let mut registry = StakeRegistry::from_genesis(&epoch);
        for v in epoch.validators() {
            registry.apply(&StakeTx::SetStake {
                pubkey: v.pubkey,
                stake: Stake::new(0),
            });
        }
        assert!(registry.derive_epoch_info().is_none());
    }
}
