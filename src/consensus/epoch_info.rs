// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;
use std::sync::Arc;

use arc_swap::ArcSwap;

use crate::consensus::{
    QUORUM_THRESHOLD, STRONG_QUORUM_THRESHOLD, WEAK_QUORUM_THRESHOLD, WEAKEST_QUORUM_THRESHOLD,
};
use crate::crypto::signature;
use crate::types::{Epoch, SLOTS_PER_WINDOW};
use crate::{Slot, Stake, ValidatorIndex, ValidatorInfo};

/// Shared epoch information, identical across all validators.
///
/// Contains the validator set and derived data for one epoch.
/// Constructed once per epoch and shared via [`std::sync::Arc`].
#[derive(Clone, Debug)]
pub struct EpochInfo {
    validators: Vec<ValidatorInfo>,
    total_stake: Stake,
}

/// The node's own role within a particular epoch's validator set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnEpochIdentity {
    /// The node is validator `ValidatorIndex` in this epoch's set.
    Member(ValidatorIndex),
    /// The node is not part of this epoch's validator set.
    NonMember,
}

impl OwnEpochIdentity {
    /// Returns our [`ValidatorIndex`] if we are a member of the epoch, else `None`.
    #[must_use]
    pub fn index(self) -> Option<ValidatorIndex> {
        match self {
            Self::Member(index) => Some(index),
            Self::NonMember => None,
        }
    }
}

/// Immutable snapshot of installed epochs, swapped atomically on install.
#[derive(Clone)]
struct RegistrySnapshot {
    /// Validator set for each installed epoch.
    epochs: BTreeMap<Epoch, Arc<EpochInfo>>,
    /// Our own identity within each installed epoch (derived from `own_pubkey`).
    own_identity: BTreeMap<Epoch, OwnEpochIdentity>,
}

/// Per-validator view of the (possibly changing) validator sets across epochs.
///
/// Holds the validator set ([`EpochInfo`]) for each installed epoch and resolves
/// the right set for a given slot via [`Self::for_slot`], plus the node's own
/// identity in that epoch
/// (it may be a [`OwnEpochIdentity::Member`] of some epochs and a
/// [`OwnEpochIdentity::NonMember`] of others as validators join and leave).
///
/// Shared across all consensus components via [`std::sync::Arc`]. Reads are
/// lock-free; [`Self::install`] (called once per epoch boundary) atomically
/// swaps in an extended snapshot.
pub struct EpochRegistry {
    /// Our node's signature public key, used to (re)derive our per-epoch identity.
    own_pubkey: signature::PublicKey,
    /// Atomically-swappable snapshot of installed epochs.
    snapshot: ArcSwap<RegistrySnapshot>,
}

/// Locates `own_pubkey` in `info`, yielding our identity within that epoch.
fn own_identity_in(own_pubkey: &signature::PublicKey, info: &EpochInfo) -> OwnEpochIdentity {
    info.validators()
        .iter()
        .find(|v| v.pubkey.as_bytes() == own_pubkey.as_bytes())
        .map_or(OwnEpochIdentity::NonMember, |v| {
            OwnEpochIdentity::Member(v.id)
        })
}

impl EpochInfo {
    /// Creates a new `EpochInfo` from the given validator set.
    ///
    /// # Panics
    ///
    /// Panics if any validator's `id` does not match its index in the vector.
    pub fn new(validators: Vec<ValidatorInfo>) -> Self {
        for (i, v) in validators.iter().enumerate() {
            assert!(
                v.id.as_usize() == i,
                "validator at index {i} has id {}, expected {i}",
                v.id
            );
        }
        let total_stake = validators.iter().map(|v| v.stake).sum();
        Self {
            validators,
            total_stake,
        }
    }

    /// Returns all validators in this epoch.
    #[must_use]
    pub fn validators(&self) -> &[ValidatorInfo] {
        &self.validators
    }

    /// Gives the validator info for the given validator index.
    ///
    /// # Panics
    ///
    /// Panics if the validator index is out of range.
    #[must_use]
    pub fn validator(&self, id: ValidatorIndex) -> &ValidatorInfo {
        &self.validators[id.as_usize()]
    }

    /// Gives the validator info for the leader for the given slot.
    ///
    /// Leader rotation is *epoch-local*: the window counter resets at each epoch
    /// boundary, so every epoch's (possibly different) validator set starts its
    /// rotation at index 0. This relies on epoch boundaries coinciding with
    /// window boundaries (see the `const_assert!` in [`crate::types::slot`]).
    #[must_use]
    pub fn leader(&self, slot: Slot) -> &ValidatorInfo {
        let window = slot.inner() / SLOTS_PER_WINDOW;
        let epoch_first_window = slot.first_slot_in_epoch().inner() / SLOTS_PER_WINDOW;
        let local_window = window - epoch_first_window;
        let leader_id = local_window % (self.validators.len() as u64);
        self.validator(ValidatorIndex::new(leader_id))
    }

    /// Gives the total stake over all validators.
    #[must_use]
    pub fn total_stake(&self) -> Stake {
        self.total_stake
    }

    /// Returns `true` if `stake` meets the weakest quorum threshold (20%).
    #[must_use]
    pub fn is_weakest_quorum(&self, stake: Stake) -> bool {
        WEAKEST_QUORUM_THRESHOLD.is_met(stake.inner(), self.total_stake().inner())
    }

    /// Returns `true` if `stake` meets the weak quorum threshold (40%).
    #[must_use]
    pub fn is_weak_quorum(&self, stake: Stake) -> bool {
        WEAK_QUORUM_THRESHOLD.is_met(stake.inner(), self.total_stake().inner())
    }

    /// Returns `true` if `stake` meets the standard quorum threshold (60%).
    #[must_use]
    pub fn is_quorum(&self, stake: Stake) -> bool {
        QUORUM_THRESHOLD.is_met(stake.inner(), self.total_stake().inner())
    }

    /// Returns `true` if `stake` meets the strong quorum threshold (80%).
    #[must_use]
    pub fn is_strong_quorum(&self, stake: Stake) -> bool {
        STRONG_QUORUM_THRESHOLD.is_met(stake.inner(), self.total_stake().inner())
    }
}

impl EpochRegistry {
    /// Creates a registry bootstrapped with the genesis epoch (epoch 0).
    ///
    /// Our own identity in epoch 0 is derived by locating `own_pubkey` in the
    /// genesis validator set (yielding [`OwnEpochIdentity::NonMember`] if absent).
    #[must_use]
    pub fn new(own_pubkey: signature::PublicKey, genesis_epoch: EpochInfo) -> Self {
        let info = Arc::new(genesis_epoch);
        let identity = own_identity_in(&own_pubkey, &info);
        let snapshot = RegistrySnapshot {
            epochs: [(Epoch::genesis(), info)].into_iter().collect(),
            own_identity: [(Epoch::genesis(), identity)].into_iter().collect(),
        };
        Self {
            own_pubkey,
            snapshot: ArcSwap::from_pointee(snapshot),
        }
    }

    /// Creates a single-epoch registry with an explicit own index.
    ///
    /// Convenience for tests and bootstrapping where the node is known to be a
    /// member of the genesis epoch at `own_id`. The own public key is taken from
    /// that validator's entry, so identity tracking still works if more epochs
    /// are later installed.
    ///
    /// # Panics
    ///
    /// Panics if `own_id` is not a valid index into `genesis_epoch`.
    #[must_use]
    pub fn single(own_id: ValidatorIndex, genesis_epoch: EpochInfo) -> Self {
        let own_pubkey = genesis_epoch.validator(own_id).pubkey;
        Self::new(own_pubkey, genesis_epoch)
    }

    /// Returns the validator set for the epoch that `slot` belongs to, if installed.
    #[must_use]
    pub fn for_slot(&self, slot: Slot) -> Option<Arc<EpochInfo>> {
        self.snapshot.load().epochs.get(&slot.epoch()).cloned()
    }

    /// Returns the validator set for `epoch`, if installed.
    #[must_use]
    pub fn for_epoch(&self, epoch: Epoch) -> Option<Arc<EpochInfo>> {
        self.snapshot.load().epochs.get(&epoch).cloned()
    }

    /// Returns the genesis epoch's validator set.
    ///
    /// Used by disseminator/repair samplers that are not yet epoch-aware (they
    /// build a single sampler at construction time); P3 replaces those with
    /// per-epoch samplers resolved from the block/shred's slot.
    #[must_use]
    pub fn genesis_epoch_info(&self) -> Arc<EpochInfo> {
        self.for_epoch(Epoch::genesis())
            .expect("genesis epoch is always installed")
    }

    /// Returns our own identity within the epoch that `slot` belongs to.
    ///
    /// Yields [`OwnEpochIdentity::NonMember`] if that epoch is not installed.
    #[must_use]
    pub fn own_identity_for_slot(&self, slot: Slot) -> OwnEpochIdentity {
        self.snapshot
            .load()
            .own_identity
            .get(&slot.epoch())
            .copied()
            .unwrap_or(OwnEpochIdentity::NonMember)
    }

    /// Returns our own [`ValidatorIndex`] in the epoch of `slot`, or `None` if we
    /// are not a member of that epoch (or it is not installed).
    #[must_use]
    pub fn own_index_for_slot(&self, slot: Slot) -> Option<ValidatorIndex> {
        self.own_identity_for_slot(slot).index()
    }

    /// Returns the highest epoch number currently installed.
    #[must_use]
    pub fn highest_installed_epoch(&self) -> Epoch {
        *self
            .snapshot
            .load()
            .epochs
            .keys()
            .next_back()
            .expect("registry always contains at least the genesis epoch")
    }

    /// Returns our node's signature public key.
    #[must_use]
    pub fn own_pubkey(&self) -> signature::PublicKey {
        self.own_pubkey
    }

    /// Installs the validator set for `epoch`, atomically extending the registry.
    ///
    /// Recomputes our own identity for `epoch` by locating `own_pubkey` in `info`.
    /// Replaces any set previously installed for `epoch`.
    pub fn install(&self, epoch: Epoch, info: EpochInfo) {
        let info = Arc::new(info);
        let identity = own_identity_in(&self.own_pubkey, &info);
        self.snapshot.rcu(|prev| {
            let mut next = (**prev).clone();
            next.epochs.insert(epoch, info.clone());
            next.own_identity.insert(epoch, identity);
            next
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::generate_validators;
    use crate::types::{SLOTS_PER_EPOCH, SLOTS_PER_WINDOW};
    use crate::{Slot, Stake, ValidatorInfo};

    /// Rebuilds an [`EpochInfo`] from a subset of validators, reassigning indices
    /// to their position (as [`EpochInfo::new`] requires `id == index`).
    fn reindexed(validators: &[ValidatorInfo]) -> EpochInfo {
        let vs = validators
            .iter()
            .enumerate()
            .map(|(i, v)| {
                let mut v = v.clone();
                v.id = ValidatorIndex::new(i as u64);
                v
            })
            .collect();
        EpochInfo::new(vs)
    }

    #[test]
    fn install_resolves_per_epoch_and_tracks_membership() {
        let (_, epoch0) = generate_validators(4);
        let vs = epoch0.validators().to_vec();
        // epoch 1 drops validator 0 (it leaves the set) and keeps 1, 2, 3.
        let epoch1 = reindexed(&vs[1..]);

        let epoch1_slot = Epoch::new(1).first_slot();

        // A node that is validator 0 in epoch 0 and absent from epoch 1.
        let leaving = EpochRegistry::new(vs[0].pubkey, epoch0.clone());
        assert_eq!(
            leaving.own_index_for_slot(Slot::genesis()),
            Some(ValidatorIndex::new(0))
        );
        // before install, epoch 1 is unknown -> NonMember and no set
        assert_eq!(
            leaving.own_identity_for_slot(epoch1_slot),
            OwnEpochIdentity::NonMember
        );
        assert!(leaving.for_slot(epoch1_slot).is_none());

        leaving.install(Epoch::new(1), epoch1.clone());
        assert_eq!(leaving.highest_installed_epoch(), Epoch::new(1));
        assert_eq!(leaving.for_slot(epoch1_slot).unwrap().validators().len(), 3);
        // validator 0 left, so it is a NonMember of epoch 1 (and still member of 0)
        assert_eq!(
            leaving.own_index_for_slot(Slot::genesis()),
            Some(ValidatorIndex::new(0))
        );
        assert_eq!(leaving.own_index_for_slot(epoch1_slot), None);

        // A node that is validator 1 in epoch 0 and validator 0 in epoch 1 (its
        // index changes across the boundary as the set shrinks).
        let staying = EpochRegistry::new(vs[1].pubkey, epoch0);
        staying.install(Epoch::new(1), epoch1);
        assert_eq!(
            staying.own_index_for_slot(Slot::genesis()),
            Some(ValidatorIndex::new(1))
        );
        assert_eq!(
            staying.own_index_for_slot(epoch1_slot),
            Some(ValidatorIndex::new(0))
        );
    }

    #[test]
    fn leader_rotation_is_epoch_local() {
        let (_, epoch_info) = generate_validators(7);

        // Within epoch 0 the leader rotates through windows 0, 1, 2, ...
        assert_eq!(epoch_info.leader(Slot::new(0)).id.inner(), 0);
        assert_eq!(epoch_info.leader(Slot::new(SLOTS_PER_WINDOW)).id.inner(), 1);

        // There are 4500 windows per epoch and 4500 % 7 == 6, so a *global*
        // rotation would put leader 6 at the first slot of epoch 1. Epoch-local
        // rotation instead restarts at index 0.
        let first_of_epoch1 = Slot::new(SLOTS_PER_EPOCH);
        assert!(first_of_epoch1.is_epoch_start());
        assert_eq!(epoch_info.leader(first_of_epoch1).id.inner(), 0);
        assert_eq!(
            epoch_info
                .leader(Slot::new(SLOTS_PER_EPOCH + SLOTS_PER_WINDOW))
                .id
                .inner(),
            1
        );
    }

    #[test]
    fn quorums() {
        let (_, epoch_info) = generate_validators(6);
        assert!(epoch_info.is_weak_quorum(Stake::new(3)));
        assert!(!epoch_info.is_quorum(Stake::new(3)));
        assert!(epoch_info.is_quorum(Stake::new(4)));
        assert!(!epoch_info.is_strong_quorum(Stake::new(4)));
        assert!(epoch_info.is_strong_quorum(Stake::new(5)));

        let (_, epoch_info) = generate_validators(11);
        assert!(epoch_info.is_weak_quorum(Stake::new(5)));
        assert!(!epoch_info.is_quorum(Stake::new(5)));
        assert!(epoch_info.is_quorum(Stake::new(7)));
        assert!(!epoch_info.is_strong_quorum(Stake::new(7)));
        assert!(epoch_info.is_strong_quorum(Stake::new(9)));
    }
}
