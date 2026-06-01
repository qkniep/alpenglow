// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Installs new validator sets at epoch boundaries.
//!
//! The [`EpochManager`] turns finalized on-chain stake state into the validator
//! set for upcoming epochs. It replays the staking transactions of every
//! finalized block into a [`StakeRegistry`] and, at each epoch boundary, derives
//! the next epoch's set and installs it into the shared [`EpochRegistry`].
//!
//! # Boundary schedule (one epoch of lookahead)
//!
//! The set for epoch `e + 1` is derived from the registry as it stands once
//! epoch `e - 1` is fully finalized — i.e. it is frozen a full epoch before it
//! is needed. Concretely, *crossing into epoch `e`* (finalizing the first block
//! of epoch `e`, by which point all of epoch `e - 1` is finalized) installs
//! epoch `e + 1`. Epochs 0 and 1 are bootstrapped at construction from the
//! genesis set.
//!
//! So a staking transaction finalized during epoch `e` takes effect in epoch
//! `e + 2`. Because the registry is a deterministic function of the finalized
//! chain, every honest node derives the identical set for each epoch.

use std::sync::Arc;

use log::{debug, info};
use tokio::sync::mpsc::Receiver;

use super::EpochRegistry;
use crate::consensus::SharedBlockstore;
use crate::execution::{StakeRegistry, StakeTx};
use crate::types::Epoch;
use crate::{BlockId, Slot, Transaction};

/// Derives and installs validator sets for upcoming epochs from finalized stake.
pub struct EpochManager {
    /// Shared registry of validator sets, into which new epochs are installed.
    epoch_info: Arc<EpochRegistry>,
    /// Blockstore, used to fetch finalized blocks' transactions.
    blockstore: SharedBlockstore,
    /// Running staking registry: the finalized on-chain stake state.
    registry: StakeRegistry,
    /// Highest finalized slot whose transactions have been applied.
    applied_slot: Slot,
    /// Next epoch number to derive and install.
    next_epoch_to_install: Epoch,
}

impl EpochManager {
    /// Creates a new epoch manager seeded with the genesis staking registry.
    ///
    /// Bootstraps epoch 1 with the same validator set as epoch 0 (the genesis
    /// set), so both initial epochs are resolvable before any staking
    /// transactions are finalized. Epoch 2 onward are derived from finalized
    /// stake.
    #[must_use]
    pub fn new(
        epoch_info: Arc<EpochRegistry>,
        blockstore: SharedBlockstore,
        genesis_registry: StakeRegistry,
    ) -> Self {
        // bootstrap epoch 1 == epoch 0 (no staking changes have taken effect yet)
        let epoch0 = epoch_info.genesis_epoch_info();
        epoch_info.install(Epoch::new(1), (*epoch0).clone());
        Self {
            epoch_info,
            blockstore,
            registry: genesis_registry,
            applied_slot: Slot::genesis(),
            next_epoch_to_install: Epoch::new(2),
        }
    }

    /// Runs the epoch manager loop until the finalization channel closes.
    ///
    /// Consumes finalized [`BlockId`]s (delivered in slot order), applies their
    /// staking transactions, and installs new epoch sets as boundaries are
    /// crossed.
    pub async fn run(mut self, mut finalized: Receiver<BlockId>) {
        while let Some(block_id) = finalized.recv().await {
            self.apply_finalized_block(block_id).await;
            self.install_due_epochs();
        }
    }

    /// Applies the staking transactions of one finalized block to the registry.
    async fn apply_finalized_block(&mut self, block_id: BlockId) {
        let slot = block_id.0;
        if slot <= self.applied_slot {
            return; // genesis, or an already-applied block re-reported
        }
        let transactions = {
            let blockstore = self.blockstore.read().await;
            match blockstore.get_block(&block_id) {
                Some(block) => block.transactions().to_vec(),
                // The block may have been pruned before we read it; it then
                // contributes no staking changes. (Acceptable for the research
                // model; a production engine would replay from durable state.)
                None => Vec::new(),
            }
        };
        self.apply_transactions(slot, &transactions);
    }

    /// Applies a finalized block's `transactions` at `slot` to the registry.
    fn apply_transactions(&mut self, slot: Slot, transactions: &[Transaction]) {
        if slot <= self.applied_slot {
            return;
        }
        for tx in transactions {
            if let Some(stake_tx) = StakeTx::decode(&tx.0) {
                debug!(
                    "applying staking tx for {:?} at slot {slot}",
                    stake_tx.pubkey()
                );
                self.registry.apply(&stake_tx);
            }
        }
        self.applied_slot = slot;
    }

    /// Installs every epoch whose validator set is now due to be frozen.
    ///
    /// Crossing into epoch `e` (i.e. `applied_slot` reaching epoch `e`) installs
    /// epoch `e + 1`. Processing finalized blocks one at a time means this
    /// installs at most one epoch per block, each derived from the registry at
    /// its own boundary.
    fn install_due_epochs(&mut self) {
        let finalized_epoch = self.applied_slot.epoch().inner();
        while finalized_epoch + 1 >= self.next_epoch_to_install.inner() {
            let epoch = self.next_epoch_to_install;
            let info = self.registry.derive_epoch_info().unwrap_or_else(|| {
                // carry over the previous epoch's set if the derived set is empty
                // (a chain must never halt for lack of a usable next set)
                let prev = Epoch::new(epoch.inner() - 1);
                (*self
                    .epoch_info
                    .for_epoch(prev)
                    .expect("previous epoch is always installed before the next"))
                .clone()
            });
            info!(
                "installing epoch {epoch} with {} validators",
                info.validators().len()
            );
            self.epoch_info.install(epoch, info);
            self.next_epoch_to_install = epoch.next();
        }
    }
}

#[cfg(test)]
mod tests {
    use tokio::sync::{RwLock, mpsc};

    use super::*;
    use crate::consensus::{BlockstoreImpl, EpochInfo};
    use crate::test_utils::generate_validators;
    use crate::{Transaction, ValidatorInfo};

    fn register(v: &ValidatorInfo) -> Transaction {
        Transaction(
            StakeTx::Register {
                pubkey: v.pubkey,
                voting_pubkey: v.voting_pubkey,
                stake: v.stake,
                all2all_address: v.all2all_address,
                disseminator_address: v.disseminator_address,
                repair_requester_address: v.repair_requester_address,
                repair_responder_address: v.repair_responder_address,
            }
            .encode(),
        )
    }

    fn deregister(v: &ValidatorInfo) -> Transaction {
        Transaction(StakeTx::Deregister { pubkey: v.pubkey }.encode())
    }

    /// Builds an epoch manager whose node is `own`, seeded with the genesis set.
    fn manager_for(own: &ValidatorInfo, epoch0: EpochInfo) -> (Arc<EpochRegistry>, EpochManager) {
        let registry = Arc::new(EpochRegistry::new(own.pubkey, epoch0.clone()));
        let (tx, _rx) = mpsc::channel(16);
        let blockstore: SharedBlockstore = Arc::new(RwLock::new(BlockstoreImpl::new(tx)));
        let genesis = StakeRegistry::from_genesis(&epoch0);
        let manager = EpochManager::new(registry.clone(), blockstore, genesis);
        (registry, manager)
    }

    #[test]
    fn installs_join_and_leave_at_epoch_boundary() {
        let (_, all) = generate_validators(5);
        let vs = all.validators();
        let epoch0 = EpochInfo::new(vs[..4].to_vec()); // validators 0..3
        let joiner = &vs[4];

        // our node is validator 0, which will leave at the boundary
        let (registry, mut manager) = manager_for(&vs[0], epoch0.clone());

        // epochs 0 and 1 are bootstrapped to the genesis set; epoch 2 not yet known
        assert_eq!(
            registry
                .for_epoch(Epoch::new(0))
                .unwrap()
                .validators()
                .len(),
            4
        );
        assert_eq!(
            registry
                .for_epoch(Epoch::new(1))
                .unwrap()
                .validators()
                .len(),
            4
        );
        assert!(registry.for_epoch(Epoch::new(2)).is_none());

        // during epoch 0: validator 4 joins, validator 0 leaves
        manager.apply_transactions(Slot::new(1), &[register(joiner), deregister(&vs[0])]);
        manager.install_due_epochs(); // still inside epoch 0 -> nothing frozen yet
        assert!(registry.for_epoch(Epoch::new(2)).is_none());

        // crossing into epoch 1 freezes epoch 2 from the end-of-epoch-0 stake state
        manager.apply_transactions(Epoch::new(1).first_slot(), &[]);
        manager.install_due_epochs();

        let epoch2 = registry
            .for_epoch(Epoch::new(2))
            .expect("epoch 2 installed");
        assert_eq!(epoch2.validators().len(), 4);
        let pks: Vec<[u8; 32]> = epoch2
            .validators()
            .iter()
            .map(|v| *v.pubkey.as_bytes())
            .collect();
        assert!(
            pks.contains(joiner.pubkey.as_bytes()),
            "joiner is in epoch 2"
        );
        assert!(
            !pks.contains(vs[0].pubkey.as_bytes()),
            "leaver is not in epoch 2"
        );

        // our node (validator 0) is a member of epochs 0/1 but not epoch 2
        assert!(registry.own_index_for_slot(Slot::genesis()).is_some());
        assert!(
            registry
                .own_index_for_slot(Epoch::new(1).first_slot())
                .is_some()
        );
        assert_eq!(
            registry.own_index_for_slot(Epoch::new(2).first_slot()),
            None
        );

        // the joiner's own node, by contrast, becomes a member only at epoch 2
        let (joiner_reg, mut joiner_mgr) = manager_for(joiner, epoch0);
        joiner_mgr.apply_transactions(Slot::new(1), &[register(joiner), deregister(&vs[0])]);
        joiner_mgr.apply_transactions(Epoch::new(1).first_slot(), &[]);
        joiner_mgr.install_due_epochs();
        assert_eq!(joiner_reg.own_index_for_slot(Slot::genesis()), None);
        assert!(
            joiner_reg
                .own_index_for_slot(Epoch::new(2).first_slot())
                .is_some()
        );
    }
}
