// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Full validator node, combining consensus and execution.
//!
//! [`Validator`] is one abstraction level below the node binary. It owns the
//! [`Alpenglow`] consensus instance and an [`ExecutionEngine`], wires the
//! execution event channel between them, and drives both in its [`run`] method.
//!
//! [`run`]: Validator::run

use std::sync::Arc;

use color_eyre::Result;
use log::warn;
use tokio::sync::{RwLock, mpsc};

use crate::consensus::{BlockInfo, Pool};
use crate::execution::{ExecutionEngine, ExecutionEvent, ExecutionOutcome};
use crate::network::Network;
use crate::{All2All, Alpenglow, Disseminator, Transaction, VotorEvent};

/// Full validator node.
///
/// Owns a consensus instance ([`Alpenglow`]) and an execution engine, and
/// drives both concurrently. The execution engine receives events from the
/// blockstore (per decoded slice) and the block producer (per produced slice)
/// via an internal channel, and feeds results back to the votor.
pub struct Validator<A, D, T, E>
where
    A: All2All,
    D: Disseminator,
    T: Network<Recv = Transaction> + 'static,
    E: ExecutionEngine + Send + 'static,
{
    /// Consensus protocol instance.
    consensus: Alpenglow<A, D, T>,

    /// Execution engine.
    execution: E,

    /// Receiver side of the execution event channel.
    exec_rx: mpsc::Receiver<ExecutionEvent>,
}

impl<A, D, T, E> Validator<A, D, T, E>
where
    A: All2All + Send + Sync + 'static,
    D: Disseminator + Send + Sync + 'static,
    T: Network<Recv = Transaction> + 'static,
    E: ExecutionEngine + Send + 'static,
{
    /// Creates a new [`Validator`].
    ///
    /// Constructs the consensus instance internally, wiring the execution
    /// event channel between the blockstore / block producer and the engine.
    ///
    /// All parameters are forwarded to [`Alpenglow::new`].
    #[allow(clippy::too_many_arguments)]
    pub fn new<RN, RR>(
        secret_key: crate::crypto::signature::SecretKey,
        voting_secret_key: crate::crypto::aggsig::SecretKey,
        all2all: A,
        disseminator: D,
        repair_network: RN,
        repair_request_network: RR,
        epoch_info: std::sync::Arc<crate::consensus::ValidatorEpochInfo>,
        txs_receiver: T,
        execution: E,
    ) -> Self
    where
        RR: crate::network::RepairRequestNetwork + 'static,
        RN: crate::network::RepairNetwork + 'static,
    {
        let (exec_tx, exec_rx) = mpsc::channel(1024);
        let consensus = Alpenglow::new(
            secret_key,
            voting_secret_key,
            all2all,
            disseminator,
            repair_network,
            repair_request_network,
            epoch_info,
            txs_receiver,
            Some(exec_tx),
        );
        Self {
            consensus,
            execution,
            exec_rx,
        }
    }

    /// Runs consensus and the execution engine concurrently.
    ///
    /// The execution loop reads [`ExecutionEvent`]s and either drives the
    /// engine or forwards results (block valid/invalid) to the votor.
    /// Both loops are stopped when the consensus cancel token fires.
    pub async fn run(self) -> Result<()> {
        let Validator {
            consensus,
            execution,
            exec_rx,
        } = self;

        let pool = consensus.get_pool();
        let votor_tx = consensus.get_votor_tx();

        let exec_handle = tokio::spawn(execution_loop(exec_rx, execution, votor_tx, pool));

        consensus.run().await?;
        exec_handle.abort();
        Ok(())
    }
}

/// Drives the execution engine, forwarding results to the votor and pool.
async fn execution_loop<E: ExecutionEngine>(
    mut exec_rx: mpsc::Receiver<ExecutionEvent>,
    mut engine: E,
    votor_tx: mpsc::Sender<VotorEvent>,
    pool: Arc<RwLock<Box<dyn Pool + Send + Sync>>>,
) {
    while let Some(event) = exec_rx.recv().await {
        match event {
            ExecutionEvent::BeginBlock { id, parent } => {
                engine.begin_block(id, parent);
            }
            ExecutionEvent::Transactions { id, transactions } => {
                engine.execute_transactions(id, transactions);
            }
            ExecutionEvent::EndBlock {
                block_id,
                parent_id,
                expected_state_hash,
            } => {
                let outcome = engine.end_block(block_id.clone(), &expected_state_hash);
                let slot = block_id.0;
                let block_info = BlockInfo {
                    hash: block_id.1.clone(),
                    parent: parent_id.clone(),
                };
                match outcome {
                    ExecutionOutcome::Valid => {
                        votor_tx
                            .send(VotorEvent::Block { slot, block_info })
                            .await
                            .unwrap();
                        pool.write().await.add_block(block_id, parent_id).await;
                    }
                    ExecutionOutcome::Invalid => {
                        warn!("execution validation failed for block {block_id:?}");
                        votor_tx.send(VotorEvent::InvalidBlock(slot)).await.unwrap();
                    }
                }
            }
            ExecutionEvent::ComputeStateHash { slot, reply } => {
                let hash = engine.compute_state_hash(slot);
                let _ = reply.send(hash);
            }
            ExecutionEvent::Finalized(block_id) => {
                engine.finalize(block_id);
            }
        }
    }
}
