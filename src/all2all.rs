// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Direct all-to-all broadcast protocols.
//!
//! The [`All2All`] trait gives a simple interface for broadcasting messages.
//! It does not impose restrictions on the guarantees that should be provided.
//! However, each implementor should clearly document which guarantees it provides.
//!
//! This module provides two implementations of the [`All2All`] trait:
//! - [`TrivialAll2All`] implements a simple best-effort all-to-all broadcast protocol.
//! - [`RobustAll2All`] is a more robust implementation, handling retransmits.
//!
//! The exact guarantees, however, also depend on the underlying [`Network`],
//! since both implementations are generic over the [`Network`] trait.
//! For example, [`TrivialAll2All`] over a TCP-based network might still give
//! strong reliability guarantess.
//!
//! # Examples
//!
//! ```rust
//! use alpenglow::all2all::All2All;
//! use alpenglow::consensus::ConsensusMessage;
//!
//! async fn broadcast_all(msgs: &[ConsensusMessage], all2all: impl All2All) -> std::io::Result<()> {
//!     for msg in msgs {
//!         all2all.broadcast(msg).await?;
//!     }
//!     Ok(())
//! }
//! ```
//!
//! [`Network`]: crate::network::Network

mod robust;
mod trivial;

use async_trait::async_trait;

pub use self::robust::RobustAll2All;
pub use self::trivial::TrivialAll2All;
use crate::consensus::ConsensusMessage;

/// Abstraction for a direct all-to-all network communication protocol.
#[async_trait]
pub trait All2All {
    /// Broadcasts the given message to all known nodes.
    ///
    /// Which delivery guarantees are provided depends on the implementor.
    /// This is allowed to be best-effort or any stronger set of guarantees.
    /// Each implementor should clearly document which guarantees it provides.
    ///
    /// # Errors
    ///
    /// Implementors should return an [`std::io::Error`] iff the underlying network fails.
    async fn broadcast(&self, msg: &ConsensusMessage) -> std::io::Result<()>;

    /// Receives a message from any of the other nodes.
    ///
    /// Resolves to the next successfully deserialized [`ConsensusMessage`].
    /// Does not provide information on which node sent the message.
    ///
    /// # Errors
    ///
    /// Implementors should return an [`std::io::Error`] iff the underlying network fails.
    async fn receive(&self) -> std::io::Result<ConsensusMessage>;
}
