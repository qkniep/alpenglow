// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Direct all-to-all broadcast protocols.
//!
//! The [`All2All`] trait gives a simple interface for broadcasting messages.
//! It does not impose restrictions on the guarantees that should be provided.
//! However, each implementor should clearly document which guarantees it provides.
//!
//! This module provides two implementations of [`All2All`]:
//! - [`TrivialAll2All`] implements a simple best-effort all-to-all broadcast protocol.
//! - [`RobustAll2All`] is a more robust implementation, handling retransmits.
//!
//! The exact guarantees, however, also depend on the underlying [`Network`],
//! since both implementations are generic over [`Network`].
//! For example, [`TrivialAll2All`] over a TCP-based network might still give
//! strong reliability guarantess.
//!
//! # Examples
//!
//! ```
//! use alpenglow::network::{NetworkError, NetworkMessage};
//! use alpenglow::all2all::All2All;
//!
//! async fn broadcast_all(msgs: &[NetworkMessage], all2all: impl All2All) -> Result<(), NetworkError> {
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

use crate::network::{NetworkError, NetworkMessage};

pub use robust::RobustAll2All;
pub use trivial::TrivialAll2All;

/// Abstraction for a direct all-to-all network communication protocol.
pub trait All2All {
    /// Broadcasts the given message to all known nodes.
    fn broadcast(
        &self,
        msg: &NetworkMessage,
    ) -> impl Future<Output = Result<(), NetworkError>> + Send;

    /// Receives a message from any of the other nodes.
    fn receive(&self) -> impl Future<Output = Result<NetworkMessage, NetworkError>> + Send;
}
