// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Fast block dissemination protocols.
//!
//! This module provides the [`Disseminator`] trait for block dissemination protocols.
//!
//! Also, this module provides implementations of three dissemination protocols:
//! - [`TrivialDisseminator`] implements a leader-to-everyone broadcast protocol.
//! - [`Rotor`] implements Alpenglow's Rotor, which is an evolution of Turbine.
//! - [`Turbine`] implements Solana's basic Turbine protocol.

pub mod rotor;
pub mod trivial;
pub mod turbine;

use async_trait::async_trait;
use mockall::automock;

pub use self::rotor::Rotor;
pub use self::trivial::TrivialDisseminator;
pub use self::turbine::Turbine;
use crate::shredder::Shred;

/// Abstraction of a block dissemination protocol.
#[async_trait]
#[automock]
pub trait Disseminator {
    /// Sends the given shred to the network as the original source.
    async fn send(&self, shred: &Shred) -> std::io::Result<()>;

    /// Performs any necessary forwarding of the given shred.
    async fn forward(&self, shred: &Shred) -> std::io::Result<()>;

    /// Receives the next shred from the network.
    async fn receive(&self) -> std::io::Result<Shred>;
}
