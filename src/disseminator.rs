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

pub use self::rotor::Rotor;
pub use self::trivial::TrivialDisseminator;
pub use self::turbine::Turbine;
use crate::shredder::Shred;

/// Abstraction of a block dissemination protocol.
#[cfg_attr(test, mockall::automock)]
pub trait Disseminator {
    /// Sends the given shred to the network as the original source.
    fn send(&self, shred: &Shred) -> impl Future<Output = std::io::Result<()>> + Send;

    /// Performs any necessary forwarding of the given shred.
    fn forward(&self, shred: &Shred) -> impl Future<Output = std::io::Result<()>> + Send;

    /// Receives the next shred from the network.
    fn receive(&self) -> impl Future<Output = std::io::Result<Shred>> + Send;
}
