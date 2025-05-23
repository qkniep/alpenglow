// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Fast block dissemination protocols.
//!
//!

pub mod rotor;
pub mod trivial;
pub mod turbine;

pub use rotor::Rotor;
pub use trivial::TrivialDisseminator;
pub use turbine::Turbine;

use crate::{network::NetworkError, shredder::Shred};

/// Abstraction of a block dissemination protocol.
pub trait Disseminator {
    /// Sends the given shred to the network as the original source.
    fn send(&self, shred: &Shred) -> impl Future<Output = Result<(), NetworkError>> + Send;

    /// Performs any necessary forwarding of the given shred.
    fn forward(&self, shred: &Shred) -> impl Future<Output = Result<(), NetworkError>> + Send;

    /// Receives the next shred from the network.
    fn receive(&self) -> impl Future<Output = Result<Shred, NetworkError>> + Send;
}
