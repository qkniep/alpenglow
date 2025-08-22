// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Fast block dissemination protocols.
//!
//!

pub mod rotor;
pub mod trivial;
pub mod turbine;

use async_trait::async_trait;
use mockall::automock;

pub use rotor::Rotor;
pub use trivial::TrivialDisseminator;
pub use turbine::Turbine;

use crate::{network::NetworkError, shredder::Shred};

/// Abstraction of a block dissemination protocol.
#[async_trait]
#[automock]
pub trait Disseminator {
    /// Sends the given shred to the network as the original source.
    async fn send(&self, shred: &Shred) -> Result<(), NetworkError>;

    /// Performs any necessary forwarding of the given shred.
    async fn forward(&self, shred: &Shred) -> Result<(), NetworkError>;

    /// Receives the next shred from the network.
    async fn receive(&self) -> Result<Shred, NetworkError>;
}
