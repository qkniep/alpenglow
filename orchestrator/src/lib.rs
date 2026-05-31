// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Cloud-testbed orchestrator for running real-world Alpenglow benchmarks.
//!
//! The orchestrator provisions a set of machines on a cloud provider (or uses
//! a list of machines you already own), installs the Alpenglow node on each,
//! runs a benchmark, and collects the logs back to your local machine.
//!
//! The design mirrors the [Mysticeti orchestrator]: a small
//! [`provider::ServerProviderClient`] trait abstracts the cloud APIs, an
//! [`ssh`] layer drives commands over SSH, and a protocol adapter
//! ([`alpenglow::Alpenglow`]) knows how to turn instances into running nodes.
//!
//! Everything is driven from a single YAML [`settings::Settings`] file; see the
//! templates under `assets/` and the crate `README.md` for the workflow.
//!
//! [Mysticeti orchestrator]: https://github.com/asonnino/mysticeti/tree/main/crates/orchestrator

pub mod alpenglow;
pub mod benchmark;
pub mod provider;
pub mod settings;
pub mod ssh;
pub mod testbed;
