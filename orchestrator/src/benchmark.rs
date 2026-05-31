// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Parameters describing a single benchmark run.

use std::fmt;
use std::path::Path;

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

/// Parameters for one benchmark run.
///
/// Loaded from a YAML file (see `assets/benchmark-parameters-template.yml`) and
/// optionally overridden from the command line.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BenchmarkParameters {
    /// Number of validator nodes to run (must be <= number of active instances).
    pub nodes: usize,
    /// Base UDP port for node 0. Each node uses `base_port..base_port + 5`.
    #[serde(default = "defaults::base_port")]
    pub base_port: u16,
    /// Target transactions per second for the load generator.
    pub load_tps: u64,
    /// Size of each transaction, in bytes.
    #[serde(default = "defaults::transaction_size")]
    pub transaction_size: u64,
    /// How long to let the benchmark run before tearing it down, in seconds.
    pub duration_secs: u64,
}

impl Default for BenchmarkParameters {
    fn default() -> Self {
        Self {
            nodes: 4,
            base_port: defaults::base_port(),
            load_tps: 1_000,
            transaction_size: defaults::transaction_size(),
            duration_secs: 60,
        }
    }
}

impl BenchmarkParameters {
    /// Load benchmark parameters from a YAML file.
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        let path = path.as_ref();
        let raw = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read parameters file {}", path.display()))?;
        serde_yaml::from_str(&raw).context("failed to parse benchmark parameters YAML")
    }
}

impl fmt::Display for BenchmarkParameters {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} nodes, {} tx/s of {} B, for {}s",
            self.nodes, self.load_tps, self.transaction_size, self.duration_secs
        )
    }
}

mod defaults {
    pub fn base_port() -> u16 {
        8000
    }

    pub fn transaction_size() -> u64 {
        512
    }
}
