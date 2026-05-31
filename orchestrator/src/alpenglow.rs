// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Alpenglow protocol adapter.
//!
//! This is the one piece of the orchestrator that knows about Alpenglow's
//! binaries. It turns a set of [`Instance`]s and [`BenchmarkParameters`] into
//! the shell commands that build, configure, and run the node.
//!
//! ## Genesis is non-deterministic
//!
//! `node --generate-config-files <socket_list> --config-name ag_node` generates
//! **fresh random keypairs** for every validator and writes one
//! `ag_node_<id>.toml` per node, each containing that node's secret keys plus
//! the public gossip list of all nodes. Because the keys are random, genesis
//! must run exactly once; the resulting per-node config is then distributed to
//! the matching machine. See [`crate::testbed::Testbed::run_benchmark`].

use crate::benchmark::BenchmarkParameters;
use crate::provider::Instance;

/// Binary names from the alpenglow crate (`src/bin/*.rs`).
const NODE_BIN: &str = "node";
const CLIENT_BIN: &str = "workload_generator";
/// Base name passed to `--config-name`; per-node files are `ag_node_<id>.toml`.
const CONFIG_BASE: &str = "ag_node";

/// Knows how to build, configure, and run the Alpenglow node over SSH.
pub struct Alpenglow;

impl Alpenglow {
    /// Create the protocol adapter.
    pub fn new() -> Self {
        Self
    }

    /// OS packages required to build and run the node on a fresh Ubuntu box.
    pub fn dependencies(&self) -> &'static [&'static str] {
        &[
            "build-essential",
            "pkg-config",
            "libssl-dev",
            "clang",
            "cmake",
            "git",
            "curl",
        ]
    }

    /// The per-node config file name for validator `id`.
    pub fn config_file(&self, id: usize) -> String {
        format!("{CONFIG_BASE}_{id}.toml")
    }

    /// The socket list fed to `--generate-config-files`: one `ip:port` per
    /// instance, in order, where `port` is the node's all-to-all base port.
    pub fn socket_list(&self, instances: &[Instance], base_port: u16) -> String {
        instances
            .iter()
            .map(|i| format!("{}:{base_port}", i.main_ip))
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Command to clone and build the node + workload generator in `repo_dir`.
    pub fn build_command(&self, repo_dir: &str) -> String {
        format!(
            "cd {repo_dir} && ~/.cargo/bin/cargo build --release \
             --bin {NODE_BIN} --bin {CLIENT_BIN}"
        )
    }

    /// Command (run once, in `repo_dir`) to generate all per-node config files
    /// from a socket list already uploaded as `socket_file`.
    pub fn genesis_command(&self, repo_dir: &str, socket_file: &str) -> String {
        format!(
            "cd {repo_dir} && ./target/release/{NODE_BIN} \
             --generate-config-files {socket_file} --config-name {CONFIG_BASE}"
        )
    }

    /// Command to start validator `id` in the background, logging to `log_file`.
    pub fn node_command(&self, repo_dir: &str, id: usize, log_file: &str) -> String {
        let config = self.config_file(id);
        format!(
            "cd {repo_dir} && RUST_LOG=alpenglow=info nohup \
             ./target/release/{NODE_BIN} --config-name {config} \
             > {log_file} 2>&1 < /dev/null &"
        )
    }

    /// Command to start the load generator against `target`, in the background.
    pub fn client_command(
        &self,
        repo_dir: &str,
        target: &Instance,
        params: &BenchmarkParameters,
        log_file: &str,
    ) -> String {
        // The node listens for transactions on its base port + 4 (see node.rs).
        let tx_port = params.base_port + 4;
        format!(
            "cd {repo_dir} && nohup ./target/release/{CLIENT_BIN} \
             --validator {}:{tx_port} \
             --transactions-per-second {} --transaction-size {} \
             > {log_file} 2>&1 < /dev/null &",
            target.main_ip, params.load_tps, params.transaction_size
        )
    }

    /// Command to stop every node and load generator on a machine.
    pub fn stop_command(&self) -> String {
        format!("pkill -f 'target/release/{NODE_BIN}'; pkill -f {CLIENT_BIN}; true")
    }
}

impl Default for Alpenglow {
    fn default() -> Self {
        Self::new()
    }
}
