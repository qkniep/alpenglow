// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! `orchestrator` — a CLI for running real-world Alpenglow benchmarks on a
//! cloud testbed. See the crate `README.md` for the end-to-end workflow.

use anyhow::Result;
use clap::{Parser, Subcommand};
use orchestrator::benchmark::BenchmarkParameters;
use orchestrator::settings::Settings;
use orchestrator::testbed::Testbed;

#[derive(Parser)]
#[command(version, about = "Cloud benchmark orchestrator for Alpenglow")]
struct Cli {
    /// Path to the settings YAML file.
    #[arg(long, default_value = "orchestrator/assets/settings.yml")]
    settings: String,
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Show the status of every instance in the testbed.
    Status,
    /// Provision new instances (one batch per configured region).
    Deploy {
        /// Number of instances to create in each region.
        #[arg(long, default_value_t = 1)]
        instances_per_region: usize,
    },
    /// Power on all instances in the testbed.
    Start,
    /// Power off all instances in the testbed.
    Stop,
    /// Delete all instances in the testbed.
    Destroy,
    /// Install dependencies and build the node on every active instance.
    Install,
    /// Run a benchmark against the active instances.
    Benchmark {
        /// Load benchmark parameters from a YAML file.
        #[arg(long)]
        parameters: Option<String>,
        /// Override the number of nodes.
        #[arg(long)]
        nodes: Option<usize>,
        /// Override the target transactions per second.
        #[arg(long)]
        load: Option<u64>,
        /// Override the benchmark duration, in seconds.
        #[arg(long)]
        duration: Option<u64>,
    },
}

#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<()> {
    let cli = Cli::parse();
    let settings = Settings::load(&cli.settings)?;
    let testbed = Testbed::new(settings)?;

    match cli.command {
        Command::Status => testbed.status().await?,
        Command::Deploy {
            instances_per_region,
        } => testbed.deploy(instances_per_region).await?,
        Command::Start => testbed.start().await?,
        Command::Stop => testbed.stop().await?,
        Command::Destroy => testbed.destroy().await?,
        Command::Install => testbed.install().await?,
        Command::Benchmark {
            parameters,
            nodes,
            load,
            duration,
        } => {
            let mut params = match parameters {
                Some(path) => BenchmarkParameters::load(path)?,
                None => BenchmarkParameters::default(),
            };
            if let Some(n) = nodes {
                params.nodes = n;
            }
            if let Some(l) = load {
                params.load_tps = l;
            }
            if let Some(d) = duration {
                params.duration_secs = d;
            }
            testbed.run_benchmark(&params).await?;
        }
    }

    Ok(())
}
