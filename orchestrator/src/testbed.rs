// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! High-level testbed lifecycle: deploy, install, benchmark, tear down.
//!
//! [`Testbed`] is the glue between the [provider](crate::provider), the
//! [SSH layer](crate::ssh), and the [Alpenglow adapter](crate::alpenglow). The
//! `orchestrator` binary is a thin CLI over the methods here.

use anyhow::{Context, Result, bail};
use futures::future::join_all;
use tokio::time::{Duration, sleep};

use crate::alpenglow::Alpenglow;
use crate::benchmark::BenchmarkParameters;
use crate::provider::{CloudClient, Instance, ServerProviderClient};
use crate::settings::Settings;
use crate::ssh::Ssh;

/// Owns a testbed and drives its lifecycle.
pub struct Testbed {
    settings: Settings,
    client: CloudClient,
    ssh: Ssh,
    protocol: Alpenglow,
}

impl Testbed {
    /// Build a testbed from loaded settings.
    pub fn new(settings: Settings) -> Result<Self> {
        let client = CloudClient::from_settings(&settings)?;
        let ssh = Ssh::new(
            settings.ssh_username().to_string(),
            settings.ssh_private_key_file.clone(),
            settings.ssh_timeout_secs,
        );
        Ok(Self {
            settings,
            client,
            ssh,
            protocol: Alpenglow::new(),
        })
    }

    /// All instances known to the provider for this testbed.
    async fn all_instances(&self) -> Result<Vec<Instance>> {
        self.client.list_instances().await
    }

    /// Active instances whose region is part of this testbed.
    async fn active_instances(&self) -> Result<Vec<Instance>> {
        Ok(self
            .all_instances()
            .await?
            .into_iter()
            .filter(|i| i.is_active() && self.settings.regions.contains(&i.region))
            .collect())
    }

    /// Print the current status of every instance in the testbed.
    pub async fn status(&self) -> Result<()> {
        let instances = self.all_instances().await?;
        println!(
            "Testbed '{}' — {} instance(s):",
            self.settings.testbed_id,
            instances.len()
        );
        for i in &instances {
            println!(
                "  [{:>14}] {:<14} {:<15} {:?}",
                i.region, i.id, i.main_ip, i.status
            );
        }
        Ok(())
    }

    /// Provision `instances_per_region` machines in each configured region.
    pub async fn deploy(&self, instances_per_region: usize) -> Result<()> {
        let public_key = self.settings.load_ssh_public_key()?;
        self.client
            .register_ssh_public_key(&public_key)
            .await
            .context("registering SSH public key with the provider")?;

        for region in &self.settings.regions {
            for n in 0..instances_per_region {
                let instance = self
                    .client
                    .create_instance(region)
                    .await
                    .with_context(|| format!("creating instance {n} in {region}"))?;
                println!("created instance {} in {region}", instance.id);
            }
        }
        println!(
            "deploy complete; wait for instances to boot, then run `install` \
             (and ensure your firewall allows UDP {}..{} and TCP 22)",
            self.settings.base_port,
            self.settings.base_port + 4,
        );
        Ok(())
    }

    /// Power on every instance.
    pub async fn start(&self) -> Result<()> {
        let instances = self.all_instances().await?;
        self.client.start_instances(&instances).await
    }

    /// Power off every instance.
    pub async fn stop(&self) -> Result<()> {
        let instances = self.all_instances().await?;
        self.client.stop_instances(&instances).await
    }

    /// Delete every instance in the testbed.
    pub async fn destroy(&self) -> Result<()> {
        for instance in self.all_instances().await? {
            self.client.delete_instance(&instance).await?;
            println!("deleted instance {}", instance.id);
        }
        Ok(())
    }

    /// Install dependencies and build the node on every active instance.
    pub async fn install(&self) -> Result<()> {
        let instances = self.active_instances().await?;
        if instances.is_empty() {
            bail!("no active instances; run `deploy` first (or check `regions`)");
        }

        let deps = self.protocol.dependencies().join(" ");
        let repo = &self.settings.repository;
        let repo_dir = self.settings.repository_name();
        let setup = self.client.setup_commands().await?;

        // One chained command keeps the whole install atomic per machine.
        let mut steps = setup;
        steps.push(format!(
            "sudo apt-get update -y && \
             sudo DEBIAN_FRONTEND=noninteractive apt-get install -y {deps}"
        ));
        steps.push(
            "command -v cargo >/dev/null 2>&1 || \
             (curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y)"
                .to_string(),
        );
        steps.push(format!(
            "rm -rf {repo_dir} && git clone {} {repo_dir}",
            repo.url
        ));
        steps.push(format!("cd {repo_dir} && git checkout {}", repo.commit));
        steps.push(self.protocol.build_command(&repo_dir));
        let command = steps.join(" && ");

        println!("installing on {} instance(s)...", instances.len());
        self.run_on_all(&instances, &command).await?;
        println!("install complete");
        Ok(())
    }

    /// Run one benchmark: genesis, distribute configs, start nodes + load, wait,
    /// stop, and download logs.
    pub async fn run_benchmark(&self, params: &BenchmarkParameters) -> Result<()> {
        let mut instances = self.active_instances().await?;
        if instances.len() < params.nodes {
            bail!(
                "benchmark needs {} nodes but only {} active instance(s) are available",
                params.nodes,
                instances.len()
            );
        }
        instances.truncate(params.nodes);
        let repo_dir = self.settings.repository_name();
        println!("running benchmark: {params}");

        // 1. Generate all configs on the first instance (genesis host).
        let genesis = instances[0].clone();
        let socket_list = self.protocol.socket_list(&instances, params.base_port);
        let local_sockets = self.settings.results_dir.join("sockets.txt");
        std::fs::write(&local_sockets, &socket_list)
            .with_context(|| format!("writing {}", local_sockets.display()))?;
        let remote_sockets = format!("{repo_dir}/sockets.txt");
        self.ssh
            .upload(genesis.main_ip, &local_sockets, &remote_sockets)
            .await?;
        self.ssh
            .execute(
                genesis.main_ip,
                &self.protocol.genesis_command(&repo_dir, "sockets.txt"),
            )
            .await
            .context("generating node configs on the genesis host")?;

        // 2. Pull each per-node config back and push it to the matching node.
        for (id, instance) in instances.iter().enumerate() {
            let config = self.protocol.config_file(id);
            let local_cfg = self.settings.results_dir.join(&config);
            self.ssh
                .download(genesis.main_ip, &format!("{repo_dir}/{config}"), &local_cfg)
                .await?;
            if instance.main_ip != genesis.main_ip {
                self.ssh
                    .upload(
                        instance.main_ip,
                        &local_cfg,
                        &format!("{repo_dir}/{config}"),
                    )
                    .await?;
            }
        }

        // 3. Start every node.
        for (id, instance) in instances.iter().enumerate() {
            let command = self
                .protocol
                .node_command(&repo_dir, id, &format!("node-{id}.log"));
            self.ssh
                .execute(instance.main_ip, &command)
                .await
                .with_context(|| format!("starting node {id}"))?;
        }
        println!("started {} node(s)", instances.len());

        // 4. Start the load generator (collocated with node 0).
        let client_command =
            self.protocol
                .client_command(&repo_dir, &instances[0], params, "client.log");
        self.ssh
            .execute(instances[0].main_ip, &client_command)
            .await
            .context("starting the load generator")?;

        // 5. Let it run.
        println!("benchmark running for {}s...", params.duration_secs);
        sleep(Duration::from_secs(params.duration_secs)).await;

        // 6. Stop everything.
        self.run_on_all(&instances, &self.protocol.stop_command())
            .await
            .context("stopping nodes")?;

        // 7. Download logs (best effort).
        for (id, instance) in instances.iter().enumerate() {
            let remote = format!("{repo_dir}/node-{id}.log");
            let local = self.settings.logs_dir.join(format!("node-{id}.log"));
            if let Err(e) = self.ssh.download(instance.main_ip, &remote, &local).await {
                eprintln!("warning: failed to download {remote}: {e}");
            }
        }
        println!(
            "benchmark complete; logs in {}",
            self.settings.logs_dir.display()
        );
        Ok(())
    }

    /// Run the same command on every instance concurrently, failing if any fails.
    async fn run_on_all(&self, instances: &[Instance], command: &str) -> Result<()> {
        let futures = instances
            .iter()
            .map(|i| async move { self.ssh.execute(i.main_ip, command).await.map(drop) });
        for result in join_all(futures).await {
            result?;
        }
        Ok(())
    }
}
