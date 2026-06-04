// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Testbed settings loaded from a YAML file.
//!
//! A single settings file fully describes a testbed: which cloud provider to
//! use, where the SSH keys live, which regions to spread machines across, and
//! which git revision of Alpenglow to build. `${ENV_VAR}` references in the
//! file are expanded from the environment before parsing, so secrets (API
//! tokens) never need to be written to disk.

use std::fs;
use std::net::Ipv4Addr;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};

/// The git repository (and revision) to build on the remote machines.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Repository {
    /// Clone URL, e.g. `https://github.com/qkniep/alpenglow`.
    pub url: String,
    /// Commit hash or branch name to check out. Defaults to `main`.
    #[serde(default = "defaults::commit")]
    pub commit: String,
}

/// One pre-provisioned machine for the [`CloudProvider::Custom`] provider.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CustomInstance {
    /// A user-chosen label that must also appear in [`Settings::regions`].
    pub region: String,
    /// The machine's public IPv4 address.
    pub ip: Ipv4Addr,
}

/// Configuration for the `custom` provider: machines you provisioned yourself.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CustomConfig {
    /// SSH username configured on the machines.
    #[serde(default = "defaults::root_user")]
    pub ssh_username: String,
    /// The pre-provisioned machines (with their region labels).
    pub instances: Vec<CustomInstance>,
}

/// Configuration for the `vultr` provider.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VultrConfig {
    /// Vultr API token. Use `${VULTR_API_TOKEN}` to read it from the env.
    pub token: String,
    /// Plan id (machine type), e.g. `vc2-4c-8gb`.
    ///
    /// List options with `curl -H "Authorization: Bearer $TOKEN" https://api.vultr.com/v2/plans`.
    pub plan: String,
    /// OS id to install (e.g. `1743` = Ubuntu 22.04 x64).
    ///
    /// List options with `curl -H "Authorization: Bearer $TOKEN" https://api.vultr.com/v2/os`.
    pub os_id: u32,
    /// SSH username on freshly created machines (Vultr default: `root`).
    #[serde(default = "defaults::root_user")]
    pub ssh_username: String,
}

/// Configuration for the `aws` provider (not yet implemented).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AwsConfig {
    /// EC2 instance type, e.g. `m5d.8xlarge`.
    pub instance_type: String,
    /// SSH username baked into the AMI (Ubuntu AMIs default to `ubuntu`).
    #[serde(default = "defaults::ubuntu_user")]
    pub ssh_username: String,
}

/// The supported cloud providers, each carrying its own configuration so the
/// type system rules out invalid combinations.
///
/// Internally tagged on a `provider` field, so the YAML reads:
///
/// ```yaml
/// cloud_provider:
///   provider: vultr
///   token: ${VULTR_API_TOKEN}
///   plan: vc2-4c-8gb
///   os_id: 1743
/// ```
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "provider", rename_all = "lowercase")]
pub enum CloudProvider {
    /// Machines you already own; the orchestrator only deploys and runs.
    Custom(CustomConfig),
    /// Vultr cloud instances, provisioned via the Vultr v2 API.
    Vultr(VultrConfig),
    /// AWS EC2 instances (stubbed — see `provider/aws.rs`).
    Aws(AwsConfig),
}

/// Top-level testbed settings.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Settings {
    /// Unique testbed id, so multiple users can share one cloud account.
    pub testbed_id: String,
    /// The cloud provider hosting the testbed, plus its provider-specific config.
    pub cloud_provider: CloudProvider,
    /// Path to the SSH private key used to access the instances.
    pub ssh_private_key_file: PathBuf,
    /// Path to the matching public key. Defaults to `<private_key>.pub`.
    #[serde(default)]
    pub ssh_public_key_file: Option<PathBuf>,
    /// Regions to spread the testbed across (cloud regions, or custom labels).
    pub regions: Vec<String>,
    /// The git repository and revision to build on the instances.
    pub repository: Repository,
    /// Working directory on each remote instance (holds the repo and configs).
    #[serde(default = "defaults::working_dir")]
    pub working_dir: PathBuf,
    /// Local directory where intermediate benchmark artifacts are written.
    #[serde(default = "defaults::results_dir")]
    pub results_dir: PathBuf,
    /// Local directory where node logs are downloaded after a run.
    #[serde(default = "defaults::logs_dir")]
    pub logs_dir: PathBuf,
    /// Base UDP port for node 0; consecutive nodes/sockets count up from here.
    #[serde(default = "defaults::base_port")]
    pub base_port: u16,
    /// SSH connection timeout, in seconds.
    #[serde(default = "defaults::ssh_timeout_secs")]
    pub ssh_timeout_secs: u64,
}

impl Settings {
    /// Load settings from a YAML file, expanding `${ENV}` references first.
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        let path = path.as_ref();
        let raw = fs::read_to_string(path)
            .with_context(|| format!("failed to read settings file {}", path.display()))?;
        let resolved = resolve_env(&raw)?;
        let settings: Settings =
            serde_yaml::from_str(&resolved).context("failed to parse settings YAML")?;
        fs::create_dir_all(&settings.results_dir).ok();
        fs::create_dir_all(&settings.logs_dir).ok();
        Ok(settings)
    }

    /// The SSH username for the configured provider.
    pub fn ssh_username(&self) -> &str {
        match &self.cloud_provider {
            CloudProvider::Custom(c) => &c.ssh_username,
            CloudProvider::Vultr(c) => &c.ssh_username,
            CloudProvider::Aws(c) => &c.ssh_username,
        }
    }

    /// Path to the SSH public key (defaults to `<private_key>.pub`).
    pub fn ssh_public_key_file(&self) -> PathBuf {
        self.ssh_public_key_file.clone().unwrap_or_else(|| {
            let mut p = self.ssh_private_key_file.clone();
            p.set_extension("pub");
            p
        })
    }

    /// Read the SSH public key contents from disk.
    pub fn load_ssh_public_key(&self) -> Result<String> {
        let p = self.ssh_public_key_file();
        let key = fs::read_to_string(&p)
            .with_context(|| format!("failed to read SSH public key {}", p.display()))?;
        Ok(key.trim().to_string())
    }

    /// The repository directory name (last URL path segment, minus `.git`).
    pub fn repository_name(&self) -> String {
        self.repository
            .url
            .trim_end_matches('/')
            .rsplit('/')
            .next()
            .unwrap_or("alpenglow")
            .trim_end_matches(".git")
            .to_string()
    }
}

/// Expand every `${VAR}` in `s` from the process environment.
fn resolve_env(s: &str) -> Result<String> {
    let mut out = s.to_string();
    for (name, value) in std::env::vars() {
        out = out.replace(&format!("${{{name}}}"), &value);
    }
    if let Some(idx) = out.find("${") {
        let end = out.len().min(idx + 40);
        bail!(
            "unresolved environment variable in settings near: {}",
            &out[idx..end]
        );
    }
    Ok(out)
}

mod defaults {
    use std::path::PathBuf;

    pub fn commit() -> String {
        "main".into()
    }

    pub fn root_user() -> String {
        "root".into()
    }

    pub fn ubuntu_user() -> String {
        "ubuntu".into()
    }

    pub fn working_dir() -> PathBuf {
        "~/alpenglow-testbed".into()
    }

    pub fn results_dir() -> PathBuf {
        "./results".into()
    }

    pub fn logs_dir() -> PathBuf {
        "./logs".into()
    }

    pub fn base_port() -> u16 {
        8000
    }

    pub fn ssh_timeout_secs() -> u64 {
        30
    }
}
