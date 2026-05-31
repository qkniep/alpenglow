// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Cloud-provider abstraction.
//!
//! Every supported provider implements [`ServerProviderClient`]; the
//! [`CloudClient`] enum dispatches to the right one at runtime based on the
//! loaded [`Settings`]. Adding a provider means implementing the trait and
//! wiring a new enum variant — nothing else in the orchestrator changes.

use std::net::{Ipv4Addr, SocketAddr};

use anyhow::Result;
use serde::{Deserialize, Serialize};

use crate::settings::{CloudProvider, Settings};

pub mod aws;
pub mod custom;
pub mod vultr;

/// The lifecycle state of a cloud instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum InstanceStatus {
    /// Running and reachable.
    Active,
    /// Provisioned but not running (e.g. stopped/halted, or still booting).
    Inactive,
    /// Being deleted.
    Terminated,
}

impl From<&str> for InstanceStatus {
    fn from(s: &str) -> Self {
        match s.to_lowercase().as_str() {
            "running" | "active" | "ok" => Self::Active,
            "terminated" | "destroying" => Self::Terminated,
            _ => Self::Inactive,
        }
    }
}

/// A single cloud-provider instance.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Instance {
    /// Provider-specific unique id.
    pub id: String,
    /// The region the instance runs in.
    pub region: String,
    /// Public IPv4 address (reachable from anywhere).
    pub main_ip: Ipv4Addr,
    /// Provider tags associated with the instance.
    pub tags: Vec<String>,
    /// Human-readable machine specs (instance type / plan).
    pub specs: String,
    /// Current lifecycle status.
    pub status: InstanceStatus,
}

impl Instance {
    /// Whether the instance is running and reachable.
    pub fn is_active(&self) -> bool {
        matches!(self.status, InstanceStatus::Active)
    }

    /// The SSH endpoint (port 22) for the instance.
    pub fn ssh_address(&self) -> SocketAddr {
        SocketAddr::new(self.main_ip.into(), 22)
    }
}

/// The minimum interface a cloud provider must implement.
///
/// The futures are not required to be `Send`: the orchestrator runs on a
/// single-threaded tokio runtime and only ever drives these concurrently via
/// `futures::join_all` on one task.
#[allow(async_fn_in_trait)]
pub trait ServerProviderClient {
    /// The SSH username used to connect to instances from this provider.
    fn username(&self) -> &str;

    /// List all instances belonging to this testbed (any status).
    async fn list_instances(&self) -> Result<Vec<Instance>>;

    /// Power on the given instances.
    async fn start_instances(&self, instances: &[Instance]) -> Result<()>;

    /// Power off the given instances (may still incur charges).
    async fn stop_instances(&self, instances: &[Instance]) -> Result<()>;

    /// Provision a new instance in the given region.
    async fn create_instance(&self, region: &str) -> Result<Instance>;

    /// Delete an instance, so it stops incurring charges.
    async fn delete_instance(&self, instance: &Instance) -> Result<()>;

    /// Register an SSH public key so newly created instances grant it access.
    async fn register_ssh_public_key(&self, public_key: &str) -> Result<()>;

    /// Provider-specific commands to prepare a fresh instance (e.g. mount NVMe).
    async fn setup_commands(&self) -> Result<Vec<String>>;
}

/// Runtime dispatch over every supported provider.
pub enum CloudClient {
    /// Bring-your-own pre-provisioned machines.
    Custom(custom::CustomClient),
    /// Vultr cloud instances.
    Vultr(vultr::VultrClient),
    /// AWS EC2 instances (stub).
    Aws(aws::AwsClient),
}

impl CloudClient {
    /// Build the right provider client from the loaded settings.
    pub fn from_settings(settings: &Settings) -> Result<Self> {
        Ok(match &settings.cloud_provider {
            CloudProvider::Custom(c) => Self::Custom(custom::CustomClient::new(c)),
            CloudProvider::Vultr(c) => Self::Vultr(vultr::VultrClient::new(c)?),
            CloudProvider::Aws(c) => Self::Aws(aws::AwsClient::new(c)),
        })
    }
}

impl ServerProviderClient for CloudClient {
    fn username(&self) -> &str {
        match self {
            Self::Custom(c) => c.username(),
            Self::Vultr(c) => c.username(),
            Self::Aws(c) => c.username(),
        }
    }

    async fn list_instances(&self) -> Result<Vec<Instance>> {
        match self {
            Self::Custom(c) => c.list_instances().await,
            Self::Vultr(c) => c.list_instances().await,
            Self::Aws(c) => c.list_instances().await,
        }
    }

    async fn start_instances(&self, instances: &[Instance]) -> Result<()> {
        match self {
            Self::Custom(c) => c.start_instances(instances).await,
            Self::Vultr(c) => c.start_instances(instances).await,
            Self::Aws(c) => c.start_instances(instances).await,
        }
    }

    async fn stop_instances(&self, instances: &[Instance]) -> Result<()> {
        match self {
            Self::Custom(c) => c.stop_instances(instances).await,
            Self::Vultr(c) => c.stop_instances(instances).await,
            Self::Aws(c) => c.stop_instances(instances).await,
        }
    }

    async fn create_instance(&self, region: &str) -> Result<Instance> {
        match self {
            Self::Custom(c) => c.create_instance(region).await,
            Self::Vultr(c) => c.create_instance(region).await,
            Self::Aws(c) => c.create_instance(region).await,
        }
    }

    async fn delete_instance(&self, instance: &Instance) -> Result<()> {
        match self {
            Self::Custom(c) => c.delete_instance(instance).await,
            Self::Vultr(c) => c.delete_instance(instance).await,
            Self::Aws(c) => c.delete_instance(instance).await,
        }
    }

    async fn register_ssh_public_key(&self, public_key: &str) -> Result<()> {
        match self {
            Self::Custom(c) => c.register_ssh_public_key(public_key).await,
            Self::Vultr(c) => c.register_ssh_public_key(public_key).await,
            Self::Aws(c) => c.register_ssh_public_key(public_key).await,
        }
    }

    async fn setup_commands(&self) -> Result<Vec<String>> {
        match self {
            Self::Custom(c) => c.setup_commands().await,
            Self::Vultr(c) => c.setup_commands().await,
            Self::Aws(c) => c.setup_commands().await,
        }
    }
}
