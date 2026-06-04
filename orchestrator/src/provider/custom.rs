// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! "Custom" provider: machines the user provisioned themselves.
//!
//! There is nothing to create or destroy — the instances come straight from the
//! settings file. The deploy/install/benchmark flow works end-to-end against
//! them, which makes this the quickest path to a first real-world run (and a
//! handy way to test the orchestrator without a cloud account).

use anyhow::{Result, bail};

use crate::provider::{Instance, InstanceStatus, ServerProviderClient};
use crate::settings::CustomConfig;

/// A provider backed by a static list of pre-provisioned machines.
pub struct CustomClient {
    username: String,
    instances: Vec<Instance>,
}

impl CustomClient {
    /// Build the client from the `custom` provider config.
    pub fn new(config: &CustomConfig) -> Self {
        let instances = config
            .instances
            .iter()
            .enumerate()
            .map(|(i, ci)| Instance {
                id: format!("custom-{i}"),
                region: ci.region.clone(),
                main_ip: ci.ip,
                tags: Vec::new(),
                specs: "custom".to_string(),
                status: InstanceStatus::Active,
            })
            .collect();
        Self {
            username: config.ssh_username.clone(),
            instances,
        }
    }
}

impl ServerProviderClient for CustomClient {
    fn username(&self) -> &str {
        &self.username
    }

    async fn list_instances(&self) -> Result<Vec<Instance>> {
        Ok(self.instances.clone())
    }

    async fn start_instances(&self, _instances: &[Instance]) -> Result<()> {
        // The user manages power state for their own machines.
        Ok(())
    }

    async fn stop_instances(&self, _instances: &[Instance]) -> Result<()> {
        Ok(())
    }

    async fn create_instance(&self, _region: &str) -> Result<Instance> {
        bail!(
            "the custom provider cannot provision machines; \
             list them under `cloud_provider.custom.instances` in the settings file"
        )
    }

    async fn delete_instance(&self, _instance: &Instance) -> Result<()> {
        bail!("the custom provider does not delete machines it does not own")
    }

    async fn register_ssh_public_key(&self, _public_key: &str) -> Result<()> {
        // Assumed already authorized on the user's machines.
        Ok(())
    }

    async fn setup_commands(&self) -> Result<Vec<String>> {
        Ok(Vec::new())
    }
}
