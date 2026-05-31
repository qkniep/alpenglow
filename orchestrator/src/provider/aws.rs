// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! AWS EC2 provider — **stub**.
//!
//! This module implements [`ServerProviderClient`] so the rest of the
//! orchestrator compiles and type-checks against AWS, but every lifecycle
//! method returns an error pointing here. To flesh it out, add the
//! `aws-config` + `aws-sdk-ec2` crates and implement the methods using
//! `RunInstances` / `DescribeInstances` / `TerminateInstances`, mirroring the
//! [Mysticeti AWS provider]. Note the cargo-deny license allowlist in
//! `../../deny.toml` may need new SPDX ids once the AWS SDK tree is pulled in.
//!
//! [Mysticeti AWS provider]: https://github.com/asonnino/mysticeti/blob/main/crates/orchestrator/src/provider/aws.rs

use anyhow::{Result, bail};

use crate::provider::{Instance, ServerProviderClient};
use crate::settings::AwsConfig;

/// Stub AWS EC2 client.
pub struct AwsClient {
    username: String,
    instance_type: String,
}

impl AwsClient {
    /// Build the (stub) client from the `aws` provider config.
    pub fn new(config: &AwsConfig) -> Self {
        Self {
            username: config.ssh_username.clone(),
            instance_type: config.instance_type.clone(),
        }
    }
}

/// Single source of the "not implemented" error so every method stays one line.
fn unimplemented(what: &str) -> anyhow::Error {
    anyhow::anyhow!("AWS provider: {what} is not implemented yet (see provider/aws.rs)")
}

impl ServerProviderClient for AwsClient {
    fn username(&self) -> &str {
        &self.username
    }

    async fn list_instances(&self) -> Result<Vec<Instance>> {
        bail!(unimplemented(&format!(
            "list_instances (instance_type={})",
            self.instance_type
        )))
    }

    async fn start_instances(&self, _instances: &[Instance]) -> Result<()> {
        bail!(unimplemented("start_instances"))
    }

    async fn stop_instances(&self, _instances: &[Instance]) -> Result<()> {
        bail!(unimplemented("stop_instances"))
    }

    async fn create_instance(&self, _region: &str) -> Result<Instance> {
        bail!(unimplemented("create_instance"))
    }

    async fn delete_instance(&self, _instance: &Instance) -> Result<()> {
        bail!(unimplemented("delete_instance"))
    }

    async fn register_ssh_public_key(&self, _public_key: &str) -> Result<()> {
        bail!(unimplemented("register_ssh_public_key"))
    }

    async fn setup_commands(&self) -> Result<Vec<String>> {
        // No-op is harmless even for the stub: lets `install` proceed if a user
        // wires AWS instances in via the custom provider.
        Ok(Vec::new())
    }
}
