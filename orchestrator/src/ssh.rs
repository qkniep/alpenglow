// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! A thin SSH/SCP layer that shells out to the system `ssh` and `scp` binaries.
//!
//! Shelling out (rather than linking an in-process SSH library) keeps the
//! dependency tree small and the behaviour transparent — every command the
//! orchestrator runs is a plain `ssh user@host '<cmd>'` you could reproduce by
//! hand. It does assume `ssh`/`scp` are on `PATH`, which they are on every
//! platform the orchestrator targets.

use std::net::Ipv4Addr;
use std::path::{Path, PathBuf};
use std::process::Output;

use anyhow::{Context, Result, bail};
use tokio::process::Command;

/// Runs commands and copies files over SSH using a fixed key and username.
pub struct Ssh {
    username: String,
    private_key: PathBuf,
    connect_timeout_secs: u64,
}

impl Ssh {
    /// Build an SSH driver for the given user, key, and connect timeout.
    pub fn new(
        username: impl Into<String>,
        private_key: impl Into<PathBuf>,
        connect_timeout_secs: u64,
    ) -> Self {
        Self {
            username: username.into(),
            private_key: private_key.into(),
            connect_timeout_secs,
        }
    }

    /// Common `-o`/`-i` options shared by `ssh` and `scp`.
    ///
    /// Host-key checking is disabled because testbed machines are freshly
    /// provisioned every run and their host keys are never known ahead of time.
    fn common_opts(&self, cmd: &mut Command) {
        cmd.arg("-o")
            .arg("StrictHostKeyChecking=no")
            .arg("-o")
            .arg("UserKnownHostsFile=/dev/null")
            .arg("-o")
            .arg("LogLevel=ERROR")
            .arg("-o")
            .arg(format!("ConnectTimeout={}", self.connect_timeout_secs))
            .arg("-i")
            .arg(&self.private_key);
    }

    fn target(&self, host: Ipv4Addr) -> String {
        format!("{}@{}", self.username, host)
    }

    /// Run a command on `host`, returning its stdout on success.
    pub async fn execute(&self, host: Ipv4Addr, command: &str) -> Result<String> {
        let mut cmd = Command::new("ssh");
        self.common_opts(&mut cmd);
        cmd.arg(self.target(host)).arg(command);
        let output = cmd
            .output()
            .await
            .with_context(|| format!("failed to spawn ssh to {host}"))?;
        check(output, &format!("ssh {host}: {command}"))
    }

    /// Upload a local file to `remote_path` on `host`.
    pub async fn upload(&self, host: Ipv4Addr, local: &Path, remote_path: &str) -> Result<()> {
        let mut cmd = Command::new("scp");
        self.common_opts(&mut cmd);
        cmd.arg(local)
            .arg(format!("{}:{remote_path}", self.target(host)));
        let output = cmd
            .output()
            .await
            .with_context(|| format!("failed to spawn scp upload to {host}"))?;
        check(output, &format!("scp upload to {host}:{remote_path}")).map(drop)
    }

    /// Download `remote_path` from `host` to a local file.
    pub async fn download(&self, host: Ipv4Addr, remote_path: &str, local: &Path) -> Result<()> {
        let mut cmd = Command::new("scp");
        self.common_opts(&mut cmd);
        cmd.arg(format!("{}:{remote_path}", self.target(host)))
            .arg(local);
        let output = cmd
            .output()
            .await
            .with_context(|| format!("failed to spawn scp download from {host}"))?;
        check(output, &format!("scp download from {host}:{remote_path}")).map(drop)
    }
}

/// Turn a process `Output` into a `Result`, surfacing stderr on failure.
fn check(output: Output, context: &str) -> Result<String> {
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("{context} failed: {}", stderr.trim());
    }
}
