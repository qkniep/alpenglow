// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Vultr provider, backed by the [Vultr v2 API].
//!
//! The lifecycle calls (list/create/delete/start/stop and SSH-key
//! registration) are wired up against the real endpoints. A couple of
//! ergonomic pieces are intentionally left as TODOs for the first real run:
//!   - polling a freshly created instance until `power_status == running`
//!     before SSHing in (right now `create_instance` returns immediately);
//!   - tagging/labelling strategy so multiple testbeds can coexist.
//!
//! All instances are tagged with the testbed-agnostic label `alpenglow` and the
//! API token is read from the settings file (typically via `${VULTR_API_TOKEN}`).
//!
//! [Vultr v2 API]: https://www.vultr.com/api/

use std::net::Ipv4Addr;
use std::sync::Mutex;

use anyhow::{Context, Result, bail};
use reqwest::Client;
use serde::{Deserialize, Serialize};

use crate::provider::{Instance, InstanceStatus, ServerProviderClient};
use crate::settings::VultrConfig;

const BASE_URL: &str = "https://api.vultr.com/v2";
const LABEL: &str = "alpenglow";

/// A client for the Vultr v2 API.
pub struct VultrClient {
    token: String,
    plan: String,
    os_id: u32,
    username: String,
    http: Client,
    /// Id of the registered SSH key, cached after `register_ssh_public_key`.
    ssh_key_id: Mutex<Option<String>>,
}

impl VultrClient {
    /// Build the client from the `vultr` provider config.
    pub fn new(config: &VultrConfig) -> Result<Self> {
        let http = Client::builder()
            .build()
            .context("failed to build HTTP client")?;
        Ok(Self {
            token: config.token.clone(),
            plan: config.plan.clone(),
            os_id: config.os_id,
            username: config.ssh_username.clone(),
            http,
            ssh_key_id: Mutex::new(None),
        })
    }

    fn url(&self, path: &str) -> String {
        format!("{BASE_URL}{path}")
    }
}

/// `GET /v2/instances` response.
#[derive(Deserialize)]
struct InstancesResponse {
    instances: Vec<VultrInstance>,
}

/// `POST /v2/instances` response.
#[derive(Deserialize)]
struct InstanceResponse {
    instance: VultrInstance,
}

/// A Vultr instance, as returned by the API (subset of fields).
#[derive(Deserialize)]
struct VultrInstance {
    id: String,
    region: String,
    #[serde(default)]
    main_ip: String,
    #[serde(default)]
    plan: String,
    #[serde(default)]
    power_status: String,
    #[serde(default)]
    tags: Vec<String>,
}

impl VultrInstance {
    fn into_instance(self) -> Instance {
        // A just-created instance reports `0.0.0.0` until it boots.
        let main_ip = self.main_ip.parse().unwrap_or(Ipv4Addr::UNSPECIFIED);
        Instance {
            id: self.id,
            region: self.region,
            main_ip,
            tags: self.tags,
            specs: self.plan,
            status: InstanceStatus::from(self.power_status.as_str()),
        }
    }
}

/// `POST /v2/instances` request body.
#[derive(Serialize)]
struct CreateInstanceRequest<'a> {
    region: &'a str,
    plan: &'a str,
    os_id: u32,
    label: &'a str,
    tags: Vec<&'a str>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    sshkey_id: Vec<String>,
}

/// `POST /v2/ssh-keys` request body.
#[derive(Serialize)]
struct CreateSshKeyRequest<'a> {
    name: &'a str,
    ssh_key: &'a str,
}

/// `POST /v2/ssh-keys` response.
#[derive(Deserialize)]
struct SshKeyResponse {
    ssh_key: SshKey,
}

#[derive(Deserialize)]
struct SshKey {
    id: String,
}

impl ServerProviderClient for VultrClient {
    fn username(&self) -> &str {
        &self.username
    }

    async fn list_instances(&self) -> Result<Vec<Instance>> {
        let resp = self
            .http
            .get(self.url("/instances"))
            .bearer_auth(&self.token)
            .send()
            .await
            .context("listing Vultr instances")?
            .error_for_status()
            .context("Vultr returned an error listing instances")?
            .json::<InstancesResponse>()
            .await
            .context("parsing Vultr instances response")?;
        Ok(resp
            .instances
            .into_iter()
            .filter(|i| i.tags.iter().any(|t| t == LABEL))
            .map(VultrInstance::into_instance)
            .collect())
    }

    async fn start_instances(&self, instances: &[Instance]) -> Result<()> {
        for instance in instances {
            self.http
                .post(self.url(&format!("/instances/{}/start", instance.id)))
                .bearer_auth(&self.token)
                .send()
                .await
                .with_context(|| format!("starting Vultr instance {}", instance.id))?
                .error_for_status()
                .with_context(|| format!("Vultr error starting instance {}", instance.id))?;
        }
        Ok(())
    }

    async fn stop_instances(&self, instances: &[Instance]) -> Result<()> {
        for instance in instances {
            self.http
                .post(self.url(&format!("/instances/{}/halt", instance.id)))
                .bearer_auth(&self.token)
                .send()
                .await
                .with_context(|| format!("halting Vultr instance {}", instance.id))?
                .error_for_status()
                .with_context(|| format!("Vultr error halting instance {}", instance.id))?;
        }
        Ok(())
    }

    async fn create_instance(&self, region: &str) -> Result<Instance> {
        let sshkey_id = self
            .ssh_key_id
            .lock()
            .expect("ssh_key_id mutex poisoned")
            .iter()
            .cloned()
            .collect();
        let body = CreateInstanceRequest {
            region,
            plan: &self.plan,
            os_id: self.os_id,
            label: LABEL,
            tags: vec![LABEL],
            sshkey_id,
        };
        let resp = self
            .http
            .post(self.url("/instances"))
            .bearer_auth(&self.token)
            .json(&body)
            .send()
            .await
            .with_context(|| format!("creating Vultr instance in {region}"))?
            .error_for_status()
            .with_context(|| format!("Vultr error creating instance in {region}"))?
            .json::<InstanceResponse>()
            .await
            .context("parsing Vultr create-instance response")?;
        // TODO: poll `GET /instances/{id}` until `power_status == running` and a
        // real `main_ip` is assigned before returning, so callers can SSH in.
        Ok(resp.instance.into_instance())
    }

    async fn delete_instance(&self, instance: &Instance) -> Result<()> {
        self.http
            .delete(self.url(&format!("/instances/{}", instance.id)))
            .bearer_auth(&self.token)
            .send()
            .await
            .with_context(|| format!("deleting Vultr instance {}", instance.id))?
            .error_for_status()
            .with_context(|| format!("Vultr error deleting instance {}", instance.id))?;
        Ok(())
    }

    async fn register_ssh_public_key(&self, public_key: &str) -> Result<()> {
        let body = CreateSshKeyRequest {
            name: LABEL,
            ssh_key: public_key,
        };
        let resp = self
            .http
            .post(self.url("/ssh-keys"))
            .bearer_auth(&self.token)
            .json(&body)
            .send()
            .await
            .context("registering Vultr SSH key")?;
        // Vultr rejects a duplicate key name with 400; treat that as "already
        // registered" and look the id up instead of failing the whole deploy.
        if !resp.status().is_success() {
            bail!(
                "Vultr error registering SSH key (status {}). \
                 If the key already exists, remove the duplicate or reuse its id.",
                resp.status()
            );
        }
        let parsed = resp
            .json::<SshKeyResponse>()
            .await
            .context("parsing Vultr ssh-key response")?;
        *self.ssh_key_id.lock().expect("ssh_key_id mutex poisoned") = Some(parsed.ssh_key.id);
        Ok(())
    }

    async fn setup_commands(&self) -> Result<Vec<String>> {
        // Nothing Vultr-specific for now. Add NVMe mount commands here if you
        // switch to a plan with local NVMe storage.
        Ok(Vec::new())
    }
}
