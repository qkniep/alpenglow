// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Orchestrator for deploying Alpenglow instances in the cloud.
//!
//! Currently, the orchestrator supports the following cloud providers:
//! - [AWS](https://aws.amazon.com/)
//! - [Vultr](https://www.vultr.com/)

mod client;

pub use client::aws::AwsClient;
pub use client::vultr::VultrClient;
