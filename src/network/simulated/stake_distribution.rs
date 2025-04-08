// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Utilities for working with the stake distribution of Solana mainnet.
//!
//! Validator data is taken from [Validators.app](https://validators.app/).
//! The data is stored in the `data/mainnet_validators_validatorsdotapp.json` file.
//! It contains all validators (i.e. nodes with non-zero stake) on Solana mainnet.
//!
//! # Examples
//!
//! ```
//! use alpenglow::network::simulated::stake_distribution::VALIDATOR_DATA;
//!
//! let mut stakes = Vec::new();
//! for validator in VALIDATOR_DATA.iter() {
//!     if validator.is_active && validator.delinquent == Some(false) {
//!         stakes.push(validator.active_stake.unwrap());
//!     }
//! }
//! ```

use std::fs::File;
use std::sync::LazyLock;

use crate::Stake;

pub static VALIDATOR_DATA: LazyLock<Vec<ValidatorData>> = LazyLock::new(|| {
    let file = File::open("data/mainnet_validators_validatorsdotapp.json").unwrap();
    let validators: Vec<ValidatorData> = serde_json::from_reader(file).unwrap();
    validators
});

#[derive(Clone, Debug, serde::Deserialize)]
pub struct ValidatorData {
    pub network: String,
    pub account: String,
    pub name: Option<String>,
    pub keybase_id: Option<String>,
    pub www_url: Option<String>,
    pub details: Option<String>,
    pub avatar_url: Option<String>,
    // "created_at": "2024-08-26 17:31:03 UTC",
    pub created_at: String,
    // "updated_at": "2024-10-22 03:35:05 UTC",
    pub updated_at: String,
    pub admin_warning: Option<String>,
    pub jito: bool,
    pub jito_commission: Option<u64>,
    pub stake_pools_list: Vec<String>,
    pub is_active: bool,
    pub avatar_file_url: Option<String>,
    pub active_stake: Option<Stake>,
    pub authorized_withdrawer_score: i8,
    pub commission: Option<u8>,
    pub data_center_concentration_score: i8,
    pub delinquent: Option<bool>,
    pub published_information_score: i8,
    pub root_distance_score: i8,
    pub security_report_score: i8,
    pub skipped_slot_score: i8,
    pub skipped_after_score: i8,
    pub software_version: String,
    pub software_version_score: i8,
    pub stake_concentration_score: i8,
    pub consensus_mods_score: i8,
    pub total_score: i8,
    pub vote_distance_score: i8,
    pub ip: String,
    pub data_center_key: Option<String>,
    pub autonomous_system_number: Option<u32>,
    // "latitude": "51.1784",
    pub latitude: Option<String>,
    // "longitude": "7.1601",
    pub longitude: Option<String>,
    pub data_center_host: Option<String>,
    pub vote_account: String,
    pub epoch_credits: Option<u64>,
    pub epoch: Option<u16>,
    pub skipped_slots: Option<u64>,
    // "skipped_slot_percent": "0.0",
    pub skipped_slot_percent: Option<String>,
    pub ping_time: Option<f64>,
    pub url: String,
}
