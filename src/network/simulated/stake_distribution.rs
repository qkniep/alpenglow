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

use serde::Deserialize;

use crate::Stake;

use super::ping_data::coordinates_for_city;

/// Information about all validators on Solana mainnet.
pub static VALIDATOR_DATA: LazyLock<Vec<ValidatorData>> = LazyLock::new(|| {
    let file = File::open("data/mainnet_validators_validatorsdotapp.json").unwrap();
    let validators: Vec<ValidatorData> = serde_json::from_reader(file).unwrap();
    validators
});

/// Data for a single validator on Solana.
///
/// This matches the format of the data in `data/mainnet_validators_validatorsdotapp.json`.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct ValidatorData {
    pub network: String,
    pub account: String,
    pub name: Option<String>,
    pub keybase_id: Option<String>,
    pub www_url: Option<String>,
    pub details: Option<String>,
    pub avatar_url: Option<String>,
    pub created_at: String,
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
    pub latitude: Option<String>,
    pub longitude: Option<String>,
    pub data_center_host: Option<String>,
    pub vote_account: String,
    pub epoch_credits: Option<u64>,
    pub epoch: Option<u16>,
    pub skipped_slots: Option<u64>,
    pub skipped_slot_percent: Option<String>,
    pub ping_time: Option<f64>,
    pub url: String,
}

/// Same as [`VALIDATOR_DATA`], but for Sui mainnet.
pub static SUI_VALIDATOR_DATA: LazyLock<Vec<ValidatorData>> = LazyLock::new(|| {
    // read CSV
    let file = File::open("data/sui_validators.csv").unwrap();
    let reader = csv::Reader::from_reader(file);
    let sui_validators: Vec<SuiValidatorData> =
        reader.into_deserialize().map(Result::unwrap).collect();

    // map from SuiValidatorData to ValidatorData
    let validators: Vec<ValidatorData> = sui_validators
        .into_iter()
        .map(|v| {
            let (lat, lon) = v.coords.split_once(',').unwrap();
            ValidatorData {
                name: Some(v.name),
                is_active: true,
                active_stake: Some((v.stake.round() * 100.0) as Stake),
                delinquent: Some(false),
                ip: v.ip.unwrap_or(v.address.clone()),
                data_center_key: Some(format!(
                    "{}-{}-{}",
                    v.country.unwrap_or_default(),
                    v.city.unwrap_or_default(),
                    v.cloud.clone().unwrap_or_default()
                )),
                latitude: Some(lat.to_owned()),
                longitude: Some(lon.to_owned()),
                data_center_host: v.cloud,
                ping_time: Some(v.ping),
                url: v.address,
                ..Default::default()
            }
        })
        .collect();

    validators
});

/// Data for a single validator on Sui.
///
/// This matches the format of the data in `data/sui_validators.csv`.
#[derive(Clone, Debug, Deserialize)]
pub struct SuiValidatorData {
    name: String,
    stake: f64,
    address: String,
    ip: Option<String>,
    cloud: Option<String>,
    city: Option<String>,
    country: Option<String>,
    coords: String,
    ping: f64,
}

///
pub fn hub_validator_data(hubs: Vec<(String, f64)>) -> Vec<ValidatorData> {
    let mut validators = Vec::new();
    for (city, frac_stake) in hubs {
        let (lat, lon) = coordinates_for_city(&city).unwrap();
        for _ in 0..30 {
            let stake = (frac_stake * 100.0 * 10_000.0 / 30.0).round() as Stake;
            validators.push(ValidatorData {
                is_active: true,
                active_stake: Some(stake),
                delinquent: Some(false),
                latitude: Some(lat.to_string()),
                longitude: Some(lon.to_string()),
                ..Default::default()
            });
        }
    }
    validators
}
