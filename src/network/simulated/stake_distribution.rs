// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Utilities for working with the stake distribution of Solana mainnet.
//!
//! Validator data is taken from [Validators.app](https://validators.app/).
//! The data is stored in the `data/mainnet_validators_epoch860.json` file.
//! It contains all validators (i.e. nodes with non-zero stake) on Solana mainnet.
//!
//! # Examples
//!
//! ```
//! use alpenglow::network::simulated::stake_distribution::{VALIDATOR_DATA, ValidatorData};
//!
//! let mut stakes = VALIDATOR_DATA
//!     .iter()
//!     .filter_map(ValidatorData::active_stake)
//!     .collect::<Vec<_>>();
//! ```

use std::collections::HashSet;
use std::fs::File;
use std::sync::LazyLock;

use log::{info, warn};
use serde::Deserialize;

use super::ping_data::{PingServer, coordinates_for_city, find_closest_ping_server, get_ping};
use crate::crypto::aggsig;
use crate::crypto::signature::SecretKey;
use crate::network::dontcare_sockaddr;
use crate::{Stake, ValidatorId, ValidatorInfo};

/// Information about all validators on Solana mainnet.
pub static VALIDATOR_DATA: LazyLock<Vec<ValidatorData>> = LazyLock::new(|| {
    let file = File::open("data/mainnet_validators_epoch860.json").unwrap();
    let validators: Vec<ValidatorData> = serde_json::from_reader(file).unwrap();
    validators
});

/// Data for a single validator on Solana.
///
/// This matches the format of the data in `data/mainnet_validators_epoch860.json`.
#[allow(dead_code)]
#[derive(Clone, Debug, Default, Deserialize)]
pub struct ValidatorData {
    network: String,
    account: String,
    name: Option<String>,
    keybase_id: Option<String>,
    www_url: Option<String>,
    details: Option<String>,
    avatar_url: Option<String>,
    created_at: String,
    updated_at: String,
    admin_warning: Option<String>,
    jito: bool,
    jito_commission: Option<u64>,
    stake_pools_list: Vec<String>,
    is_active: bool,
    avatar_file_url: Option<String>,
    active_stake: Option<Stake>,
    authorized_withdrawer_score: i8,
    commission: Option<u8>,
    data_center_concentration_score: i8,
    delinquent: bool,
    published_information_score: i8,
    root_distance_score: i8,
    security_report_score: i8,
    skipped_slot_score: i8,
    skipped_after_score: i8,
    software_version: String,
    software_version_score: i8,
    stake_concentration_score: i8,
    consensus_mods_score: i8,
    total_score: i8,
    vote_distance_score: i8,
    ip: String,
    data_center_key: Option<String>,
    autonomous_system_number: Option<u32>,
    latitude: Option<String>,
    longitude: Option<String>,
    data_center_host: Option<String>,
    vote_account: String,
    epoch_credits: Option<u64>,
    epoch: Option<u16>,
    skipped_slots: Option<u64>,
    skipped_slot_percent: Option<String>,
    ping_time: Option<f64>,
    url: String,
}

impl ValidatorData {
    /// Returns the active stake of a validator, if it has non-zero active stake.
    pub fn active_stake(&self) -> Option<Stake> {
        if !self.is_active || self.delinquent {
            return None;
        }
        self.active_stake.filter(|stake| *stake > 0)
    }
}

/// Same as [`VALIDATOR_DATA`], but for Sui mainnet.
pub static SUI_VALIDATOR_DATA: LazyLock<Vec<ValidatorData>> = LazyLock::new(|| {
    // read CSV
    let file = File::open("data/sui_validators.csv").unwrap();
    let reader = csv::Reader::from_reader(file);
    let sui_validators = reader
        .into_deserialize::<SuiValidatorData>()
        .map(Result::unwrap);

    // map from SuiValidatorData to ValidatorData
    let validators: Vec<ValidatorData> = sui_validators
        .into_iter()
        .map(|v| {
            let (lat, lon) = v.coords.split_once(',').unwrap();
            ValidatorData {
                name: Some(v.name),
                is_active: true,
                active_stake: Some((v.stake.round() * 100.0) as Stake),
                delinquent: false,
                ip: v.ip.unwrap_or_else(|| v.address.clone()),
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

/// Artificial stake distribution for 5 global hubs.
///
/// Uses the same data format as [`VALIDATOR_DATA`].
pub static FIVE_HUBS_VALIDATOR_DATA: LazyLock<Vec<ValidatorData>> = LazyLock::new(|| {
    hub_validator_data(vec![
        ("San Francisco".to_string(), 0.2),
        ("Secaucus".to_string(), 0.2), // NYC/NJ
        ("London".to_string(), 0.2),
        ("Shanghai".to_string(), 0.2),
        ("Tokyo".to_string(), 0.2),
    ])
});

/// Artificial stake distribution for location of top 10 global stock exchanges.
///
/// Uses the same data format as [`VALIDATOR_DATA`].
pub static STOCK_EXCHANGES_VALIDATOR_DATA: LazyLock<Vec<ValidatorData>> = LazyLock::new(|| {
    hub_validator_data(vec![
        ("Toronto".to_string(), 0.1),
        ("Secaucus".to_string(), 0.2),  // NYC/NJ
        ("Westpoort".to_string(), 0.1), // Amsterdam
        ("Taipei".to_string(), 0.1),    // should maybe be Shenzhen (but we don't have ping data)
        ("Pune".to_string(), 0.2),      // should maybe be Mumbai (but we don't have ping data)
        ("Shanghai".to_string(), 0.1),
        ("Hong Kong".to_string(), 0.1),
        ("Tokyo".to_string(), 0.1),
    ])
});

/// Loads and converts a list of [`ValidatorData`], augmenting it with ping data.
///
/// Returns a tuple `(all_val, val_with_ping)`, where:
///   - `all_val` is a list [`ValidatorInfo`] for all validators
///   - `val_with_ping` is a list of tuples of [`ValidatorInfo`] and [`PingServer`]
///     for validators for which we find ping data in the dataset
#[must_use]
pub fn validators_from_validator_data(
    validator_data: &[ValidatorData],
) -> (
    Vec<ValidatorInfo>,
    Vec<(ValidatorInfo, &'static PingServer)>,
) {
    let mut validators = Vec::new();
    for v in validator_data {
        if let Some(stake) = v.active_stake() {
            let id = validators.len() as ValidatorId;
            let sk = SecretKey::new(&mut rand::rng());
            let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
            validators.push(ValidatorInfo {
                id,
                stake,
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: dontcare_sockaddr(),
                disseminator_address: dontcare_sockaddr(),
                repair_request_address: dontcare_sockaddr(),
                repair_response_address: dontcare_sockaddr(),
            });
        }
    }

    // assign closest ping servers to validators
    let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
    let mut validators_with_ping_data = Vec::new();
    let mut stake_with_ping_server = 0;
    for v in validator_data {
        let Some(stake) = v.active_stake() else {
            continue;
        };
        let (Some(lat), Some(lon)) = (&v.latitude, &v.longitude) else {
            continue;
        };
        let ping_server = find_closest_ping_server(lat.parse().unwrap(), lon.parse().unwrap());
        stake_with_ping_server += stake;
        let sk = SecretKey::new(&mut rand::rng());
        let voting_sk = aggsig::SecretKey::new(&mut rand::rng());
        validators_with_ping_data.push((
            ValidatorInfo {
                id: validators_with_ping_data.len() as ValidatorId,
                stake,
                pubkey: sk.to_pk(),
                voting_pubkey: voting_sk.to_pk(),
                all2all_address: dontcare_sockaddr(),
                disseminator_address: dontcare_sockaddr(),
                repair_request_address: dontcare_sockaddr(),
                repair_response_address: dontcare_sockaddr(),
            },
            ping_server,
        ));
    }
    let frac_wo_ping_server = 100.0 - stake_with_ping_server as f64 * 100.0 / total_stake as f64;
    warn!("discarding {frac_wo_ping_server:.2}% of validators w/o ping server");

    // determine pings of validator pairs
    let mut nodes_without_ping = HashSet::new();
    for (v1, p1) in &validators_with_ping_data {
        for (v2, p2) in &validators_with_ping_data {
            if get_ping(p1.id, p2.id).is_none()
                || (get_ping(p2.id, p1.id) == Some(0.0) && p2.id != p1.id)
            {
                nodes_without_ping.insert(v1.id);
                nodes_without_ping.insert(v2.id);
            }
        }
    }
    let frac_wo_ping =
        nodes_without_ping.len() as f64 * 100.0 / validators_with_ping_data.len() as f64;
    warn!("discarding {frac_wo_ping:.2}% of nodes w/o ping");
    warn!("{} validators without ping data", nodes_without_ping.len());
    validators_with_ping_data.retain(|(v, _)| !nodes_without_ping.contains(&v.id));
    let vals_left = validators_with_ping_data.len();
    info!("{vals_left} validators with ping data",);

    // give validators with ping data consecutive IDs
    for (i, v) in validators_with_ping_data.iter_mut().enumerate() {
        v.0.id = i as ValidatorId;
    }

    (validators, validators_with_ping_data)
}

/// Generates an artificial stake distribution.
///
/// The input `hubs` contains a list of (city, fraction of total stake).
/// Each city has to be in the ping dataset, i.e. supported by [`coordinates_for_city`].
/// Outputs a stake distribution in the same data format as [`VALIDATOR_DATA`].
#[must_use]
pub fn hub_validator_data(hubs: Vec<(String, f64)>) -> Vec<ValidatorData> {
    let mut validators = Vec::new();
    for (city, frac_stake) in hubs {
        let (lat, lon) = coordinates_for_city(&city).unwrap();
        for _ in 0..30 {
            let stake = (frac_stake * 100.0 * 10_000.0 / 30.0).round() as Stake;
            validators.push(ValidatorData {
                is_active: true,
                active_stake: Some(stake),
                delinquent: false,
                latitude: Some(lat.to_string()),
                longitude: Some(lon.to_string()),
                ..Default::default()
            });
        }
    }
    validators
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let validator_data = hub_validator_data(vec![("San Francisco".to_string(), 1.0)]);
        let (_, vals_with_ping) = validators_from_validator_data(&validator_data);
        assert_eq!(count_different_cities(&vals_with_ping), 1);

        let (validators, _) = validators_from_validator_data(&VALIDATOR_DATA);
        assert_eq!(validators.len(), 954);

        let (validators, _) = validators_from_validator_data(&SUI_VALIDATOR_DATA);
        assert_eq!(validators.len(), 106);

        let (_, vals_with_ping) = validators_from_validator_data(&FIVE_HUBS_VALIDATOR_DATA);
        assert_eq!(count_different_cities(&vals_with_ping), 5);

        let (_, vals_with_ping) = validators_from_validator_data(&STOCK_EXCHANGES_VALIDATOR_DATA);
        assert_eq!(count_different_cities(&vals_with_ping), 8);
    }

    fn count_different_cities(validators: &[(ValidatorInfo, &PingServer)]) -> usize {
        let mut cities = HashSet::new();
        for (_, p) in validators {
            cities.insert(&p.location);
        }
        cities.len()
    }
}
