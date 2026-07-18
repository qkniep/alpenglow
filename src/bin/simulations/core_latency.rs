// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Finalization-latency simulation driven by the *real* consensus core.
//!
//! Where [`crate::alpenglow`]'s latency test models the happy path analytically,
//! this runs the actual [`ConsensusCore`] on every validator (via the library's
//! [`alpenglow::consensus::latency_sim`] engine) over the mainnet ping matrix and
//! reports when the block finalizes. It is the sans-IO payoff applied to the
//! simulator: the protocol itself produces the numbers.
//!
//! [`ConsensusCore`]: alpenglow::consensus
//!
//! The executor is O(N²) in messages, so it runs over the top
//! [`MAX_VALIDATORS`] validators by stake rather than the full set — enough for a
//! representative, real-data latency figure without the analytical model's
//! assumptions.

use std::time::Duration;

use ::alpenglow::consensus::latency_sim::{LatencySimConfig, simulate_slot_finalization};
use ::alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use ::alpenglow::{Stake, ValidatorInfo};
use log::info;

/// Cap on validators fed to the O(N²) core-driven executor.
const MAX_VALIDATORS: usize = 50;

/// Runs the core-driven finalization-latency simulation and logs the result.
///
/// `validators_and_ping_servers` must already be sorted by descending stake, so
/// the top [`MAX_VALIDATORS`] are the highest-staked validators.
pub(crate) fn run(
    distribution_name: &str,
    validators_and_ping_servers: &[(ValidatorInfo, &'static PingServer)],
) {
    let n = validators_and_ping_servers.len().min(MAX_VALIDATORS);
    let subset = &validators_and_ping_servers[..n];

    let stakes: Vec<Stake> = subset.iter().map(|(v, _)| v.stake).collect();
    let latencies: Vec<Vec<Duration>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    if i == j {
                        Duration::ZERO
                    } else {
                        one_way_latency(subset[i].1.id, subset[j].1.id)
                    }
                })
                .collect()
        })
        .collect();

    let config = LatencySimConfig { stakes, latencies };
    let result = simulate_slot_finalization(&config);

    let fmt = |latency: Option<Duration>| {
        latency.map_or_else(
            || "n/a".to_owned(),
            |d| format!("{:.1}ms", d.as_secs_f64() * 1000.0),
        )
    };
    info!("{distribution_name}: core-driven finalization latency (top-{n} validators)");
    info!(
        "  60% stake finalized: {}",
        fmt(result.time_to_stake_fraction(0.60))
    );
    info!(
        "  80% stake finalized: {}",
        fmt(result.time_to_stake_fraction(0.80))
    );
    info!("  all stake finalized: {}", fmt(result.max()));
    if !result.all_finalized() {
        info!("  WARNING: not every validator finalized within the simulation");
    }
}

/// One-way latency between two ping servers, from their round-trip ping.
///
/// Falls back to a conservatively large delay if the pair has no ping datum, so
/// a missing measurement slows that link rather than aborting the run.
fn one_way_latency(source: usize, destination: usize) -> Duration {
    const MISSING_PING_MS: f64 = 400.0;
    let rtt_ms = get_ping(source, destination).unwrap_or(MISSING_PING_MS);
    Duration::from_secs_f64(rtt_ms / 2.0 / 1e3)
}
