// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Rotor simulated workload and bandwidth testing.
//!
//! This module provides simulations about Rotor bandwidth usage.
//! It simulates the dissemination of multiple slices via Rotor.
//! It tracks the workload (number of shreds/datagrams sent) for each validator.
//! The workload is then used to estimate the bandwidth requirements for each validator.
//!
//! Specifically, it provides the following:
//!   - An analysis of Rotor workload distribution per validator,
//!     that is the number of shreds/datagrams sent by each validator.
//!   - An analysis of Rotor bandwidth usage (in bits/s) per validator to send
//!     a given number of slices.
//!   - The maximum goodput that can be achieved for a given bandwidth distribution.

use std::fs::File;
use std::sync::{Arc, Mutex};

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::shredder::MAX_DATA_PER_SHRED;
use alpenglow::{ValidatorId, ValidatorInfo};
use rand::prelude::*;

/// Instance of a bandwidth requirements test.
///
/// This is a wrapper around [`WorkloadTest`].
/// It augments the workload test with bandwidth information.
pub struct BandwidthTest<L: SamplingStrategy, R: SamplingStrategy> {
    leader_bandwidth: u64,
    bandwidths: Vec<u64>,
    workload_test: WorkloadTest<L, R>,
}

/// Instance of a bandwidth workload test.
///
/// This simulates the distribution of shreds via Rotor.
/// It tracks the workload (number of shreds/datagrams sent) for each validator.
pub struct WorkloadTest<L: SamplingStrategy, R: SamplingStrategy> {
    validators: Vec<ValidatorInfo>,
    leader_sampler: L,
    rotor_sampler: R,
    num_shreds: usize,

    leader_workload: u64,
    workload: Vec<u64>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> BandwidthTest<L, R> {
    /// Creates a new instance with the given stake and bandwidth distribution.
    pub fn new(
        validators: &[ValidatorInfo],
        leader_bandwidth: u64,
        bandwidths: Vec<u64>,
        leader_sampler: L,
        rotor_sampler: R,
        num_shreds: usize,
    ) -> Self {
        let workload_test =
            WorkloadTest::new(validators, leader_sampler, rotor_sampler, num_shreds);
        Self::from_workload_test(validators, leader_bandwidth, bandwidths, workload_test)
    }

    fn from_workload_test(
        validators: &[ValidatorInfo],
        leader_bandwidth: u64,
        bandwidths: Vec<u64>,
        workload_test: WorkloadTest<L, R>,
    ) -> Self {
        assert_eq!(validators.len(), bandwidths.len());
        Self {
            leader_bandwidth,
            bandwidths,
            workload_test,
        }
    }

    /// Sets the number of shreds per slice to `num_shreds`.
    ///
    /// Should usually call [`BandwidthTest::reset`] after this.
    pub fn set_num_shreds(&mut self, num_shreds: usize) {
        self.workload_test.set_num_shreds(num_shreds);
    }

    /// Runs multiple iterations of the workload test.
    ///
    /// Each iteration corresponds to distributing one slice, sampling leader
    /// and relays. This only modifies the internal state of the workload test.
    /// Calling `evaluate_supported` or `evaluate_usage` will output the results.
    pub fn run_multiple(&mut self, slices: usize) {
        self.workload_test.run_multiple(slices);
    }

    /// Evaluates the maximum supported goodput.
    ///
    /// Writes the results to the given CSV file.
    /// This is only meaningful after `run_multiple` has been called.
    pub fn evaluate_supported(&self, test_name: &str, csv_file: &Arc<Mutex<csv::Writer<File>>>) {
        let (leader_workload, workload) = self.workload_test.get_workload();
        let seconds =
            (8 * MAX_DATA_PER_SHRED as u64 * leader_workload) as f64 / self.leader_bandwidth as f64;
        let mut min_supported_bandwidth = self.leader_bandwidth as f64;
        for (i, shreds) in workload.iter().enumerate() {
            let bytes = MAX_DATA_PER_SHRED as u64 * shreds;
            let required_bandwidth = (bytes * 8) as f64 / seconds;
            let ratio = required_bandwidth / self.bandwidths[i] as f64;
            if self.leader_bandwidth as f64 / ratio < min_supported_bandwidth {
                min_supported_bandwidth = self.leader_bandwidth as f64 / ratio;
            }
        }

        let parts = test_name.split('-').collect::<Vec<_>>();
        let stake_distribution = parts[0];
        let sampling_strategy = parts[1];

        let mut csv_file = csv_file.lock().unwrap();
        csv_file
            .write_record(&[
                stake_distribution.to_string(),
                sampling_strategy.to_string(),
                self.leader_bandwidth.to_string(),
                self.workload_test.num_shreds.to_string(),
                (min_supported_bandwidth / 2.0).to_string(),
            ])
            .unwrap();
        csv_file.flush().unwrap();
    }

    /// Evaluates the bandwidth usage.
    ///
    /// Writes the results to the given CSV file.
    /// This is only meaningful after `run_multiple` has been called.
    pub fn evaluate_usage(&self, test_name: &str, csv_file: Arc<Mutex<csv::Writer<File>>>) {
        let (leader_workload, workload) = self.workload_test.get_workload();
        let mut bandwidth_usage = vec![(0.0, 0); workload.len()];
        for (i, shreds) in workload.iter().enumerate() {
            let ratio = *shreds as f64 / leader_workload as f64;
            bandwidth_usage[i] = (self.leader_bandwidth as f64 * ratio, i as ValidatorId);
        }

        bandwidth_usage.sort_unstable_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        let mut binned_bandwidth_usage = vec![(0.0, 0, 0); 99];
        for (i, (bandwidth, _)) in bandwidth_usage.into_iter().enumerate() {
            let bin = i / 13;
            let (b, mut v, c) = binned_bandwidth_usage[bin];
            if i % 13 == 0 {
                v = i;
            }
            let new_b = (b * c as f64 + bandwidth) / (c + 1) as f64;
            binned_bandwidth_usage[bin] = (new_b, v, c + 1);
        }

        let parts = test_name.split('-').collect::<Vec<_>>();
        let stake_distribution = parts[0];
        let sampling_strategy = parts[1];

        let mut csv_file = csv_file.lock().unwrap();
        for (bandwidth, validator, _) in binned_bandwidth_usage {
            csv_file
                .write_record(&[
                    stake_distribution.to_string(),
                    sampling_strategy.to_string(),
                    self.leader_bandwidth.to_string(),
                    self.workload_test.num_shreds.to_string(),
                    validator.to_string(),
                    32_270_000.0.to_string(),
                    bandwidth.to_string(),
                ])
                .unwrap();
        }
        csv_file.flush().unwrap();
    }

    /// Resets the internal state.
    ///
    /// This is useful for running multiple independent tests.
    pub fn reset(&mut self) {
        self.workload_test.reset();
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> WorkloadTest<L, R> {
    /// Creates a new instance with the given stake distribution.
    pub fn new(
        validators: &[ValidatorInfo],
        leader_sampler: L,
        rotor_sampler: R,
        num_shreds: usize,
    ) -> Self {
        let num_val = validators.len();
        Self {
            validators: validators.to_vec(),
            leader_sampler,
            rotor_sampler,
            num_shreds,

            leader_workload: 0,
            workload: vec![0; num_val],
        }
    }

    /// Sets the number of shreds per slice to `num_shreds`.
    ///
    /// Should usually call [`WorkloadTest::reset`] after this.
    pub fn set_num_shreds(&mut self, num_shreds: usize) {
        self.num_shreds = num_shreds;
    }

    /// Simulates distribution of `slices` slices via Rotor.
    ///
    /// Adds the workload from these iterations to the running totals.
    pub fn run_multiple(&mut self, slices: usize) {
        let mut rng = SmallRng::from_rng(&mut rand::rng());
        for _ in 0..slices {
            self.run_one(&mut rng);
        }
    }

    /// Simulates distribution of one slice via Rotor.
    ///
    /// Adds the workload from this iteration to the running totals.
    pub fn run_one(&mut self, rng: &mut impl Rng) {
        let leader = self.leader_sampler.sample(rng);
        self.leader_workload += self.num_shreds as u64;
        self.workload[leader as usize] += self.num_shreds as u64;
        let relays = self.rotor_sampler.sample_multiple(self.num_shreds, rng);
        for relay in relays {
            if leader == relay {
                self.workload[relay as usize] += self.validators.len() as u64 - 1;
            } else {
                self.workload[relay as usize] += self.validators.len() as u64 - 2;
            }
        }
    }

    /// Resets the internal state.
    ///
    /// This is useful for running multiple independent tests.
    pub fn reset(&mut self) {
        self.workload = vec![0; self.validators.len()];
    }

    /// Returns the workload for the leader and the workload per validator.
    ///
    /// Workload is defined as the total number of shreds sent by each.
    pub fn get_workload(&self) -> (u64, &[u64]) {
        (self.leader_workload, &self.workload)
    }
}
