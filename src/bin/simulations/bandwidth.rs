// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Rotor simulated workload and bandwidth testing.
//!
//!

use std::fs::File;
use std::sync::{Arc, Mutex};

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use rand::prelude::*;

///
pub struct BandwidthTest<L: SamplingStrategy, R: SamplingStrategy> {
    leader_bandwidth: u64,
    bandwidths: Vec<u64>,
    workload_test: WorkloadTest<L, R>,
}

///
pub struct WorkloadTest<L: SamplingStrategy, R: SamplingStrategy> {
    validators: Vec<ValidatorInfo>,
    leader_sampler: L,
    rotor_sampler: R,
    num_shreds: usize,

    leader_workload: u64,
    workload: Vec<u64>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> BandwidthTest<L, R> {
    ///
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

    ///
    pub fn run_multiple(&mut self, slices: usize) {
        self.workload_test.run_multiple(slices);
    }

    ///
    pub fn evaluate_supported(&self, test_name: &str, csv_file: Arc<Mutex<csv::Writer<File>>>) {
        let (leader_workload, workload) = self.workload_test.get_workload();
        let seconds = (8 * 1500 * leader_workload) as f64 / self.leader_bandwidth as f64;
        let mut min_supported_bandwidth = self.leader_bandwidth as f64;
        for (i, shreds) in workload.iter().enumerate() {
            let bytes = 1500 * shreds;
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

    ///
    pub fn evaluate_usage(&self, test_name: &str, csv_file: Arc<Mutex<csv::Writer<File>>>) {
        let (leader_workload, workload) = self.workload_test.get_workload();
        let mut bandwidth_usage = vec![(0.0, 0); workload.len()];
        for (i, shreds) in workload.iter().enumerate() {
            let ratio = *shreds as f64 / leader_workload as f64;
            bandwidth_usage[i] = (self.leader_bandwidth as f64 * ratio, i as ValidatorId);
        }

        let validators = &self.workload_test.validators;
        bandwidth_usage.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let percentile_stake = total_stake as f64 / 100.0;
        let mut percentile = 1;
        let mut stake_so_far = 0.0;
        let mut percentile_bandwidth_usage = vec![0.0; 100];
        for (bandwidth, v) in &*bandwidth_usage {
            let mut validator_stake = validators[*v as usize].stake as f64;
            for _ in 0..100 {
                let percentile_stake_left = percentile as f64 * percentile_stake - stake_so_far;
                let abs_stake_contrib = validator_stake.min(percentile_stake_left);
                let rel_stake_contrib = abs_stake_contrib / percentile_stake;
                let bandwidth_contrib = rel_stake_contrib * *bandwidth;
                percentile_bandwidth_usage[percentile as usize - 1] += bandwidth_contrib;
                stake_so_far += abs_stake_contrib;
                validator_stake -= abs_stake_contrib;
                if percentile < 100 && stake_so_far >= percentile as f64 * percentile_stake {
                    percentile += 1;
                } else {
                    break;
                }
            }
        }

        let parts = test_name.split('-').collect::<Vec<_>>();
        let stake_distribution = parts[0];
        let sampling_strategy = parts[1];

        let mut csv_file = csv_file.lock().unwrap();
        for percentile in 1..=100 {
            csv_file
                .write_record(&[
                    stake_distribution.to_string(),
                    sampling_strategy.to_string(),
                    self.leader_bandwidth.to_string(),
                    self.workload_test.num_shreds.to_string(),
                    percentile.to_string(),
                    32_270_000.0.to_string(),
                    percentile_bandwidth_usage[percentile - 1].to_string(),
                ])
                .unwrap();
        }
        csv_file.flush().unwrap();
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> WorkloadTest<L, R> {
    /// Creates a new workload test.
    ///
    ///
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
