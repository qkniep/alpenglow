// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Rotor simulated workload and bandwidth testing.
//!
//!

use std::fs::File;
use std::sync::{Arc, Mutex};

use alpenglow::ValidatorInfo;
use alpenglow::disseminator::rotor::SamplingStrategy;
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
    pub fn run(&mut self, test_name: &str, slices: usize, csv_file: Arc<Mutex<csv::Writer<File>>>) {
        self.workload_test.run_multiple(slices);
        self.evaluate(test_name, csv_file);
    }

    fn evaluate(&self, test_name: &str, csv_file: Arc<Mutex<csv::Writer<File>>>) {
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
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
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
