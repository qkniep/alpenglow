// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Simulated latency test for the Alpenglow protocol.
//!
//! So far, this test can only simulate the good case.

use std::collections::HashMap;
use std::fs::File;
use std::hash::Hash;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::RwLock;

use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::shredder::MAX_DATA_PER_SHRED;
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use rand::prelude::*;
use rayon::prelude::*;

use crate::discrete_event_simulator::{EventTimingStats, TimingStats, Timings};
use crate::rotor::{RotorInstance, RotorInstanceBuilder, RotorParams};

/// Size (in bytes) assumed per vote in the simulation.
const VOTE_SIZE: usize = 128 /* sig */ + 64 /* slot, hash, flags */;
/// Size (in bytes) assumed per certificate in the simulation.
const CERT_SIZE: usize = 128 /* sig */ + 256 /* bitmap */ + 64 /* slot, hash, flags */;

/// The sequential stages of the latency test.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyTestStage {
    Rotor,
    Notar,
    Final1,
    Final2,
}

impl LatencyTestStage {
    fn next(self) -> Option<Self> {
        match self {
            LatencyTestStage::Rotor => Some(LatencyTestStage::Notar),
            LatencyTestStage::Notar => Some(LatencyTestStage::Final1),
            LatencyTestStage::Final1 => Some(LatencyTestStage::Final2),
            LatencyTestStage::Final2 => None,
        }
    }

    fn events(self) -> Vec<LatencyEvent> {
        match self {
            LatencyTestStage::Rotor => vec![LatencyEvent::Direct(0), LatencyEvent::Rotor(0)],
            LatencyTestStage::Notar => vec![LatencyEvent::Notar, LatencyEvent::Shreds95],
            LatencyTestStage::Final1 => vec![LatencyEvent::FastFinal, LatencyEvent::SlowFinal],
            LatencyTestStage::Final2 => vec![LatencyEvent::Final],
        }
    }
}

/// Events that can occur at each validator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LatencyEvent {
    Direct(usize),
    Rotor(usize),
    Shreds95,
    Notar,
    Notar65,
    FastFinal,
    SlowFinal,
    Final,
}

///
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LatencySimParams {
    rotor_params: RotorParams,
    num_slots_per_window: usize,
    num_slots: usize,
}

impl LatencySimParams {
    ///
    pub fn new(rotor_params: RotorParams, num_slots_per_window: usize, num_slots: usize) -> Self {
        Self {
            rotor_params,
            num_slots_per_window,
            num_slots,
        }
    }
}

///
pub struct LatencySimInstanceBuilder<L: SamplingStrategy, R: SamplingStrategy> {
    rotor_builder: RotorInstanceBuilder<L, R>,
    params: LatencySimParams,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencySimInstanceBuilder<L, R> {
    ///
    pub fn new(rotor_builder: RotorInstanceBuilder<L, R>, params: LatencySimParams) -> Self {
        Self {
            rotor_builder,
            params,
        }
    }

    ///
    pub fn sample_instance(&self, rng: &mut impl Rng) -> LatencySimInstance {
        let rotor_instance = self.rotor_builder.build(rng);
        LatencySimInstance {
            rotor_instance,
            params: self.params.clone(),
        }
    }
}

///
pub struct LatencySimInstance {
    rotor_instance: RotorInstance,
    params: LatencySimParams,
}

/// Simulated latency test.
pub struct LatencyTest<L: SamplingStrategy, R: SamplingStrategy> {
    // core setup of the latency test
    validators: Vec<ValidatorInfo>,
    ping_servers: Vec<&'static PingServer>,
    total_stake: Stake,
    builder: LatencySimInstanceBuilder<L, R>,

    // optional bandwidth information
    // if provided, these will be used to simulate transmission delays
    // otherwise, transmission delay is ignored
    leader_bandwidth: Option<u64>,
    bandwidths: Option<Vec<u64>>,

    // running aggregates (averages)
    stats: RwLock<TimingStats<LatencyEvent>>,
}

impl<L: SamplingStrategy + Sync + Send, R: SamplingStrategy + Sync + Send> LatencyTest<L, R> {
    /// Creates a new latency test instance.
    ///
    /// Caller needs to make sure that `leader_sampler` and `rotor_smapler`
    /// operate on the correct set of validators.
    pub fn new(
        validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
        leader_sampler: L,
        rotor_sampler: R,
        num_data_shreds: usize,
        num_shreds: usize,
    ) -> Self {
        let validators: Vec<ValidatorInfo> = validators_with_ping_data
            .iter()
            .map(|(v, _)| v.clone())
            .collect();
        let ping_servers: Vec<&'static PingServer> =
            validators_with_ping_data.iter().map(|(_, p)| *p).collect();
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();

        let rotor_params = RotorParams {
            num_data_shreds,
            num_shreds,
            num_slices: 1,
        };
        let rotor_builder = RotorInstanceBuilder::new(leader_sampler, rotor_sampler, rotor_params);

        let params = LatencySimParams::new(rotor_params, 4, 1);
        let builder = LatencySimInstanceBuilder::new(rotor_builder, params);

        Self {
            validators,
            ping_servers,
            total_stake,
            builder,

            leader_bandwidth: None,
            bandwidths: None,

            stats: RwLock::new(TimingStats::<LatencyEvent>::default()),
        }
    }

    /// Sets the bandwidths for all validators for simulating transmission delays.
    pub fn with_bandwidths(mut self, leader_bandwidth: u64, bandwidths: Vec<u64>) -> Self {
        self.leader_bandwidth = Some(leader_bandwidth);
        self.bandwidths = Some(bandwidths);
        self
    }

    /// Runs the latency simulation `iterations` times.
    ///
    /// In each iteration, a new leader and new relays are randomly selected.
    /// Each iteration runs only until `up_to_stage`, e.g., if `up_to_stage` is
    /// `LatencyTestStage::Direct`, only the direct latency will be measured.
    pub fn run_many(&self, test_name: &str, iterations: usize, up_to_stage: LatencyTestStage) {
        (0..iterations).into_par_iter().for_each(|_| {
            let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
            self.run_one(up_to_stage, &mut rng);
        });
        let path = Path::new("data")
            .join("output")
            .join("simulations")
            .join("latency")
            .join(test_name)
            .with_extension("csv");
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        self.stats
            .read()
            .unwrap()
            .write_to_csv(
                path,
                &[
                    ("direct", LatencyEvent::Direct(0)),
                    ("rotor", LatencyEvent::Rotor(0)),
                    ("shreds95", LatencyEvent::Shreds95),
                    ("notar", LatencyEvent::Notar),
                    ("fast_final", LatencyEvent::FastFinal),
                    ("slow_final", LatencyEvent::SlowFinal),
                    ("final", LatencyEvent::Final),
                ],
            )
            .unwrap();
    }

    /// Runs the latency simulation `iterations` times.
    ///
    /// In each iteration, a new leader and new relays are randomly selected.
    /// Each iteration runs only until `up_to_stage`, e.g., if `up_to_stage` is
    /// `LatencyTestStage::Direct`, only the direct latency will be measured.
    pub fn run_many_with_leader(
        &self,
        test_name: &str,
        iterations: usize,
        up_to_stage: LatencyTestStage,
        leader: ValidatorInfo,
    ) {
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
        for _ in 0..iterations {
            let mut instance = self.builder.sample_instance(&mut rng);
            instance.rotor_instance.leader = leader.id;
            self.run_one_deterministic(up_to_stage, instance);
        }

        let leader_ping_server = self.ping_servers[leader.id as usize];
        let path = Path::new("data")
            .join("output")
            .join("simulations")
            .join("latency")
            .join(&leader_ping_server.location)
            .join(test_name)
            .with_extension("csv");
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        self.stats
            .read()
            .unwrap()
            .write_to_csv(
                path,
                &[
                    ("direct", LatencyEvent::Direct(0)),
                    ("rotor", LatencyEvent::Rotor(0)),
                    ("shreds95", LatencyEvent::Shreds95),
                    ("notar", LatencyEvent::Notar),
                    ("fast_final", LatencyEvent::FastFinal),
                    ("slow_final", LatencyEvent::SlowFinal),
                    ("final", LatencyEvent::Final),
                ],
            )
            .unwrap();
    }

    /// Runs one iteration of the latency simulation with random leader and relays.
    pub fn run_one(&self, up_to_stage: LatencyTestStage, rng: &mut impl Rng) {
        let instance = self.builder.sample_instance(rng);
        self.run_one_deterministic(up_to_stage, instance);
    }

    /// Runs one iteration of the latency simulation with given leader and relays.
    pub fn run_one_deterministic(
        &self,
        up_to_stage: LatencyTestStage,
        instance: LatencySimInstance,
    ) {
        // setup & initialization
        let num_val = self.validators.len();
        let mut timings = Timings::default();
        // let mut relay_latencies = vec![0.0; self.params.num_shreds];
        // let mut tmp_rotor_latencies = vec![0.0; self.params.num_shreds];
        // let mut tmp_latencies = vec![(0.0, 0); num_val];
        // let mut tmp_transmission_latencies = vec![0.0; num_val];

        // simulation loop
        let mut stage = LatencyTestStage::Rotor;
        while stage <= up_to_stage {
            for event in stage.events() {
                timings.initialize(event, num_val);
            }

            for event in stage.events() {
                //
            }

            match stage.next() {
                Some(s) => stage = s,
                None => break,
            }
        }

        // for (slice, relays) in relays.iter().enumerate() {
        //     // measure direct latencies from leader to everyone
        //     for v in &self.validators {
        //         let leader_ping_server = self.ping_servers[leader as usize].id;
        //         let v_ping_server = self.ping_servers[v.id as usize].id;
        //
        //         let start_time = tmp_transmission_latencies[leader as usize];
        //         let propagation_delay = get_ping(leader_ping_server, v_ping_server).unwrap();
        //         let transmission_delay =
        //             v.id as f64 * self.time_to_send_message(MAX_DATA_PER_SHRED, v.id);
        //         let latency = start_time + propagation_delay + transmission_delay;
        //         timings.record(LatencyEvent::Direct(slice), latency, v.id);
        //     }
        //     let total_transmission_delay =
        //         self.time_to_send_message(MAX_DATA_PER_SHRED * num_val, leader);
        //     tmp_transmission_latencies[leader as usize] += total_transmission_delay;
        //     for (i, relay) in relays.iter().enumerate() {
        //         relay_latencies[i] = timings.get_one(LatencyEvent::Direct(slice), *relay);
        //     }
        //
        //     // measure Rotor block dissemination latencies
        //     for v in &self.validators {
        //         for (i, (relay, latency)) in relays.iter().zip(relay_latencies.iter()).enumerate() {
        //             let relay_ping_server = self.ping_servers[*relay as usize].id;
        //             let v_ping_server = self.ping_servers[v.id as usize].id;
        //
        //             let start_time = tmp_transmission_latencies[*relay as usize].max(*latency);
        //             if slice == 0 {
        //                 tmp_transmission_latencies[*relay as usize] = start_time;
        //             }
        //             let propagation_delay = get_ping(relay_ping_server, v_ping_server).unwrap();
        //             let transmission_delay = self.time_to_send_message(MAX_DATA_PER_SHRED, *relay);
        //             tmp_transmission_latencies[*relay as usize] += transmission_delay;
        //             let latency = start_time + propagation_delay + transmission_delay;
        //             tmp_rotor_latencies[i] = latency;
        //         }
        //         tmp_rotor_latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        //         let threshold_latency = tmp_rotor_latencies[self.params.num_data_shreds - 1];
        //         timings.record(LatencyEvent::Rotor(slice), threshold_latency, v.id);
        //         let threshold_latency = tmp_rotor_latencies[61 - 1];
        //         timings.record(LatencyEvent::Shreds95, threshold_latency, v.id);
        //     }
        // }
        //
        // // simulate notar vote propagation
        // // FIXME: need to use actual slowest slice (which may not generally be the last one)
        // let last_slice_event = LatencyEvent::Rotor(self.params.num_slices - 1);
        // for (v1_rotor_latency, v1) in timings.get(last_slice_event).unwrap().iter() {
        //     for (v2_rotor_latency, v2) in timings.get(last_slice_event).unwrap().iter() {
        //         let v1_ping_server = self.ping_servers[*v1 as usize].id;
        //         let v2_ping_server = self.ping_servers[*v2 as usize].id;
        //
        //         let start_time = tmp_transmission_latencies[*v2 as usize].max(*v2_rotor_latency);
        //         if *v1 == 0 {
        //             tmp_transmission_latencies[*v2 as usize] = start_time;
        //         }
        //         let propagation_delay = get_ping(v2_ping_server, v1_ping_server).unwrap();
        //         let transmission_delay = self.time_to_send_message(VOTE_SIZE, *v2);
        //         tmp_transmission_latencies[*v2 as usize] += transmission_delay;
        //         let latency = start_time + propagation_delay + transmission_delay;
        //         tmp_latencies[*v2 as usize] = (latency, *v2);
        //     }
        //     tmp_latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        //
        //     // measure latency until notarization and fast-finalization
        //     let mut notar_latency = None;
        //     let mut notar65_latency = None;
        //     let mut fast_final_latency = None;
        //     let mut stake_so_far = 0;
        //     for (latency, v) in &tmp_latencies {
        //         stake_so_far += self.validators[*v as usize].stake;
        //         if notar_latency.is_none() && stake_so_far as f64 > self.total_stake as f64 * 0.6 {
        //             notar_latency = Some(*latency);
        //         }
        //         if notar65_latency.is_none() && stake_so_far as f64 > self.total_stake as f64 * 0.65
        //         {
        //             notar65_latency = Some(*latency);
        //         }
        //         if stake_so_far as f64 > self.total_stake as f64 * 0.8 {
        //             fast_final_latency = Some(*latency);
        //             break;
        //         }
        //     }
        //     let mut notar_latency = notar_latency.unwrap();
        //     let notar65_latency = notar65_latency.unwrap();
        //     let mut fast_final_latency = fast_final_latency.unwrap();
        //     notar_latency = notar_latency.max(*v1_rotor_latency);
        //     timings.record(LatencyEvent::Notar, notar_latency, *v1);
        //     timings.record(LatencyEvent::Notar65, notar65_latency, *v1);
        //     fast_final_latency = fast_final_latency.max(*v1_rotor_latency);
        //     timings.record(LatencyEvent::FastFinal, fast_final_latency, *v1);
        //     timings.record(LatencyEvent::Final, fast_final_latency, *v1);
        // }
        //
        // // measure latency until (slow) finalization
        // for (v1_notar_latency, v1) in timings.get(LatencyEvent::Notar).unwrap().iter() {
        //     for (v2_notar_latency, v2) in timings.get(LatencyEvent::Notar).unwrap().iter() {
        //         let v1_ping_server = self.ping_servers[*v1 as usize].id;
        //         let v2_ping_server = self.ping_servers[*v2 as usize].id;
        //
        //         let start_time = tmp_transmission_latencies[*v2 as usize].max(*v2_notar_latency);
        //         if *v1 == 0 {
        //             tmp_transmission_latencies[*v2 as usize] = start_time;
        //         }
        //         let propagation_delay = get_ping(v2_ping_server, v1_ping_server).unwrap();
        //         let transmission_delay = self.time_to_send_message(VOTE_SIZE, *v2);
        //         tmp_transmission_latencies[*v2 as usize] += transmission_delay;
        //         let latency = start_time + propagation_delay + transmission_delay;
        //         tmp_latencies[*v2 as usize] = (latency, *v2);
        //     }
        //     tmp_latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        //     let mut slow_final_latency: f64 = 0.0;
        //     let mut stake_so_far = 0;
        //     for (latency, v) in &tmp_latencies {
        //         stake_so_far += self.validators[*v as usize].stake;
        //         if stake_so_far as f64 > self.total_stake as f64 * 0.6 {
        //             slow_final_latency = *latency;
        //             break;
        //         }
        //     }
        //     slow_final_latency = slow_final_latency.max(*v1_notar_latency);
        //     timings.record(LatencyEvent::SlowFinal, slow_final_latency, *v1);
        //     timings.record(LatencyEvent::Final, slow_final_latency, *v1);
        // }

        // commit latencies to stats (update averages)
        let stats_map = &mut self.stats.write().unwrap();
        stats_map.record_latencies(&mut timings, &self.validators, &self.ping_servers);
    }

    fn time_to_send_message(&self, bytes: usize, validator: ValidatorId) -> f64 {
        let Some(bandwidths) = &self.bandwidths else {
            return 0.0;
        };
        (bytes * 8) as f64 / bandwidths[validator as usize] as f64
    }
}
