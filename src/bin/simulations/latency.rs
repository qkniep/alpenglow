use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::network::simulated::ping_data::{PingServer, get_ping};
use alpenglow::{Stake, ValidatorId, ValidatorInfo};
use log::info;
use rand::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LatencyTestStage {
    Direct,
    Rotor,
    Notar,
    Final,
}

pub struct LatencyTest<L: SamplingStrategy, R: SamplingStrategy> {
    validators: Vec<ValidatorInfo>,
    ping_servers: Vec<&'static PingServer>,
    leader_sampler: L,
    rotor_sampler: R,
    num_shreds: usize,
    total_stake: Stake,

    direct_stats: LatencyStats,
    rotor_stats: LatencyStats,
    notar_stats: LatencyStats,
    fast_final_stats: LatencyStats,
    slow_final_stats: LatencyStats,

    relay_latencies: Vec<f64>,
    direct_latencies: Vec<(f64, ValidatorId)>,
    rotor_latencies: Vec<(f64, ValidatorId)>,
    notar_latencies: Vec<(f64, ValidatorId)>,
    fast_final_latencies: Vec<(f64, ValidatorId)>,
    slow_final_latencies: Vec<(f64, ValidatorId)>,
    tmp_latencies: Vec<f64>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> LatencyTest<L, R> {
    pub fn new(
        validators_with_ping_data: &[(ValidatorInfo, &'static PingServer)],
        leader_sampler: L,
        rotor_sampler: R,
        k: usize,
    ) -> Self {
        let validators: Vec<ValidatorInfo> = validators_with_ping_data
            .iter()
            .map(|(v, _)| v.clone())
            .collect();
        let ping_servers: Vec<&'static PingServer> =
            validators_with_ping_data.iter().map(|(_, p)| *p).collect();
        let num_val = validators.len();
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        Self {
            validators,
            ping_servers,
            leader_sampler,
            rotor_sampler,
            num_shreds: k,
            total_stake,

            direct_stats: LatencyStats::new(),
            rotor_stats: LatencyStats::new(),
            notar_stats: LatencyStats::new(),
            fast_final_stats: LatencyStats::new(),
            slow_final_stats: LatencyStats::new(),

            relay_latencies: vec![0.0; k],
            direct_latencies: vec![(0.0, 0); num_val],
            rotor_latencies: vec![(0.0, 0); num_val],
            notar_latencies: vec![(0.0, 0); num_val],
            fast_final_latencies: vec![(0.0, 0); num_val],
            slow_final_latencies: vec![(0.0, 0); num_val],
            tmp_latencies: vec![0.0; k],
        }
    }

    pub fn run_many(&mut self, iterations: usize, up_to_stage: LatencyTestStage) {
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
        for _ in 0..iterations {
            let leader = self.leader_sampler.sample(&mut rng);
            let relays = self
                .rotor_sampler
                .sample_multiple(self.num_shreds, &mut rng);
            for (i, relay) in relays.iter().enumerate() {
                let leader_ping_server = self.ping_servers[leader.id as usize].id;
                let relay_ping_server = self.ping_servers[relay.id as usize].id;
                let latency = get_ping(leader_ping_server, relay_ping_server).unwrap();
                self.relay_latencies[i] = latency;
            }

            for (i, v) in self.validators.iter().enumerate() {
                let leader_ping_server = self.ping_servers[leader.id as usize].id;
                let v_ping_server = self.ping_servers[v.id as usize].id;
                let latency = get_ping(leader_ping_server, v_ping_server).unwrap();
                self.direct_latencies[i] = (latency, v.id);
            }

            if up_to_stage == LatencyTestStage::Direct {
                continue;
            }

            for (i, v) in self.validators.iter().enumerate() {
                for (j, (relay, latency)) in
                    relays.iter().zip(self.relay_latencies.iter()).enumerate()
                {
                    let relay_ping_server = self.ping_servers[relay.id as usize].id;
                    let v_ping_server = self.ping_servers[v.id as usize].id;
                    let latency = latency + get_ping(relay_ping_server, v_ping_server).unwrap();
                    self.tmp_latencies[j] = latency;
                }
                self.tmp_latencies
                    .sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let threshold_latency = self.tmp_latencies[31];
                self.rotor_latencies[i] = (threshold_latency, v.id);
            }

            if up_to_stage == LatencyTestStage::Rotor {
                continue;
            }

            for (v1_rotor_latency, v1) in &self.rotor_latencies {
                let mut latencies = Vec::new();
                for (v2_rotor_latency, v2) in &self.rotor_latencies {
                    let v1_ping_server = self.ping_servers[*v1 as usize].id;
                    let v2_ping_server = self.ping_servers[*v2 as usize].id;
                    let latency =
                        v2_rotor_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                    latencies.push((latency, *v2));
                }
                latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let mut notar_latency = 0.0;
                let mut stake_so_far = 0;
                for (latency, v) in &latencies {
                    stake_so_far += self.validators[*v as usize].stake;
                    if stake_so_far as f64 > self.total_stake as f64 * 0.6 {
                        notar_latency = *latency;
                        break;
                    }
                }
                notar_latency = notar_latency.max(*v1_rotor_latency);
                self.notar_latencies[*v1 as usize] = (notar_latency, *v1);
            }

            if up_to_stage == LatencyTestStage::Notar {
                continue;
            }

            for (v1_rotor_latency, v1) in &self.rotor_latencies {
                let mut latencies = Vec::new();
                for (v2_rotor_latency, v2) in &self.rotor_latencies {
                    let v1_ping_server = self.ping_servers[*v1 as usize].id;
                    let v2_ping_server = self.ping_servers[*v2 as usize].id;
                    let latency =
                        v2_rotor_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                    latencies.push((latency, *v2));
                }
                latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let mut fast_final_latency: f64 = 0.0;
                let mut stake_so_far = 0;
                for (latency, v) in &latencies {
                    stake_so_far += self.validators[*v as usize].stake;
                    if stake_so_far as f64 > self.total_stake as f64 * 0.8 {
                        fast_final_latency = *latency;
                        break;
                    }
                }
                fast_final_latency = fast_final_latency.max(*v1_rotor_latency);
                self.fast_final_latencies[*v1 as usize] = (fast_final_latency, *v1);
            }

            for (v1_notar_latency, v1) in &self.notar_latencies {
                let mut latencies = Vec::new();
                for (v2_notar_latency, v2) in &self.notar_latencies {
                    let v1_ping_server = self.ping_servers[*v1 as usize].id;
                    let v2_ping_server = self.ping_servers[*v2 as usize].id;
                    let latency =
                        v2_notar_latency + get_ping(v2_ping_server, v1_ping_server).unwrap();
                    latencies.push((latency, *v2));
                }
                latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
                let mut slow_final_latency: f64 = 0.0;
                let mut stake_so_far = 0;
                for (latency, v) in &latencies {
                    stake_so_far += self.validators[*v as usize].stake;
                    if stake_so_far as f64 > self.total_stake as f64 * 0.6 {
                        slow_final_latency = *latency;
                        break;
                    }
                }
                slow_final_latency = slow_final_latency.max(*v1_notar_latency);
                self.slow_final_latencies[*v1 as usize] = (slow_final_latency, *v1);
            }

            self.direct_stats
                .record_latencies(&mut self.direct_latencies, &self.validators);
            self.rotor_stats
                .record_latencies(&mut self.rotor_latencies, &self.validators);
            self.notar_stats
                .record_latencies(&mut self.notar_latencies, &self.validators);
            self.fast_final_stats
                .record_latencies(&mut self.fast_final_latencies, &self.validators);
            self.slow_final_stats
                .record_latencies(&mut self.slow_final_latencies, &self.validators);
        }
        println!(
            "{},{},{},{},{},{},{}",
            self.num_shreds,
            self.direct_stats.max_latency,
            self.direct_stats.p60_latency,
            self.direct_stats.p80_latency,
            self.rotor_stats.max_latency,
            self.rotor_stats.p60_latency,
            self.rotor_stats.p80_latency
        );
        // info!("[{k} Shreds] Direct:");
        // direct_stats.print();
        // info!("[{k} Shreds] Rotor:");
        // rotor_stats.print();
        // info!("[{k} Shreds] Notarization:");
        // notar_stats.print();
        // info!("[{k} Shreds] Fast-Finalization:");
        // fast_final_stats.print();
        // info!("[{k} Shreds] Slow-Finalization:");
        // slow_final_stats.print();
    }
}

#[derive(Default)]
struct LatencyStats {
    max_latency: f64,
    p60_latency: f64,
    p80_latency: f64,
    count: u64,
}

impl LatencyStats {
    fn new() -> Self {
        Self::default()
    }

    fn record_latencies(
        &mut self,
        latencies: &mut Vec<(f64, ValidatorId)>,
        validators: &[ValidatorInfo],
    ) {
        latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        let total_stake: Stake = validators.iter().map(|v| v.stake).sum();
        let max_rotor_latency = latencies.last().unwrap().0;
        let mut p60_rotor_latency = 0.0;
        let mut stake_so_far = 0;
        for (latency, v) in &*latencies {
            stake_so_far += validators[*v as usize].stake;
            if stake_so_far as f64 > total_stake as f64 * 0.6 {
                p60_rotor_latency = *latency;
                break;
            }
        }
        let mut p80_rotor_latency = 0.0;
        let mut stake_so_far = 0;
        for (latency, v) in &*latencies {
            stake_so_far += validators[*v as usize].stake;
            if stake_so_far as f64 > total_stake as f64 * 0.8 {
                p80_rotor_latency = *latency;
                break;
            }
        }
        self.max_latency += max_rotor_latency;
        self.p60_latency += p60_rotor_latency;
        self.p80_latency += p80_rotor_latency;
        self.count += 1;
    }

    fn print(&self) {
        let avg_max_latency = self.max_latency / self.count as f64;
        let avg_p60_latency = self.p60_latency / self.count as f64;
        let avg_p80_latency = self.p80_latency / self.count as f64;
        info!("avg max latency: {:.2}", avg_max_latency);
        info!("avg p60 latency: {:.2}", avg_p60_latency);
        info!("avg p80 latency: {:.2}", avg_p80_latency);
    }
}
