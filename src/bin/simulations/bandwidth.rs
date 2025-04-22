use alpenglow::ValidatorInfo;
use alpenglow::disseminator::rotor::SamplingStrategy;
use alpenglow::shredder::TOTAL_SHREDS;
use rand::prelude::*;

pub struct BandwidthTest<L: SamplingStrategy, R: SamplingStrategy> {
    leader_bandwidth: u64,
    bandwidths: Vec<u64>,
    workload_test: WorkloadTest<L, R>,
}

struct WorkloadTest<L: SamplingStrategy, R: SamplingStrategy> {
    validators: Vec<ValidatorInfo>,
    leader_sampler: L,
    rotor_sampler: R,
    num_shreds: usize,

    leader_workload: u64,
    workload: Vec<u64>,
}

impl<L: SamplingStrategy, R: SamplingStrategy> BandwidthTest<L, R> {
    pub fn new(
        validators: &[ValidatorInfo],
        leader_bandwidth: u64,
        bandwidths: Vec<u64>,
        leader_sampler: L,
        rotor_sampler: R,
        k: usize,
    ) -> Self {
        let workload_test = WorkloadTest::new(validators, leader_sampler, rotor_sampler, k);
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

    pub fn run(&mut self, slices: usize) {
        self.workload_test.run_multiple(slices);
        self.evaluate();
    }

    fn evaluate(&self) {
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
        println!(
            "min. supported bandwidth: {:.1} Mbit/s",
            min_supported_bandwidth / 1e6 / 2.0,
        );
    }
}

impl<L: SamplingStrategy, R: SamplingStrategy> WorkloadTest<L, R> {
    fn new(validators: &[ValidatorInfo], leader_sampler: L, rotor_sampler: R, k: usize) -> Self {
        let num_val = validators.len();
        Self {
            validators: validators.to_vec(),
            leader_sampler,
            rotor_sampler,
            num_shreds: k,

            leader_workload: 0,
            workload: vec![0; num_val],
        }
    }

    fn run_multiple(&mut self, slices: usize) {
        let mut rng = rand::rngs::SmallRng::from_rng(&mut rand::rng());
        for _ in 0..slices {
            let leader = self.leader_sampler.sample(&mut rng);
            self.leader_workload += TOTAL_SHREDS as u64;
            self.workload[leader.id as usize] += TOTAL_SHREDS as u64;
            let relays = self
                .rotor_sampler
                .sample_multiple(self.num_shreds, &mut rng);
            for relay in relays {
                if leader.id == relay.id {
                    self.workload[relay.id as usize] += self.validators.len() as u64 - 1;
                } else {
                    self.workload[relay.id as usize] += self.validators.len() as u64 - 2;
                }
            }
        }
    }

    fn reset(&mut self) {
        self.workload = vec![0; self.validators.len()];
    }

    fn get_workload(&self) -> (u64, &[u64]) {
        (self.leader_workload, &self.workload)
    }
}
