// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structures for resource utilization.
//!
//! For now, all these resources exist at each validator individually.

// TODO: introduce notion of a shared resource?

use alpenglow::ValidatorId;

use crate::discrete_event_simulator::{Event, Protocol, SimTime, SimulationEnvironment, Stage};

///
#[derive(Clone, Debug)]
pub struct Resources {
    network: Resource,
    cpu: Resource,
}

impl Resources {
    ///
    pub fn new(num_validators: usize) -> Self {
        Self {
            network: Resource::new(num_validators),
            cpu: Resource::new(num_validators),
        }
    }
}

///
#[derive(Clone, Debug)]
pub struct Resource {
    next_free: Vec<SimTime>,
}

impl Resource {
    ///
    pub fn new(num_validators: usize) -> Self {
        Self {
            next_free: vec![SimTime::ZERO; num_validators],
        }
    }

    ///
    pub fn time_next_free(&self, validator: ValidatorId) -> SimTime {
        self.next_free[validator as usize]
    }

    ///
    // TODO: find better name
    pub fn wait_for_next_free(&self, validator: ValidatorId, time: SimTime) -> SimTime {
        time.max(self.time_next_free(validator))
    }

    ///
    fn reserve(&mut self, validator: ValidatorId, start_time: SimTime, duration: SimTime) {
        let end_time = start_time + duration;
        self.next_free[validator as usize] = end_time;
    }

    /// Schedules the resource to be used for `duration` at the
    pub fn schedule(
        &mut self,
        validator: ValidatorId,
        target_start_time: SimTime,
        duration: SimTime,
    ) {
        let actual_start_time = self.wait_for_next_free(validator, target_start_time);
        self.reserve(validator, actual_start_time, duration);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {}
}
