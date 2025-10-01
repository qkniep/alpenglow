// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structures for resource utilization.
//!
//! For now, all these resources exist at each validator individually.

// TODO: introduce notion of a shared resource?

use alpenglow::ValidatorId;

use crate::discrete_event_simulator::SimTime;

/// Tracks resource utilization across all resources and validators.
// TODO: add other resources
#[derive(Clone, Debug)]
pub struct Resources {
    pub network: Resource,
    // pub cpu: Resource,
}

impl Resources {
    /// Creates a new resource utilization tracker.
    ///
    /// All validators start with all resources free to be used.
    pub fn new(num_validators: usize) -> Self {
        Self {
            network: Resource::new(num_validators),
            // cpu: Resource::new(num_validators),
        }
    }
}

/// Tracks resource utilization for a single resource.
#[derive(Clone, Debug)]
pub struct Resource {
    next_free: Vec<SimTime>,
}

impl Resource {
    /// Creates a new resource.
    ///
    /// All validators start with this resource free to be used.
    pub fn new(num_validators: usize) -> Self {
        Self {
            next_free: vec![SimTime::ZERO; num_validators],
        }
    }

    /// Returns the next time this resource will be free.
    pub fn time_next_free(&self, validator: ValidatorId) -> SimTime {
        self.next_free[validator as usize]
    }

    /// Returns the next time this resource will be free, after `time`.
    // TODO: find better name
    pub fn wait_for_next_free(&self, validator: ValidatorId, time: SimTime) -> SimTime {
        time.max(self.time_next_free(validator))
    }

    /// Schedules the resource to be used.
    ///
    /// First, finds the next time this resource will be free after `target_start_time`.
    /// Then, reserves the resource for `duration` starting at that time.
    pub fn schedule(
        &mut self,
        validator: ValidatorId,
        target_start_time: SimTime,
        duration: SimTime,
    ) -> SimTime {
        let actual_start_time = self.wait_for_next_free(validator, target_start_time);
        self.reserve(validator, actual_start_time, duration)
    }

    /// Reserves the resource for `duration` starting at `start_time`.
    fn reserve(
        &mut self,
        validator: ValidatorId,
        start_time: SimTime,
        duration: SimTime,
    ) -> SimTime {
        let end_time = start_time + duration;
        self.next_free[validator as usize] = end_time;
        end_time
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {}
}
