// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Data structures for timing measurements.
//!
//! Most importantly the [`Timings`] struct, which is a map from events to timing vectors.
//! This is what the discrete-event simulator uses to record timings of events.
//! It can be thought of as a `#events x #validators` matrix of latencies.
//! Although, it is actually backed by a [`HashMap`] of [`Vec<SimTime>`],
//! so the rows are only initialized as needed.

use std::collections::HashMap;
use std::fmt::Display;
use std::fs::File;
use std::hash::Hash;
use std::io::{BufWriter, Write};
use std::ops::{Add, AddAssign};
use std::path::Path;

use alpenglow::ValidatorId;

use crate::discrete_event_simulator::{Event, Protocol, SimulationEnvironment, Stage};

/// Simulated time in nanoseconds.
// TODO: maybe split into a duration and an instant type?
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SimTime(u64);

impl SimTime {
    /// Start of the simulation.
    pub const ZERO: Self = Self(0);
    /// Infinite time, used to represent a point in time that is never reached.
    pub const NEVER: Self = Self(u64::MAX);

    /// Constructs a new [`SimTime`] from the given number of nanoseconds.
    pub const fn new(time_ns: u64) -> Self {
        Self(time_ns)
    }

    /// Constructs a new [`SimTime`] from the given number of seconds.
    ///
    /// The time is rounded to the nearest nanosecond.
    ///
    /// # Panics
    ///
    /// Panics if `time_secs` is negative.
    pub const fn from_secs(time_secs: f64) -> Self {
        assert!(time_secs >= 0.0);
        let time_ns = (time_secs * 1e9).round() as u64;
        Self::new(time_ns)
    }

    /// Returns the exact number of nanoseconds the [`SimTime`] represents.
    pub const fn nanos(self) -> Option<u64> {
        match self {
            Self::NEVER => None,
            Self(t) => Some(t),
        }
    }

    /// Converts the [`SimTime`] to (fractional) microseconds.
    pub fn as_micros(self) -> f64 {
        self.nanos()
            .map_or(f64::INFINITY, |nanos| nanos as f64 / 1e3)
    }

    /// Converts the [`SimTime`] to (fractional) milliseconds.
    pub fn as_millis(self) -> f64 {
        self.nanos()
            .map_or(f64::INFINITY, |nanos| nanos as f64 / 1e6)
    }

    /// Converts the [`SimTime`] to (fractional) seconds.
    pub fn as_secs(self) -> f64 {
        self.nanos()
            .map_or(f64::INFINITY, |nanos| nanos as f64 / 1e9)
    }
}

impl Add<SimTime> for SimTime {
    type Output = Self;
    fn add(self, other: SimTime) -> Self {
        Self(self.0 + other.0)
    }
}

impl AddAssign<SimTime> for SimTime {
    fn add_assign(&mut self, other: SimTime) {
        self.0 += other.0;
    }
}

impl Display for SimTime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self == &SimTime::NEVER {
            write!(f, "never")
        } else if self.0 < 1_000 {
            write!(f, "{} ns", self.0)
        } else if self.0 < 1_000_000 {
            write!(f, "{:.0} us", self.as_micros())
        } else if self.0 < 1_000_000_000 {
            write!(f, "{:.0} ms", self.as_millis())
        } else {
            write!(f, "{:.0} s", self.as_secs())
        }
    }
}

/// The timing matrix, implemented as a map from events to timing vectors.
pub struct Timings<E: Event> {
    start_time: SimTime,
    event_timings: HashMap<E, Vec<SimTime>>,
}

impl<E: Event> Timings<E> {
    /// Constructs a new [`Timings`] from the given start time.
    pub fn new(start_time: SimTime) -> Self {
        Self {
            start_time,
            event_timings: HashMap::new(),
        }
    }

    /// Initializes the timing vector for the given event to infinity.
    pub fn initialize(&mut self, event: E, num_val: usize) {
        self.event_timings
            .insert(event, vec![SimTime::NEVER; num_val]);
    }

    /// Deletes all the rows from the [`HashMap`].
    pub fn clear(&mut self) {
        self.event_timings.clear();
    }

    /// Records the latency for the given event and validator.
    pub fn record(&mut self, event: E, timing: SimTime, validator: ValidatorId) {
        let vec = self.event_timings.get_mut(&event).unwrap();
        let entry = vec.get_mut(validator as usize).unwrap();
        if timing < *entry {
            *entry = timing;
        }
    }

    /// Returns the start time.
    pub fn start_time(&self) -> SimTime {
        self.start_time
    }

    /// Returns the timing vector for the given event.
    pub fn get(&self, event: E) -> Option<&[SimTime]> {
        self.event_timings.get(&event).map(Vec::as_slice)
    }

    /// Iterates over timing vectors for all events.
    pub fn iter(&self) -> impl Iterator<Item = (&E, &[SimTime])> {
        self.event_timings.iter().map(|(k, v)| (k, v.as_slice()))
    }
}

impl<E: Event> Default for Timings<E> {
    fn default() -> Self {
        Self::new(SimTime::ZERO)
    }
}

/// Stats tracker for timings across all events and multiple simulation runs.
pub struct TimingStats<P: Protocol>(HashMap<P::Event, EventTimingStats>);

impl<P: Protocol> TimingStats<P> {
    /// Records the timing statistics for all events.
    ///
    /// Updates the [`EventTimingStats`] corresponding to each event.
    pub fn record_latencies(
        &mut self,
        timings: &mut Timings<P::Event>,
        environment: &SimulationEnvironment,
    ) {
        for (event, timing_vec) in timings.iter() {
            if !event.should_track_stats() {
                continue;
            }
            self.0
                .entry(*event)
                .or_default()
                .record_latencies(timing_vec, environment);
        }
    }

    /// References the [`EventTimingStats`] for the given event, if it exists.
    pub fn get(&self, event: &P::Event) -> Option<&EventTimingStats> {
        self.0.get(event)
    }

    /// Writes percentiles to a CSV file.
    pub fn write_to_csv(
        &self,
        filename: impl AsRef<Path>,
        params: &P::Params,
    ) -> std::io::Result<()> {
        let file = File::create(filename)?;
        let mut writer = BufWriter::new(file);

        // collect all events
        let events = P::Stage::all()
            .iter()
            .flat_map(|stage| {
                stage
                    .events(params)
                    .into_iter()
                    .filter(Event::should_track_stats)
                    .map(|event| (event.name(), event))
            })
            .collect::<Vec<_>>();

        // write header row
        let columns = events
            .iter()
            .map(|(name, _event)| name.to_string())
            .collect::<Vec<_>>();
        let column_str = columns.join(",");
        writeln!(writer, "percentile,{column_str}")?;

        // write data rows
        for percentile in 1..=100 {
            let event_timings = events
                .iter()
                .map(|(_name, event)| {
                    let event_stats = self.get(event).unwrap();
                    event_stats
                        .get_avg_percentile_latency(percentile)
                        .to_string()
                })
                .collect::<Vec<_>>();
            let event_timings_str = event_timings.join(",");
            writeln!(writer, "{percentile},{event_timings_str}")?;
        }

        Ok(())
    }
}

impl<P: Protocol> Default for TimingStats<P> {
    fn default() -> Self {
        Self(HashMap::new())
    }
}

/// Stats tracker for timings of a single event across multiple simulation runs.
pub struct EventTimingStats {
    sum_percentile_latencies: [f64; 100],
    percentile_location: Vec<HashMap<String, f64>>,
    count: u64,
}

impl EventTimingStats {
    /// Updates the aggregate stats based on the timing vector from a single run.
    pub fn record_latencies(&mut self, latencies: &[SimTime], environment: &SimulationEnvironment) {
        let mut latencies = latencies
            .iter()
            .enumerate()
            .map(|(v, l)| (*l, v))
            .collect::<Vec<_>>();
        latencies.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        let percentile_stake = environment.total_stake as f64 / 100.0;
        let mut percentile = 1;
        let mut stake_so_far = 0.0;
        for (latency, v) in latencies {
            let mut validator_stake = environment.validators[v].stake as f64;
            for _ in 0..100 {
                let percentile_stake_left = percentile as f64 * percentile_stake - stake_so_far;
                let abs_stake_contrib = validator_stake.min(percentile_stake_left);
                let rel_stake_contrib = abs_stake_contrib / percentile_stake;
                let latency_contrib = rel_stake_contrib * latency.as_millis();
                self.sum_percentile_latencies[percentile as usize - 1] += latency_contrib;
                let count = self.percentile_location[percentile as usize - 1]
                    .entry(environment.ping_servers[v].location.clone())
                    .or_default();
                *count += abs_stake_contrib;
                stake_so_far += abs_stake_contrib;
                validator_stake -= abs_stake_contrib;
                if percentile < 100 && stake_so_far >= percentile as f64 * percentile_stake {
                    percentile += 1;
                } else {
                    break;
                }
            }
        }
        assert!((stake_so_far - environment.total_stake as f64).abs() < 5000.0);
        assert!(percentile >= 100);
        self.count += 1;
    }

    /// Returns the average timing for a given percentile in milliseconds.
    pub fn get_avg_percentile_latency(&self, percentile: u8) -> f64 {
        assert!(percentile > 0 && percentile <= 100);
        let sum = self.sum_percentile_latencies[percentile as usize - 1];
        sum / self.count as f64
    }
}

impl Default for EventTimingStats {
    fn default() -> Self {
        Self {
            sum_percentile_latencies: [0.0; 100],
            percentile_location: vec![HashMap::new(); 100],
            count: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rotor::LatencyEvent;

    #[test]
    fn basic() {
        let mut time = SimTime::new(1_000_000);
        assert!((time.as_secs() - 1e-3).abs() < f64::EPSILON);
        assert!((time.as_millis() - 1.0).abs() < f64::EPSILON);
        time += SimTime::new(1_000_000);
        assert!((time.as_secs() - 2e-3).abs() < f64::EPSILON);
        assert!((time.as_millis() - 2.0).abs() < f64::EPSILON);

        let time = SimTime::from_secs(0.1);
        assert!((time.as_secs() - 0.1).abs() < f64::EPSILON);
        assert!((time.as_millis() - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn timings() {
        let mut timings = Timings::<LatencyEvent>::default();
        let event = LatencyEvent::BlockSent;
        timings.initialize(event, 2);
        timings.record(event, SimTime::new(10), 0);
        assert_eq!(timings.get(event).unwrap()[0], SimTime::new(10));
        assert_eq!(timings.get(event).unwrap()[1], SimTime::NEVER);
    }

    // #[test]
    // fn stats() {
    //     let mut stats = TimingStats::default();
    //     let mut stats = EventTimingStats::default();
    //     stats.record_latencies(&[], &SimulationEnvironment::new());
    //     assert_eq!(stats.get_avg_percentile_latency(1), 0.0);
    // }
}
