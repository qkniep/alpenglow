// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use colored::{Color, ColoredString, Colorize};
use logforth::filter::env_filter::EnvFilterBuilder;
use logforth::record::Level;
use logforth::{Layout, append};

#[derive(Clone, Debug)]
struct MinimalLogforthLayout;

impl MinimalLogforthLayout {
    fn colorize_record_level(&self, level: Level) -> ColoredString {
        let color = match level {
            Level::Fatal | Level::Fatal2 | Level::Fatal3 | Level::Fatal4 => Color::BrightRed,
            Level::Error | Level::Error2 | Level::Error3 | Level::Error4 => Color::Red,
            Level::Warn | Level::Warn2 | Level::Warn3 | Level::Warn4 => Color::Yellow,
            Level::Info | Level::Info2 | Level::Info3 | Level::Info4 => Color::Green,
            Level::Debug | Level::Debug2 | Level::Debug3 | Level::Debug4 => Color::Blue,
            Level::Trace | Level::Trace2 | Level::Trace3 | Level::Trace4 => Color::Magenta,
        };
        ColoredString::from(level.to_string()).color(color)
    }
}

impl Layout for MinimalLogforthLayout {
    fn format(
        &self,
        record: &logforth::record::Record,
        _diagnostics: &[Box<dyn logforth::Diagnostic>],
    ) -> Result<Vec<u8>, logforth::Error> {
        let level = self.colorize_record_level(record.level());
        let message = record.payload();
        Ok(format!("{level:>5} {message}").into_bytes())
    }
}

pub fn enable_logforth() {
    enable_logforth_append(append::Stderr::default().with_layout(MinimalLogforthLayout));
}

pub fn enable_logforth_stderr() {
    enable_logforth_append(append::Stderr::default());
}

fn enable_logforth_append<A: logforth::Append>(to_append: A) {
    let filter = EnvFilterBuilder::from_default_env_or("info").build();
    logforth::starter_log::builder()
        .dispatch(|d| d.filter(filter).append(to_append))
        .apply();
}

#[cfg(test)]
mod tests {
    use log::{Level, debug, error, info, log_enabled, trace, warn};

    use super::*;

    #[test]
    fn basic() {
        enable_logforth();

        // check logger is enabled with default level of "info"
        assert!(log_enabled!(Level::Error));
        assert!(log_enabled!(Level::Warn));
        assert!(log_enabled!(Level::Info));
        assert!(!log_enabled!(Level::Debug));
        assert!(!log_enabled!(Level::Trace));

        trace!("trace");
        debug!("debug");
        info!("info");
        warn!("warn");
        error!("error");
    }
}
