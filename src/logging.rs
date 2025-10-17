// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use colored::{Color, ColoredString, Colorize};
use logforth::filter::env_filter::EnvFilterBuilder;
use logforth::record::Level;
use logforth::{Layout, append};

#[derive(Clone, Debug, Default)]
struct MinimalLogforthLayout {
    colors: LevelColor,
}

impl Layout for MinimalLogforthLayout {
    fn format(
        &self,
        record: &logforth::record::Record,
        _diagnostics: &[Box<dyn logforth::Diagnostic>],
    ) -> Result<Vec<u8>, logforth::Error> {
        let level = self.colors.colorize_record_level(false, record.level());
        let message = record.payload();
        Ok(format!("{level:>5} {message}").into_bytes())
    }
}

pub fn enable_logforth() {
    let layout = MinimalLogforthLayout::default();
    enable_logforth_append(append::Stderr::default().with_layout(layout));
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

/// Colors for different log levels.
#[derive(Debug, Clone)]
pub struct LevelColor {
    /// Color for error level logs.
    pub error: Color,
    /// Color for warning level logs.
    pub warn: Color,
    /// Color for info level logs.
    pub info: Color,
    /// Color for debug level logs.
    pub debug: Color,
    /// Color for trace level logs.
    pub trace: Color,
}

impl Default for LevelColor {
    fn default() -> Self {
        Self {
            error: Color::Red,
            warn: Color::Yellow,
            info: Color::Green,
            debug: Color::Blue,
            trace: Color::Magenta,
        }
    }
}

impl LevelColor {
    /// Colorize the log level.
    fn colorize_record_level(&self, no_color: bool, level: Level) -> ColoredString {
        if no_color {
            ColoredString::from(level.to_string())
        } else {
            let color = match level {
                Level::Error => self.error,
                Level::Warn => self.warn,
                Level::Info => self.info,
                Level::Debug => self.debug,
                Level::Trace => self.trace,
            };
            ColoredString::from(level.to_string()).color(color)
        }
    }
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
