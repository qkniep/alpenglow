// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use logforth::color::LevelColor;
use logforth::filter::EnvFilter;
use logforth::{Layout, append};

#[derive(Clone, Copy, Debug)]
struct MinimalLogforthLayout;

impl Layout for MinimalLogforthLayout {
    fn format(
        &self,
        record: &log::Record,
        _: &[Box<dyn logforth::Diagnostic>],
    ) -> anyhow::Result<Vec<u8>> {
        let colors = LevelColor::default();
        let level = colors.colorize_record_level(false, record.level());
        let message = record.args();
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
    let filter = EnvFilter::from_default_env_or("alpenglow=debug,info");
    logforth::builder()
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
