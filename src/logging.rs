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
    logforth::builder()
        .dispatch(|d| d.filter(EnvFilter::from_default_env()).append(to_append))
        .apply();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        enable_logforth();
        log::trace!("trace");
        log::debug!("debug");
        log::info!("info");
        log::warn!("warn");
        log::error!("error");
    }
}
