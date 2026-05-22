// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

#[cfg(feature = "telemetry")]
use std::borrow::Cow;
use std::io::{IsTerminal, stderr};

#[cfg(feature = "telemetry")]
use fastrace::collector::Config;
#[cfg(feature = "telemetry")]
use fastrace_opentelemetry::OpenTelemetryReporter;
use logforth::filter::env_filter::EnvFilterBuilder;
use logforth::record::Level;
use logforth::{Layout, append};
#[cfg(feature = "telemetry")]
use opentelemetry::{InstrumentationScope, KeyValue};
#[cfg(feature = "telemetry")]
use opentelemetry_otlp::{
    ExporterBuildError, OTEL_EXPORTER_OTLP_TIMEOUT_DEFAULT, Protocol, SpanExporter,
    WithExportConfig,
};
#[cfg(feature = "telemetry")]
use opentelemetry_sdk::Resource;
use owo_colors::{AnsiColors, OwoColorize};

/// Endpoint used for OTLP trace export when `OTEL_EXPORTER_OTLP_ENDPOINT` is unset.
#[cfg(feature = "telemetry")]
const DEFAULT_OTLP_ENDPOINT: &str = "http://127.0.0.1:4317";

#[derive(Clone, Debug)]
struct MinimalLogforthLayout {
    /// Whether to emit ANSI color codes. Disabled when stderr is not a terminal
    /// or the `NO_COLOR` environment variable is set.
    colorize: bool,
}

impl MinimalLogforthLayout {
    fn new() -> Self {
        let colorize = stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none();
        Self { colorize }
    }

    fn level_color(level: Level) -> AnsiColors {
        match level {
            Level::Fatal | Level::Fatal2 | Level::Fatal3 | Level::Fatal4 => AnsiColors::BrightRed,
            Level::Error | Level::Error2 | Level::Error3 | Level::Error4 => AnsiColors::Red,
            Level::Warn | Level::Warn2 | Level::Warn3 | Level::Warn4 => AnsiColors::Yellow,
            Level::Info | Level::Info2 | Level::Info3 | Level::Info4 => AnsiColors::Green,
            Level::Debug | Level::Debug2 | Level::Debug3 | Level::Debug4 => AnsiColors::Blue,
            Level::Trace | Level::Trace2 | Level::Trace3 | Level::Trace4 => AnsiColors::Magenta,
        }
    }
}

impl Layout for MinimalLogforthLayout {
    fn format(
        &self,
        record: &logforth::record::Record,
        _diagnostics: &[Box<dyn logforth::Diagnostic>],
    ) -> Result<Vec<u8>, logforth::Error> {
        let level = record.level();
        // Pad the level name to width 5 *before* coloring so the ANSI escape
        // codes don't throw off the alignment.
        let padded = format!("{:>5}", level.to_string());
        let message = record.payload();
        let line = if self.colorize {
            format!("{} {message}", padded.color(Self::level_color(level)))
        } else {
            format!("{padded} {message}")
        };
        Ok(line.into_bytes())
    }
}

/// Sets up `fastrace` to export spans to an OpenTelemetry collector over OTLP/gRPC.
///
/// The collector endpoint is read from the standard `OTEL_EXPORTER_OTLP_ENDPOINT`
/// environment variable, falling back to [`DEFAULT_OTLP_ENDPOINT`] for local runs.
///
/// Returns an error if the OTLP exporter cannot be built (e.g., the endpoint URL
/// is malformed). Callers must invoke [`fastrace::flush`] on shutdown to avoid
/// losing buffered spans.
#[cfg(feature = "telemetry")]
pub fn enable_otel_tracing(service_name: &str) -> Result<(), ExporterBuildError> {
    let endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .ok()
        .filter(|s| !s.trim().is_empty())
        .unwrap_or_else(|| DEFAULT_OTLP_ENDPOINT.to_string());
    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_protocol(Protocol::Grpc)
        .with_timeout(OTEL_EXPORTER_OTLP_TIMEOUT_DEFAULT)
        .build()?;
    let reporter = OpenTelemetryReporter::new(
        exporter,
        Cow::Owned(
            Resource::builder()
                .with_attributes([KeyValue::new("service.name", service_name.to_string())])
                .build(),
        ),
        InstrumentationScope::builder("alpenglow")
            .with_version(env!("CARGO_PKG_VERSION"))
            .build(),
    );
    fastrace::set_reporter(reporter, Config::default());
    Ok(())
}

pub fn enable_logforth() {
    enable_logforth_append(append::Stderr::default().with_layout(MinimalLogforthLayout::new()));
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
