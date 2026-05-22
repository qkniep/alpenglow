// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

#[cfg(feature = "telemetry")]
use std::borrow::Cow;

use colored::{Color, ColoredString, Colorize};
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
    OTEL_EXPORTER_OTLP_TIMEOUT_DEFAULT, Protocol, SpanExporter, WithExportConfig,
};
#[cfg(feature = "telemetry")]
use opentelemetry_sdk::Resource;

/// Endpoint used for OTLP trace export when `OTEL_EXPORTER_OTLP_ENDPOINT` is unset.
#[cfg(feature = "telemetry")]
const DEFAULT_OTLP_ENDPOINT: &str = "http://127.0.0.1:4317";

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

/// Sets up `fastrace` to export spans to an OpenTelemetry collector over OTLP/gRPC.
///
/// The collector endpoint is read from the standard `OTEL_EXPORTER_OTLP_ENDPOINT`
/// environment variable, falling back to [`DEFAULT_OTLP_ENDPOINT`] for local runs.
///
/// Callers must invoke [`fastrace::flush`] on shutdown to avoid losing buffered spans.
#[cfg(feature = "telemetry")]
pub fn enable_otel_tracing(service_name: &str) {
    let endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| DEFAULT_OTLP_ENDPOINT.to_string());
    let reporter = OpenTelemetryReporter::new(
        SpanExporter::builder()
            .with_tonic()
            .with_endpoint(endpoint)
            .with_protocol(Protocol::Grpc)
            .with_timeout(OTEL_EXPORTER_OTLP_TIMEOUT_DEFAULT)
            .build()
            .expect("initialize otlp exporter"),
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
