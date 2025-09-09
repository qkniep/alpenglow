// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::borrow::Cow;

use alpenglow::{create_test_nodes, logging};
use color_eyre::Result;
use fastrace::collector::Config;
use fastrace::prelude::*;
use fastrace_opentelemetry::OpenTelemetryReporter;
use log::warn;
use opentelemetry::{InstrumentationScope, KeyValue};
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use opentelemetry_sdk::Resource;

#[tokio::main]
async fn main() -> Result<()> {
    // enable fancy `color_eyre` error messages
    color_eyre::install()?;

    // enable `fastrace` tracing
    let reporter = OpenTelemetryReporter::new(
        SpanExporter::builder()
            .with_tonic()
            .with_endpoint("http://127.0.0.1:4317".to_string())
            .with_protocol(opentelemetry_otlp::Protocol::Grpc)
            .with_timeout(opentelemetry_otlp::OTEL_EXPORTER_OTLP_TIMEOUT_DEFAULT)
            .build()
            .expect("initialize oltp exporter"),
        Cow::Owned(
            Resource::builder()
                .with_attributes([KeyValue::new("service.name", "alpenglow-main")])
                .build(),
        ),
        InstrumentationScope::builder("alpenglow")
            .with_version(env!("CARGO_PKG_VERSION"))
            .build(),
    );
    fastrace::set_reporter(reporter, Config::default());

    logging::enable_logforth();

    {
        let parent = SpanContext::random();

        // spawn local cluster
        let nodes = create_test_nodes(2);
        let mut node_tasks = Vec::new();
        let mut cancel_tokens = Vec::new();
        for (i, node) in nodes.into_iter().enumerate() {
            let span_name = format!("node {i}");
            let span = Span::root(span_name, parent);
            cancel_tokens.push(node.get_cancel_token());
            node_tasks.push(tokio::spawn(node.run().in_span(span)));
        }

        tokio::signal::ctrl_c().await.unwrap();
        warn!("shutting down all nodes");
        for token in &cancel_tokens {
            token.cancel();
        }
        futures::future::join_all(node_tasks).await;
    }

    fastrace::flush();

    Ok(())
}
