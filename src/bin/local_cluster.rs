// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use alpenglow::{create_test_nodes, logging};
use anyhow::Result;
use clap::Parser;
use fastrace::prelude::*;
use log::warn;

/// Local Alpenglow cluster for testing and development.
#[derive(Debug, Parser)]
#[command(version, about)]
struct Args {}

#[tokio::main]
#[hotpath::main]
async fn main() -> Result<()> {
    Args::parse();

    // enable `fastrace` tracing via OpenTelemetry export (only with `telemetry` feature)
    #[cfg(feature = "telemetry")]
    logging::enable_otel_tracing("alpenglow-main")?;

    logging::enable_logforth();

    {
        let parent = SpanContext::random();

        // spawn local cluster
        let nodes = create_test_nodes(6);
        let mut node_tasks = Vec::new();
        let mut cancel_tokens = Vec::new();
        for (i, node) in nodes.into_iter().enumerate() {
            let span_name = format!("node {i}");
            let span = Span::root(span_name, parent);
            cancel_tokens.push(node.get_cancel_token());
            node_tasks.push(tokio::spawn(node.run().in_span(span)));
        }

        tokio::signal::ctrl_c().await?;
        warn!("shutting down all nodes");
        for token in &cancel_tokens {
            token.cancel();
        }
        futures::future::join_all(node_tasks).await;
    }

    fastrace::flush();

    Ok(())
}
