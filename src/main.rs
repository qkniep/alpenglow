// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::borrow::Cow;
use std::sync::Arc;

use alpenglow::ValidatorInfo;
use alpenglow::all2all::TrivialAll2All;
use alpenglow::consensus::{Alpenglow, EpochInfo};
use alpenglow::crypto::aggsig;
use alpenglow::crypto::signature::SecretKey;
use alpenglow::disseminator::Rotor;
use alpenglow::disseminator::rotor::StakeWeightedSampler;
use alpenglow::network::UdpNetwork;
use color_eyre::Result;
use fastrace::collector::Config;
use fastrace::prelude::*;
use fastrace_opentelemetry::OpenTelemetryReporter;
use log::warn;
use logforth::color::LevelColor;
use logforth::filter::EnvFilter;
use logforth::{Layout, append};
use opentelemetry::trace::SpanKind;
use opentelemetry::{InstrumentationScope, KeyValue};
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use opentelemetry_sdk::Resource;
use rand::rng;

#[derive(Debug, Clone, Copy)]
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
        SpanKind::Server,
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

    // enable `logforth` logging
    logforth::builder()
        .dispatch(|d| {
            d.filter(EnvFilter::from_default_env())
                .append(append::Stderr::default().with_layout(MinimalLogforthLayout))
        })
        .apply();

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

type TestNode =
    Alpenglow<TrivialAll2All<UdpNetwork>, Rotor<UdpNetwork, StakeWeightedSampler>, UdpNetwork>;

fn create_test_nodes(count: u64) -> Vec<TestNode> {
    // prepare validator info for all nodes
    let mut port = 3000;
    let mut rng = rng();
    let mut sks = Vec::new();
    let mut voting_sks = Vec::new();
    let mut validators = Vec::new();
    for id in 0..count {
        sks.push(SecretKey::new(&mut rng));
        voting_sks.push(aggsig::SecretKey::new(&mut rng));
        validators.push(ValidatorInfo {
            id,
            stake: 1,
            pubkey: sks[id as usize].to_pk(),
            voting_pubkey: voting_sks[id as usize].to_pk(),
            all2all_address: format!("127.0.0.1:{}", port),
            disseminator_address: format!("127.0.0.1:{}", port + 1),
            repair_address: format!("127.0.0.1:{}", port + 2),
        });
        port += 3;
    }

    // turn validator info into actual nodes
    validators
        .iter()
        .map(|v| {
            let epoch_info = Arc::new(EpochInfo::new(v.id, validators.clone()));
            let start_port = 3000 + v.id * 3;
            let network = UdpNetwork::new(start_port as u16);
            let all2all = TrivialAll2All::new(validators.clone(), network);
            let network = UdpNetwork::new(start_port as u16 + 1);
            let disseminator = Rotor::new(network, epoch_info.clone());
            let repair_network = UdpNetwork::new(start_port as u16 + 2);
            Alpenglow::new(
                sks[v.id as usize].clone(),
                voting_sks[v.id as usize].clone(),
                all2all,
                disseminator,
                repair_network,
                epoch_info,
            )
        })
        .collect()
}
