// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Smoke tests for all Alpenglow binaries.
//!
//! These tests ensure that each binary at least starts up correctly, preventing
//! regressions where a binary becomes broken and cannot be invoked.

use std::io::Write;

use assert_cmd::cargo_bin_cmd;

#[test]
fn local_cluster_help() {
    cargo_bin_cmd!("local_cluster")
        .arg("--help")
        .assert()
        .success();
}

#[test]
fn node_help() {
    cargo_bin_cmd!("node").arg("--help").assert().success();
}

#[test]
fn node_generate_config_files() {
    let dir = tempfile::tempdir().unwrap();

    let ip_file_path = dir.path().join("ips.txt");
    let mut ip_file = std::fs::File::create(&ip_file_path).unwrap();
    writeln!(ip_file, "127.0.0.1:8000").unwrap();
    writeln!(ip_file, "127.0.0.1:8100").unwrap();

    let config_prefix = dir.path().join("node").to_str().unwrap().to_string();

    cargo_bin_cmd!("node")
        .arg("--generate-config-files")
        .arg(&ip_file_path)
        .arg("--config-name")
        .arg(&config_prefix)
        .assert()
        .success();

    assert!(dir.path().join("node_0.toml").exists());
    assert!(dir.path().join("node_1.toml").exists());
}

#[test]
fn all2all_test_help() {
    cargo_bin_cmd!("all2all_test")
        .arg("--help")
        .assert()
        .success();
}

#[test]
fn workload_generator_help() {
    cargo_bin_cmd!("workload_generator")
        .arg("--help")
        .assert()
        .success();
}

#[test]
fn simulations_help() {
    cargo_bin_cmd!("simulations")
        .arg("--help")
        .assert()
        .success();
}

#[test]
fn performance_test_help() {
    cargo_bin_cmd!("performance_test")
        .arg("--help")
        .assert()
        .success();
}

/// Runs the performance test for a few seconds to verify it makes progress.
/// Marked as `#[ignore]` to keep it out of the default fast test suite;
/// run via `./test.sh smoke` or `cargo nextest run --test smoke_tests --run-ignored=all`.
#[test]
#[ignore]
fn performance_test_short() {
    cargo_bin_cmd!("performance_test")
        .arg("--duration-secs")
        .arg("5")
        .assert()
        .success();
}
