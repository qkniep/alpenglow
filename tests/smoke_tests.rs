// Copyright (c) Anza Technology, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Smoke tests for all Alpenglow binaries.
//!
//! These tests ensure that each binary starts up correctly and runs successfully,
//! preventing regressions where a binary becomes broken and cannot be invoked.
//!
//! Tests are organized in two tiers:
//! - **Help tests** (fast, always run): verify the CLI parses and the binary links.
//! - **Launch tests** (slow, `#[ignore]`): actually start the binary, let it run for
//!   a few seconds, and verify it makes progress. Run via `./test.sh smoke` or
//!   `cargo nextest run --test smoke_tests --run-ignored=all`.

use std::io::{Read, Write};
use std::process::Stdio;
use std::time::Duration;

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

/// Generates per-node config files from an IP list and checks the files exist.
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

/// Launches a 2-node local cluster and verifies it keeps running and finalizes
/// at least one slot within 15 seconds.
#[test]
#[ignore]
fn local_cluster_short() {
    // `assert_cmd::Command` doesn't expose `spawn()`, so use `std::process::Command`
    // directly with the Cargo-provided binary path.
    let bin = env!("CARGO_BIN_EXE_local_cluster");
    let mut child = std::process::Command::new(bin)
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn local_cluster");

    // Read stderr in a background thread so the pipe buffer never fills up and
    // blocks the child process while we wait.
    let stderr_pipe = child.stderr.take().unwrap();
    let reader = std::thread::spawn(move || {
        let mut buf = String::new();
        std::io::BufReader::new(stderr_pipe)
            .read_to_string(&mut buf)
            .unwrap();
        buf
    });

    // Give the cluster time to elect a leader and finalize a few slots.
    std::thread::sleep(Duration::from_secs(15));

    // Verify the process is still alive — a crash would show up here.
    assert!(
        child.try_wait().unwrap().is_none(),
        "local_cluster exited unexpectedly before being killed"
    );

    child.kill().unwrap();
    child.wait().unwrap();

    let stderr = reader.join().unwrap();
    assert!(
        stderr.contains("finalized slot"),
        "expected at least one finalized slot in stderr output, got:\n{stderr}"
    );
}

/// Runs the performance test (11 nodes, simulated network) for 5 seconds and
/// verifies that nodes actually finalize blocks, not just that the binary exits.
#[test]
#[ignore]
fn performance_test_short() {
    let output = cargo_bin_cmd!("performance_test")
        .arg("--duration-secs")
        .arg("5")
        .output()
        .expect("failed to run performance_test");

    assert!(
        output.status.success(),
        "performance_test exited with non-zero status: {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("finalized new block"),
        "expected to see block finalization progress in stderr, got:\n{stderr}"
    );
}

// NOTE: `simulations` does not have a launch smoke test.
// The binary takes many minutes to complete - too long for this test.
// The help test above verifies the binary compiles adn starts up correctly.
