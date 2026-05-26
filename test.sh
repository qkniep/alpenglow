#!/bin/bash

set -euo pipefail

# fail fast if a tool is missing
require() {
    command -v "$1" >/dev/null 2>&1 || { echo "❌ missing: $1 — $2"; exit 1; }
}

slow_tests () {
    echo "🐌 Running slow tests can take up to 10 minutes!"
    echo "Starting in 3 seconds..."
    sleep 3
    # run performance tests sequentially in release mode
    cargo nextest run --release --jobs=1 --run-ignored=only
    # run other tests in parallel in debug mode
    RUST_BACKTRACE=1 cargo nextest run
}

fast_tests () {
    echo "🚀 Running fast tests!"
    sleep 1
    RUST_BACKTRACE=1 cargo nextest run --all-targets --all-features
}

doc_tests () {
    echo "📜 Running documentation tests!"
    sleep 1
    RUST_BACKTRACE=1 cargo test --doc
}

sequential_tests () {
    echo "🦥 Running sequential tests!"
    sleep 1
    RUST_BACKTRACE=1 cargo nextest run --release --jobs=1 --run-ignored=only \
        network::simulated::core::tests::asymmetric \
        network::simulated::core::tests::symmetric \
        network::simulated::token_bucket::tests::extreme_rate \
        max_crashes \
        repair::tests::repair_large_block \
        three_nodes_crash
}

fuzz_tests () {
    echo "🧪 Running fuzz tests!"
    sleep 1
    require cargo-fuzz "install with: cargo install cargo-fuzz"
    require rustc "install the Rust toolchain via rustup"
    local targets host
    # Pin to the host triple: prebuilt cargo-fuzz binaries default to their own
    # musl-static target, which is ASAN-incompatible and usually not installed.
    host=$(rustc -vV | sed -n 's/^host: //p')
    if ! targets=$(cargo +nightly fuzz list); then
        echo "❌ Failed to list fuzz targets (nightly toolchain + cargo-fuzz installed?)"
        return 1
    fi
    if [ -z "$targets" ]; then
        echo "⚠️  No fuzz targets found, skipping."
        return 0
    fi
    for target in $targets; do
        echo "Fuzzing $target..."
        cargo +nightly fuzz run --target "$host" "$target" -- -max_total_time=30 || return 1
    done
}

smoke_tests () {
    echo "🔥 Running smoke tests!"
    sleep 1
    RUST_BACKTRACE=1 cargo nextest run --all-features --release \
        --test smoke_tests --run-ignored=all
}

many_tests () {
    echo "🔁 Running tests for 50 iterations to detect flaky tests..."
    for i in $(seq 1 50); do
        echo "Iteration $i/50:"
        # Guard with `if` so `set -e` doesn't abort before we can report flakiness.
        if ! { fast_tests && sequential_tests; }; then
            echo "❌ Test failed in one iteration, maybe some tests are flaky."
            break
        fi
    done
}

# every mode but `doc` and `fuzz` needs cargo-nextest
case "${1:-}" in
    doc|fuzz) ;;
    *) require cargo-nextest "install with: cargo install cargo-nextest" ;;
esac

case "${1:-}" in
    slow) slow_tests ;;
    ci) fast_tests && doc_tests && smoke_tests && sequential_tests ;;
    doc) doc_tests ;;
    sequential) sequential_tests ;;
    fuzz) fuzz_tests ;;
    smoke) smoke_tests ;;
    many) many_tests ;;
    "") fast_tests ;;  # default: fast suite
    *)
        echo "❌ unknown mode: $1" >&2
        echo "usage: ${0##*/} [slow|ci|doc|sequential|fuzz|smoke|many]" >&2
        exit 1
        ;;
esac
