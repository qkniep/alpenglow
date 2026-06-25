# Local task runner for alpenglow. Run `just` to list recipes.
# Bootstrap `just` itself with `cargo install just`; then run `just setup` to
# install the rest of the dev toolchain.

# Test threads for nextest. Override with `just jobs=8 test` or JOBS=8.
jobs := env_var_or_default("JOBS", "16")

# List available recipes.
default:
    @just --list

# Install the dev tools `just check` and `just test-ci` need. Run once per machine.
setup:
    rustup toolchain install nightly --component rustfmt
    cargo install --locked cargo-nextest cargo-deny cargo-machete cargo-fuzz cargo-llvm-cov typos-cli
    @echo "Also install editorconfig-checker:"
    @echo "  go install github.com/editorconfig-checker/editorconfig-checker/v3/cmd/editorconfig-checker@latest"

# Full local check suite (mirrors the core CI). Roughly the old check.sh.
check: _check-tools editorconfig fmt clippy build doc deny machete typos fuzz-build test-ci

# Check formatting (nightly rustfmt).
fmt:
    cargo +nightly fmt --all -- --check

# Lint with clippy, denying warnings.
clippy:
    cargo clippy --all-targets --all-features -- -D warnings

# Build all targets in debug mode, all features. `--locked` enforces a fresh lockfile.
build: _lockfile
    cargo build --all-targets --all-features --locked

# Build the documentation, denying warnings (mirrors CI and docs.rs conventions).
doc: _lockfile
    RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --document-private-items --all-features --locked

# Check the dependency tree (advisories, licenses, bans, sources).
deny:
    cargo deny check

# Find unused dependencies.
machete:
    cargo machete

# Check spelling.
typos:
    typos

# Lint the GitHub Actions workflows.
actionlint:
    actionlint

# Check that all files follow the editorconfig.
editorconfig:
    editorconfig-checker

# Default test suite: fast tests, all targets/features.
test: _lockfile
    RUST_BACKTRACE=1 cargo nextest run --all-targets --all-features --test-threads={{ jobs }}

# Documentation tests (nextest doesn't run these).
test-doc: _lockfile
    RUST_BACKTRACE=1 cargo test --doc --all-features

# Ignored-by-default smoke tests, in release mode.
test-smoke: _lockfile
    RUST_BACKTRACE=1 cargo nextest run --all-features --release \
        --test smoke_tests --run-ignored=all

# Performance-sensitive tests that must run sequentially, in release mode.
test-sequential: _lockfile
    RUST_BACKTRACE=1 cargo nextest run --release --jobs=1 --run-ignored=only \
        network::simulated::core::tests::asymmetric \
        network::simulated::core::tests::symmetric \
        network::simulated::token_bucket::tests::extreme_rate \
        max_crashes \
        repair::tests::repair_large_block \
        three_nodes_crash

# What CI runs: fast + doc + smoke + sequential.
test-ci: test test-doc test-smoke test-sequential

# Full slow suite (release ignored-only then fast). May take ~10 minutes.
test-slow:
    cargo nextest run --release --jobs=1 --run-ignored=only
    RUST_BACKTRACE=1 cargo nextest run

# Run the fast + sequential suite 50 times to surface flaky tests.
test-many:
    #!/usr/bin/env bash
    set -euo pipefail
    for i in $(seq 1 50); do
        echo "Iteration $i/50:"
        if ! { just test && just test-sequential; }; then
            echo "❌ Test failed in one iteration, maybe some tests are flaky."
            exit 1
        fi
    done

# Build all fuzz targets (compile-check only).
fuzz-build:
    cargo +nightly fuzz build

# Run every fuzz target for 30s.
fuzz:
    #!/usr/bin/env bash
    set -euo pipefail
    host=$(rustc -vV | sed -n 's/^host: //p')
    targets=$(cargo +nightly fuzz list)
    if [ -z "$targets" ]; then
        echo "⚠️  No fuzz targets found, skipping."
        exit 0
    fi
    for target in $targets; do
        echo "Fuzzing $target..."
        cargo +nightly fuzz run --target "$host" "$target" -- -max_total_time=30
    done

# Compile-check benchmarks. CI never runs benches.
# `test-utils` unlocks the slice/`SlotState` helpers that most benches need.
bench-build: _lockfile
    cargo bench --no-run --locked --features test-utils

# Run benchmarks (divan). For local profiling only.
bench:
    cargo bench --features test-utils

# Generate an HTML coverage report and open it.
coverage:
    cargo llvm-cov --all-features --open nextest

# Revert every SHA-pinned action (@<sha> # vX) to its mutable tag (@vX). Use sparingly.
# Actions ship SHA-pinned for supply-chain safety; run this once if you'd rather
# track tags. The new ref is read from the `# vX` comment. Dependabot updates either form.
unpin:
    #!/usr/bin/env bash
    set -euo pipefail
    find .github -type f \( -name '*.yml' -o -name '*.yaml' \) -print0 \
        | xargs -0 perl -i -pe 's/uses:(\s*)([^@\s]+)@[0-9a-fA-F]{40}\s+#\s+(\S+)/uses:$1$2\@$3/g'
    echo "Unpinned all actions to tag refs. Review with: git diff .github"

# List unfinished work: todo!/unimplemented! macros and TODO-style comments.
todo:
    -rg 'todo!\(\)|unimplemented!\(\)' --iglob='!Justfile'
    -rg 'TODO|XXX|HACK|PERF|FIXME|BUG' --iglob='!Justfile'

# Ensure a Cargo.lock exists before the `--locked` recipes run (hidden helper).
_lockfile:
    [ -f Cargo.lock ] || cargo generate-lockfile

# Report any tools `just check` needs that aren't installed (hidden helper).
_check-tools:
    #!/usr/bin/env bash
    set -euo pipefail
    missing=()
    command -v cargo-nextest         >/dev/null 2>&1 || missing+=("cargo-nextest")
    command -v cargo-deny            >/dev/null 2>&1 || missing+=("cargo-deny")
    command -v cargo-machete         >/dev/null 2>&1 || missing+=("cargo-machete")
    command -v cargo-fuzz            >/dev/null 2>&1 || missing+=("cargo-fuzz")
    command -v typos                 >/dev/null 2>&1 || missing+=("typos-cli")
    command -v editorconfig-checker  >/dev/null 2>&1 || missing+=("editorconfig-checker")
    cargo +nightly fmt --version     >/dev/null 2>&1 || missing+=("nightly rustfmt")
    if [ ${#missing[@]} -ne 0 ]; then
        echo "Missing tools: ${missing[*]}" >&2
        echo "Run \`just setup\` to install most of them (editorconfig-checker is a Go binary)." >&2
        exit 1
    fi
