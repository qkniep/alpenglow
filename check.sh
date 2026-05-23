#!/bin/bash

set -euo pipefail

# fail fast if a tool is missing
require() {
    command -v "$1" >/dev/null 2>&1 || { echo "❌ missing: $1 — $2"; exit 1; }
}

# check for required tools
require editorconfig-checker "install with: go install github.com/editorconfig-checker/editorconfig-checker/v3/cmd/editorconfig-checker@latest"
require cargo-machete "install with: cargo install cargo-machete"
require cargo-fuzz    "install with: cargo install cargo-fuzz"
require cargo-nextest "install with: cargo install cargo-nextest"
rustup toolchain list | grep -q '^nightly' \
    || { echo "❌ missing nightly toolchain — install with: rustup toolchain install nightly"; exit 1; }

# run all checks
editorconfig-checker
cargo build --all-targets --all-features
cargo clippy --all-targets --all-features -- -Dwarnings
cargo +nightly fmt --check
cargo doc --no-deps --document-private-items
cargo machete
cargo +nightly fuzz build
./test.sh ci
