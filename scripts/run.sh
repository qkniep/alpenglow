#!/usr/bin/env bash
set -euo pipefail

BINS=(
    "all2all_test:cli"
    "local_cluster:cli"
    "node:cli"
    "performance_test:cli"
    "simulations:cli,simulations"
    "workload_generator:cli"
)

print_help() {
    echo "usage: $(basename "$0") <bin> [-- args...]"
    echo "bins:"
    for entry in "${BINS[@]}"; do
        printf "  %-22s (features: %s)\n" "${entry%%:*}" "${entry#*:}"
    done
}

if [[ $# -lt 1 || "$1" == "-h" || "$1" == "--help" ]]; then
    print_help
    exit 0
fi

FEATURES=""
for entry in "${BINS[@]}"; do
    if [[ "${entry%%:*}" == "$1" ]]; then
        FEATURES="${entry#*:}"
        break
    fi
done

if [[ -z "$FEATURES" ]]; then
    echo "error: unknown bin '$1'" >&2
    print_help >&2
    exit 1
fi

export RUST_LOG="${RUST_LOG:-alpenglow=debug}"
export RUST_BACKTRACE="${RUST_BACKTRACE:-1}"

exec cargo run --release --bin="$1" --features="${FEATURES}" "${@:2}"