#!/bin/bash

cargo build --all-targets --all-features \
    && cargo clippy --all-targets --all-features -- -Dwarnings \
	&& cargo +nightly fmt --check \
	&& cargo doc --no-deps --document-private-items \
	&& cargo machete \
	&& ./test.sh ci
