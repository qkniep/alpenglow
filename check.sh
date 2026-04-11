#!/bin/bash

cargo clippy --all-targets --all-features -- -Dwarnings \
	&& cargo +nightly fmt --check \
	&& cargo doc --no-deps --document-private-items \
	&& cargo machete \
	&& cargo +nightly fuzz build \
	&& ./test.sh ci
