#!/bin/bash

if [ $# -gt 0 ] && [ $1 == "slow" ]; then
	echo "🐌 Running slow tests can take up to 10 minutes!"
	echo "Starting in 3 seconds..."
	sleep 3
	# run performance tests in release mode (others run in debug mode)
	cargo test --release -- --test-threads=1 --ignored \
		high_bandwidth \
		unlimited_bandwidth \
		turbine_sampler \
		turbine_sampler_real_world \
		only_correct_nodes \
		many_nodes \
		single_crash \
		max_fast_crashes \
		too_many_fast_crashes \
		max_crashes \
		too_many_crashes \
		three_nodes \
		three_nodes_crash && \
	RUST_BACKTRACE=1 cargo test
else
	echo "🚀 Running fast tests only!"
	sleep 1
	RUST_BACKTRACE=1 cargo nextest run
fi
