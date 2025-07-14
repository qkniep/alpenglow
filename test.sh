#!/bin/bash

slow_tests () {
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
}

fast_tests () {
	echo "🚀 Running fast tests!"
	sleep 1
	RUST_BACKTRACE=1 cargo nextest run
}

sequential_tests () {
	echo "Running sequential tests!"
	sleep 1
	RUST_BACKTRACE=1 cargo test --release -- test-threads=1 --ignored \
		network::simulated::core::tests::asymmetric \
		network::simulated::core::tests::symmetric
}

if [ $# -gt 0 ] && [ $1 == "slow" ]; then
	slow_tests
elif [ $# -gt 0 ] && [ $1 == "ci" ]; then
	fast_tests && \
		sequential_tests
elif [ $# -gt 0 ] && [ $1 == "sequential" ]; then
	sequential_tests
else
	fast_tests
fi
