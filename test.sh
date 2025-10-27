#!/bin/bash

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
	RUST_BACKTRACE=1 cargo nextest run --all-targets
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

if [ $# -gt 0 ] && [ $1 == "slow" ]; then
	slow_tests
elif [ $# -gt 0 ] && [ $1 == "ci" ]; then
	fast_tests && doc_tests && sequential_tests
elif [ $# -gt 0 ] && [ $1 == "doc" ]; then
	doc_tests
elif [ $# -gt 0 ] && [ $1 == "sequential" ]; then
	sequential_tests
elif [ $# -gt 0 ] && [ $1 == "many" ]; then
	echo "🔁 Running tests for 50 iterations to detect flaky tests..."
	for i in $(seq 1 50); do
		echo "Iteration $i/50:"
		fast_tests && sequential_tests
		if [ $? -ne 0 ]; then
            echo "❌ Test failed in one iteration, maybe some tests are flaky."
            break
        fi
    done
else
	fast_tests
fi
