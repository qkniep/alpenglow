cargo clippy --all-targets --all-features -- -Dwarnings
cargo machete
./test.sh ci
