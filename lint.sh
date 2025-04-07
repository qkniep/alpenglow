cargo clippy --all-targets --all-features -- -W clippy::pedantic -W clippy::nursery -W clippy::cargo -A clippy::module_name_repetitions -A clippy::missing_errors_doc
cargo +nightly udeps
tokei
