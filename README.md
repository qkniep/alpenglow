# Alpenglow

Research reference implementation of the Alpenglow consensus protocol.

![Latency Histogram for Random Leaders](./latency_histogram.png)

## Getting Started

A local cluster example can be run with the following command:

```bash
./run.sh
```

This spawns a local cluster with 2 nodes.
These nodes communicate via UDP on localhost.
Console output from the [`logforth`](https://docs.rs/logforth) crate shows the progress of all nodes.

Further, we provide the `simulations` binary target.
It provides various simulations of parts of the Alpenglow protocol,
specifically resilience of Rotor, as well as latency and bandwidth requirements of Alpenglow as a whole.
Currently, configuration is a bit cumbersome and is done via the `const` values in `src/bin/simulations/main.rs`.

Some of the simulations, specifically the latency simulation, requires first downloading a public ping dataset via this script:

```bash
./download_data.sh
```

After that, the simulations can be run like this:

```bash
RUST_LOG="simulations=debug" cargo run --release --bin=simulations
```

## Benchmarks

Some micro-benchmarks can be run like this:

```bash
cargo bench
```

## Tests

Regular tests can be run like this:

```bash
./test.sh
```

The more extensive test suite, including some slow tests, can be run like this:

```bash
./test.sh slow
```

## Debugging

The Alpenglow implementation uses the [`logforth`](https://docs.rs/logforth) crate for logging. By default, the `run.sh` script sets `RUST_LOG="alpenglow=debug"` to show debug-level logs for the `alpenglow` crate, along with `RUST_BACKTRACE=1` to enable stack traces on panics.

### Interpreting Logs

When running the local cluster with `./run.sh`, you'll see logs like:

- **DEBUG dropping duplicate shred X-Y in slot Z**: Indicates a duplicate data fragment (shred) was received and ignored. This is normal in distributed systems for redundancy.
- **DEBUG reconstructed block HASH in slot Z with parent HASH in slot W**: A block was successfully assembled from shreds.
- **DEBUG voted notar for slot Z**: The node voted to approve (notarize) a block.
- **INFO producing block in slot Z with ready parent HASH in slot W**: Starting production of a new block.
- **DEBUG produced block Z in TIME ms**: A block was created, with production time.
- **INFO notarized(-fallback) block HASH in slot Z**: A block was notarized (approved by votes).
- **INFO fast finalized slot Z** / **INFO slow finalized slot Z**: The slot (and its block) is permanently committed.

### Enabling Verbose Debugging

To see more details, including function inputs/outputs added for debugging:

1. Run with full debug logging:
   ```bash
   RUST_LOG="alpenglow=debug,blockstore=debug,pool=debug,votor=debug,block_producer=debug" RUST_BACKTRACE=1 cargo run --release --bin=alpenglow
   ```

2. This will show additional debug prints like:
   - `add_validated_shred: slot=X, slice_index=Y, shred_index=Z`
   - `send_votor_event: event=Block { ... }`
   - `try_notar: slot=X, hash=Y, parent_slot=Z, parent_hash=W`
   - `produce_block_parent_ready: slot=X, parent_slot=Y, parent_hash=Z`

### Common Debugging Scenarios

- **No progress (blocks not advancing)**: Check for network issues (UDP ports blocked) or missing shreds (look for "repairing" logs).
- **Crashes**: Enable `RUST_BACKTRACE=1` and share the stack trace.
- **Performance**: Block production times >500ms may indicate CPU/network bottlenecks.
- **Simulations not working**: Ensure `./download_data.sh` was run for latency simulations.

For protocol details, refer to the [Alpenglow Whitepaper](https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view?usp=sharing).

## Standalone node

There is a rudimentary implementation of a standalone node in the `node` binary. To use it, please do the folowing.

### Define the cluster
Since there is no gossip and stake manipulation in this prototype, you need to define all peers manually in advance. To do that, prepare a text file defining the socket addresses of the nodes that will be used in the test, e.g.
```csv
127.0.0.1:3000
127.0.0.1:3005
127.0.0.1:3010
127.0.0.1:3015
```
Obviously, you can use any IP addresses here, as long as they are reachable. Only first out of 5 needed ports is specified, the others are port+1, ..., port+4.

### Generate config files for the nodes

```► cargo run --release --bin node -- --generate-config-files ip_list --config-name ag_node```

will produce a config file starting with ```ag_node``` for each socket address found in ```ip_list``` file.

### Run the nodes
You may want to use multiple terminals or a script to start the nodes:
``` bash
cargo run --release --bin node -- --config-name ag_node_0.toml &
cargo run --release --bin node -- --config-name ag_node_1.toml &
cargo run --release --bin node -- --config-name ag_node_2.toml &
cargo run --release --bin node -- --config-name ag_node_3.toml
```

You should be able to take one node offline and bring it back up at will without cluster stopping.

## Security

For security related issues, please do not file a public issue on GitHub,
instead reach out directly via email to:

quentin (at) anza (dot) xyz

## License

Copyright (c) Anza Technology, Inc.

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

### Literature

- [Alpenglow Whitepaper](https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view?usp=sharing)
- [Kudzu](https://arxiv.org/pdf/2505.08771)
- [DispersedSimplex](https://iacr.steepath.eu/2023/1916-DispersedSimplexsimpleandefficientatomicbroadcast.pdf)
- [Simplex](https://eprint.iacr.org/2023/463.pdf)
- [Banyan](https://arxiv.org/pdf/2312.05869v3)
- [Solana (TowerBFT) Whitepaper](https://solana.com/solana-whitepaper.pdf)

### Other Resources

- [Alpenglow Presentation (YouTube)](https://www.youtube.com/watch?v=x1sxtm-dvyE)
- [Alpenglow Presentation (Slides)](https://disco.ethz.ch/members/wroger/AlpenglowPresentation.pdf)
- [Anza Blog Post](https://www.anza.xyz/blog/alpenglow-a-new-consensus-for-solana)
- [Helius Blog Post](https://www.helius.dev/blog/alpenglow)
- [Agave + Alpenglow Prototype](https://github.com/anza-xyz/alpenglow)
