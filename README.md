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
