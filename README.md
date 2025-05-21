# Alpenglow

Research reference implementation of the Alpenglow consensus protocol.

![Latency Histogram for Random Leaders](./latency_histogram.png)

## Getting Started

A local cluster example can be run with the following command:

```bash
./run.sh
```

This spawns a local cluster with 6 nodes.
These nodes communicate via UDP on localhost.
Console output from the `tracing` crate shows the progress of all nodes.

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

## Security

## License

Copyright (c) Anza Technology, Inc.

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## Literature

- [Alpenglow Whitepaper](https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view?usp=sharing)
- [Anza Blog Post](https://www.anza.xyz/blog/alpenglow-a-new-consensus-for-solana)
