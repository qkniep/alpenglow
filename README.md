# Alpenglow

Research reference implementation of the Alpenglow consensus protocol.

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

TODO: add Alpenglow paper
