# Alpenglow benchmark orchestrator

Scaffolding for running real-world Alpenglow benchmarks on a cloud testbed.
The design follows the [Mysticeti orchestrator][mysticeti]: a small provider
trait abstracts the cloud APIs, an SSH layer drives the machines, and a protocol
adapter knows how to build and run the Alpenglow `node`.

> **Status:** first-pass scaffolding. The **custom** (bring-your-own-IPs)
> provider works end-to-end. The **Vultr** provider is wired against the real v2
> API but is untested against a live account (a couple of `TODO`s remain, e.g.
> polling new instances until they boot). The **AWS** provider is a compiling
> stub — every method returns "not implemented".

## Layout

```
orchestrator/
├─ src/
│  ├─ main.rs        # CLI: status / deploy / install / benchmark / start / stop / destroy
│  ├─ settings.rs    # YAML settings (+ ${ENV} expansion) and the CloudProvider enum
│  ├─ benchmark.rs   # BenchmarkParameters
│  ├─ provider.rs    # Instance, ServerProviderClient trait, CloudClient dispatch enum
│  ├─ provider/
│  │  ├─ custom.rs   # bring-your-own machines (works)
│  │  ├─ vultr.rs    # Vultr v2 API client (wired, untested)
│  │  └─ aws.rs      # stub
│  ├─ ssh.rs         # shells out to system ssh/scp
│  ├─ alpenglow.rs   # protocol adapter: genesis / node / load-gen commands
│  └─ testbed.rs     # lifecycle glue
└─ assets/           # settings + benchmark templates
```

Adding a provider means implementing `ServerProviderClient` and adding one
`CloudClient` variant — nothing else changes.

## Prerequisites

- `ssh` and `scp` on your `PATH` (used directly, not linked).
- An SSH keypair; the public key is registered with the provider on `deploy`.
- For Vultr: a `VULTR_API_TOKEN` environment variable.

## Workflow

1. Copy a template from `assets/` to `orchestrator/assets/settings.yml` and edit it.
2. Provision (cloud providers only — skip for `custom`):
   ```bash
   cargo run -p orchestrator -- deploy --instances-per-region 2
   ```
3. Build the node on every machine:
   ```bash
   cargo run -p orchestrator -- install
   ```
4. Run a benchmark:
   ```bash
   cargo run -p orchestrator -- benchmark --nodes 4 --load 5000 --duration 120
   # or: benchmark --parameters orchestrator/assets/benchmark-parameters-template.yml
   ```
5. Inspect / tear down:
   ```bash
   cargo run -p orchestrator -- status
   cargo run -p orchestrator -- destroy
   ```

All commands take `--settings <path>` (default `orchestrator/assets/settings.yml`).

## How a benchmark run works

`node --generate-config-files <socket_list> --config-name ag_node` generates
**fresh random keypairs** for every validator and writes one `ag_node_<id>.toml`
per node (each holding that node's secret keys plus the public gossip list of
all nodes). Because the keys are random, the orchestrator:

1. runs genesis **once** on the first instance,
2. downloads each `ag_node_<id>.toml` and uploads it to the matching node,
3. starts every `node`, then a `workload_generator` against node 0,
4. waits `duration_secs`, kills everything, and downloads the logs to `logs/`.

Each node binds `base_port..base_port + 5` (all-to-all, disseminator, two repair
sockets, and transactions on `base_port + 4`). **Open UDP `base_port..base_port+4`
and TCP 22** in your firewall / cloud security group, or nodes can't reach each
other.

## Notes & next steps

- The orchestrator is a separate workspace member so its cloud/SSH dependencies
  never touch the consensus build. To keep it out of `just check`/`just test`
  entirely, change `members` to `exclude` in the root `Cargo.toml`.
- Metrics: the node currently logs throughput/latency rather than exposing a
  Prometheus endpoint. A natural next step is a `collector` module (à la
  Mysticeti) once the node serves `/metrics`.
- TLS uses `native-tls` (not rustls) to keep the dependency tree on the
  cargo-deny license allowlist; see the note in `Cargo.toml`.

[mysticeti]: https://github.com/asonnino/mysticeti/tree/main/crates/orchestrator
