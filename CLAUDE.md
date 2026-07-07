# CLAUDE.md

Guidance for Claude Code (claude.ai/code) when working in this repository.

## Project Overview

Alpenglow is a research reference implementation of the Alpenglow consensus
protocol — a high-performance, global Proof-of-Stake blockchain consensus system
with erasure coding for data availability. Written in Rust for distributed systems
research.

## Essential Commands

Dev tasks run through a `Justfile` (`cargo install just`; `just` lists recipes,
`just setup` installs the toolchain once per machine). Only `run.sh` and
`download_data.sh` remain of the old `*.sh` scripts.

### Build and Run
```bash
cargo build --release                          # Build in release mode
./run.sh                                       # Run local cluster (alpenglow=debug)
RUST_LOG="alpenglow=debug" cargo run --release --bin=local_cluster
cargo run --release --bin=simulations          # Run protocol simulations
```
Other binaries: `node`, `all2all_test`, `performance_test`, `workload_generator`.

### Testing (`cargo-nextest`, not `cargo test`)
```bash
just test                    # Fast tests (default), all targets/features
just test-doc                # Doctests (nextest doesn't run these)
just test-smoke              # Ignored-by-default smoke tests, release mode
just test-sequential         # Perf-sensitive tests that must run with --jobs=1
just test-ci                 # Full CI: test + test-doc + test-smoke + test-sequential
just test-slow               # Full slow suite (~10 min)
just test-many               # Run fast+sequential 50x to surface flaky tests
cargo nextest run <name>     # Run a specific test directly
```

### Linting and Quality
```bash
just check                   # Full local CI: editorconfig, fmt, clippy, build, doc, deny, machete, typos, license, fuzz-build, test-ci
just fmt                     # cargo +nightly fmt --all -- --check
just clippy                  # cargo clippy --all-targets --all-features -- -D warnings
just doc                     # cargo doc with -D warnings
```

### Benchmarks & Simulations
```bash
just bench                   # All micro-benchmarks (divan); CI never runs benches
cargo bench --bench crypto   # Specific bench (crypto, disseminator, network, shredder)
./download_data.sh           # Required before latency simulations (ping dataset)
```

## Architecture Overview

### Core Components
- **Alpenglow** (`src/consensus.rs`) — consensus coordinator; async message loops
  wiring together `All2All`, `Disseminator`, `Blockstore`, `Pool`, `Votor`.
- **Validator** (`src/validator.rs`) — pairs an `Alpenglow` instance with an
  `ExecutionEngine` to form a full node.
- **Blockstore** (`src/consensus/blockstore.rs`) — stores shreds, reconstructs blocks.
- **Pool** (`src/consensus/pool.rs`) — tracks votes/certs, manages finalization.
- **Votor** (`src/consensus/votor.rs`) — per-slot voting state machine.

```
Leader → Shredder → Disseminator → Network
                                      ↓
Network → Repair (if needed) → Blockstore → Pool → Votor → All2All → Certificates
```

### Networks
Independent channels, each trait-abstracted (`All2All`, `Disseminator`,
`Network<Send, Recv>`) with UDP / TCP / simulated impls:
- **All2All** (`src/all2all/`) — broadcasts votes and certs to all validators.
- **Disseminator** (`src/disseminator/`) — spreads block shreds (Rotor or Turbine).
- **Repair** (`src/repair.rs`) — point-to-point recovery of missing shreds. Each
  response carries a `DoubleMerkleProof`, so untrusted sources can't corrupt data.
  Requests: `LastSliceRoot`, `SliceRoot`, `Shred`; stake-weighted target sampling.
- **Transaction network** — receives incoming transactions.

### Shredding
Blocks split into **slices**; each slice Reed-Solomon-coded into **shreds**:
```
Block → Slices (fixed-size chunks)
Each Slice → n data + (k−n) coding = k shreds
```
- **Shredder** (`src/shredder.rs`) — encodes slices. Impls: `RegularShredder`,
  `CodingOnlyShredder` (DA-focused), `AontShredder`/`PetsShredder` (all-or-nothing).
- **Double-Merkle** — block tree over slice roots, per-slice tree over shreds. A
  `Shred` is one UDP packet with slice header, Merkle proof, and leader signature.

### Consensus Flow
1. **Produce** (`block_producer.rs`) — leader shreds its block and sends via
   disseminator (`DELTA_BLOCK` 400ms, `DELTA_FIRST_SLICE` 10ms).
2. **Reconstruct** — validators collect shreds; n-of-k reconstructs the block →
   `VotorEvent::BlockReconstructed` (via `Blockstore::add_shred_from_disseminator`).
   `Votor` then decides whether to vote based on parent availability.
3. **Vote** (`votor.rs`) — per-slot state machine reacts to block/cert/timeout
   events, emits `Vote`s (Notar/Confirm/Finalize) over `All2All`.
4. **Certify** (`pool.rs`) — `Pool` aggregates votes; at 2/3+ stake forms a `Cert`
   (BLS aggregate signature) that drives the next phase and tracks finalization.
5. **Repair** (`repair.rs`) — see Networks above.

### Dissemination Protocols
- **Rotor** (`src/disseminator/rotor/`) — primary protocol; a Turbine evolution with
  push-based probabilistic forwarding and configurable sampling (uniform,
  stake-weighted, Fait Accompli, decaying acceptance).
- **Turbine** (`src/disseminator/turbine/`) — Solana's tree-based protocol,
  deterministic routing by node position.

### Cryptography (`src/crypto/`)
- **Ed25519** (`signature.rs`) — block/shred signatures with batch verification.
- **BLS12-381** (`aggsig.rs`, via `blst`) — aggregate signatures for compact certs.
- **Double-Merkle** (`merkle.rs`) — `MerkleRoot`/`MerkleTree`/`MerkleProof`; per-shred
  verification during repair. SHA-256 for hashing / content addressing.

### Execution Engine
`ExecutionEngine` (`src/execution.rs`) bridges consensus and transaction execution,
running alongside consensus and reporting back over an `ExecutionEvent` channel.
Four ops: `begin_block` (first slice), `execute_transactions` (per slice, pipelined),
`end_block` (last slice), `finalize` (commit state, prune unreachable forks). A
placeholder impl lives in the same module.

### Simulations
The `simulations` binary (`src/bin/simulations/`) runs discrete-event sims — latency
(real ping data), bandwidth/throughput, and crash/Byzantine robustness — for Rotor,
Alpenglow, Ryse, and Pyjama (one module each). Uses real validator distributions
(Solana/Sui mainnet) and ping datasets (`data/pings-*.csv`). Configure via constants
at the top of `src/bin/simulations/main.rs` (`RUN_*_TESTS`, `SAMPLING_STRATEGIES`,
`SHRED_COMBINATIONS`, `MAX_BANDWIDTHS`).

## Key Types and Abstractions

### Core Types (`src/types/`, `src/lib.rs`)
Domain scalars are **newtypes** (mostly tuple structs wrapping `u64`), not bare
aliases — each in its own module under `src/types/`, re-exported from `types`:
```rust
struct Slot(u64);                          // src/types/slot.rs
struct Stake(u64);                         // src/types/stake.rs
struct ValidatorIndex(u64);                // src/types/validator_index.rs (NOT `ValidatorId`)
struct SliceIndex(u64);                    // src/types/slice_index.rs
struct Fraction { numerator, denominator } // src/types/fraction.rs
```
The only bare aliases are `type BlockId = (Slot, BlockHash)` (`src/lib.rs`) and
`type BlockHash = DoubleMerkleRoot` (`src/crypto/merkle.rs`). Prefer the newtype
(with its `.inner()` / constructor API) over raw `u64`; new domain quantities should
follow the same pattern rather than aliasing `u64`.

### Message Types
Serialized via `wincode` (custom library): `ConsensusMessage` (votes and certs),
`Shred`, `RepairRequest`/`RepairResponse`, `Transaction`.

### Timing Constants (`src/consensus.rs`)
```rust
DELTA = 250ms              // Network synchrony bound
DELTA_BLOCK = 400ms        // Leader block production time
DELTA_FIRST_SLICE = 10ms   // First slice send deadline
DELTA_TIMEOUT = 750ms      // Base voting timeout (3 * DELTA)
DELTA_STANDSTILL = 10s     // Standstill detection timeout
```

## Testing Patterns

- **Unit tests**: `#[cfg(test)] mod tests` at the bottom of each file.
- **Integration tests**: `tests/` (`liveness.rs`, `smoke_tests.rs`).
- **Slow/perf tests**: `#[ignore]` (run via `just test-smoke` / `just test-slow`).
- **Sequential tests**: need `--jobs=1` (run via `just test-sequential`).
- **Test cluster**: `create_test_nodes(count)` (`src/lib.rs`, helpers in
  `src/test_utils.rs`) returns `Vec<TestNode>` on localhost UDP.
- **Mocks**: `mockall` `#[automock]` gives `MockDisseminator`, `MockNetwork`, etc.

## Conventions

### File Structure
1. Copyright + SPDX header  2. Module doc comment (`//!`)  3. Submodule decls
4. Imports (std, external, internal)  5. Public items  6. Private items
7. `#[cfg(test)] mod tests`

### Code Style

- **Equalizing operand types**: When two sides of a comparison (`==`, `assert_eq!`,
  etc.) differ only by a reference level, prefer lifting both to a reference with
  `&` over lowering both to a value with `*` — e.g. `assert_eq!(&hash, block_hash)`
  or `assert_eq!(hash, &block_hash)`, not `assert_eq!(*hash, block_hash)`. The two
  forms compile identically (the comparison macros re-borrow), but `&` doesn't imply
  a move/copy that isn't happening and reads the same whether or not the type is
  `Copy`. Keep this consistent within a file.

#### Formatting (`rustfmt.toml`, `.editorconfig`)

- **rustfmt runs on nightly** (`cargo +nightly fmt`) because the config uses
  unstable options: `edition = "2024"`, `group_imports = "StdExternalCrate"`
  (three import groups — std, external crates, then `crate`/`super`/`self`),
  `imports_granularity = "Module"` (one `use` per module path, not merged trees or
  one-per-item), and `use_field_init_shorthand`. Match these when writing imports by
  hand rather than relying on the formatter to fix them.
- **Indentation is spaces**, width 4 for `*.rs`/`*.py`/`*.sh` and 2 for
  `*.json`/`*.toml`/`*.yml`/`*.yaml` (Markdown is unconstrained). Files are UTF-8,
  LF line endings, with a trailing newline and no trailing whitespace (except
  Markdown). Enforced by `just editorconfig`.

#### Doc comments (`///`, `//!`)

- **Mood & structure**: Write item docs in the third-person present indicative, as
  rustdoc convention dictates — "Creates a new `Votor` instance.", "Returns the slot
  this vote is for.", "`Votor` implements the decision process…". Not imperative
  ("Create…"), not "This function…". The first line is a single-sentence summary;
  if more is needed, add a blank `///` line, then the details.
- **Intra-doc links**: Reference other items with rustdoc link syntax
  ``[`Name`]`` — e.g. ``[`ValidatedVote`]``, ``[`All2All`]``,
  ``[`super::Pool::finalized_slot`]`` — not plain backticked text. This is enforced
  in spirit by `just doc` (rustdoc runs with `-D warnings`), so broken links fail CI.
- **Fallible fns get an `# Errors` section** describing which error variant is
  returned when; see `ValidatedVote::try_new`. Public getters that would be misused
  if ignored are marked `#[must_use]`.
- Every source file starts with the two-line copyright + SPDX header (checked by
  `just license`) and, for modules, a `//!` module doc comment.

#### Non-doc comments (`//`)

- **Tag callout comments with an uppercase prefix + colon**, matching
  existing usage: `// NOTE:` (non-obvious invariant or subtlety), `// PERF:`
  (a deliberate performance choice), `// SAFETY:` (justifies an `unsafe` block or a
  panic-avoidance guard), `// TODO:` (deferred work), `// HACK:` (known-ugly
  workaround). Plain explanatory comments need no tag.
- Comments explain *why*, not *what* the code already says.

#### Error handling

- **`thiserror` for library errors, `anyhow` for binaries/glue.** Public/library
  fallible APIs return a typed `pub enum XxxError` deriving `thiserror::Error`.
  Binaries (`src/bin/*`) and top-level orchestration (`consensus.rs`) use `anyhow`
  where a typed error buys nothing.
- **Error message style**: `#[error("…")]` messages are lowercase and have no
  trailing period ("`signer is not a validator in the current epoch`"). Name the
  enum `<Thing>Error` or `<Thing>ValidationError`; give each variant a `///` doc
  line in addition to its `#[error]` message.
- **`Validated*` newtype pattern**: To make "this value passed verification" a
  type-level invariant, wrap the raw type in a `Validated*` newtype whose only
  constructor is a fallible `try_new(...) -> Result<Self, XxxValidationError>` that
  runs the checks. Downstream code takes the `Validated*` type and can assume it is
  well-formed. Examples: `ValidatedVote`, `ValidatedCert`, `ValidatedShred`.
- **Panic policy**: Never panic on untrusted input (peer messages, network bytes,
  byzantine data) — reject it with a `Result` instead. `try_new`-style validators
  guard *before* any indexing/slicing that could panic on adversarial input (see
  the `UnknownSigner` bounds check in `ValidatedVote::try_new`). Reserve
  `expect()`/`unwrap()` (prefer `expect()`, with a message documenting the
  invariant) for genuine *local* invariants that cannot fail.

## Gotchas & Notes

- **64-bit assumption**: code assumes `usize == 8 bytes`; 32-bit unsupported.
- **`--release`**: always use it for realistic performance testing.
- **Logging**: control levels via the `RUST_LOG` env var (`logforth` crate).
- **Standstill recovery**: after `DELTA_STANDSTILL` with no progress, the
  `standstill_loop` in `Alpenglow` calls `Pool::recover_from_standstill()` (repair
  requests for missing blocks).
- **Leader schedule**: `EpochInfo::leader(slot)` — deterministic, stake-weighted
  random over slot + validator set (`src/consensus/epoch_info.rs`).

### Adding a Dissemination Protocol
Create a module in `src/disseminator/`, implement `Disseminator` (`send`, `forward`,
`receive`) generic over `Network<Shred, Shred>` and `SamplingStrategy`, export from
`src/disseminator.rs`, wire into `create_test_nodes` (`lib.rs`) and add a sim variant
in `src/bin/simulations/` as needed.

## References

- [Alpenglow Whitepaper](https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view)
- [Alpenglow Presentation](https://www.youtube.com/watch?v=x1sxtm-dvyE)
- Related protocols: Kudzu, DispersedSimplex, Simplex, Banyan, Solana TowerBFT
