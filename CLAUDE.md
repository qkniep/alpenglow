# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Alpenglow is a research reference implementation of the Alpenglow consensus protocol - a high-performance, global Proof-of-Stake blockchain consensus system with erasure coding for data availability. The project is written in Rust and designed for distributed systems research.

## Essential Commands

Dev tasks run through a `Justfile` (install with `cargo install just`; run `just`
to list recipes, `just setup` once per machine to install the toolchain). The
old `*.sh` scripts are gone — only `run.sh` and `download_data.sh` remain.

### Build and Run
```bash
cargo build --release                          # Build in release mode
./run.sh                                       # Run local cluster (alpenglow=debug)
RUST_LOG="alpenglow=debug" cargo run --release --bin=local_cluster
cargo run --release --bin=simulations          # Run protocol simulations
```
Other binaries: `node`, `all2all_test`, `performance_test`, `workload_generator`.

### Testing
Uses `cargo-nextest` (not `cargo test`):
```bash
just test                    # Fast tests (default), all targets/features
just test-doc                # Doctests (nextest doesn't run these)
just test-smoke              # Ignored-by-default smoke tests, release mode
just test-sequential         # Perf-sensitive tests that must run with --jobs=1
just test-ci                 # Full CI suite: test + test-doc + test-smoke + test-sequential
just test-slow               # Full slow suite (~10 min)
just test-many               # Run fast+sequential 50x to surface flaky tests
cargo nextest run <name>     # Run a specific test directly
```

### Linting and Quality
```bash
just check                   # Full local CI: fmt, clippy, build, doc, deny, machete, typos, fuzz-build, test-ci
just fmt                     # cargo +nightly fmt --all -- --check
just clippy                  # cargo clippy --all-targets --all-features -- -D warnings
just doc                     # cargo doc with -D warnings
```

### Benchmarks
```bash
just bench                   # Run all micro-benchmarks (divan); CI never runs benches
cargo bench --bench crypto   # Specific benchmark (crypto, disseminator, network, shredder)
```

### Simulations
Configure via constants in `src/bin/simulations/main.rs`:
```bash
./download_data.sh           # Required: download ping dataset first
RUST_LOG="simulations=debug" cargo run --release --bin=simulations
```

## Architecture Overview

### Core Components

The consensus protocol is built around three main abstractions that work together:

1. **Alpenglow** (`src/consensus.rs`) - The main consensus coordinator
   - Orchestrates all consensus activity via async message loops
   - Manages the lifecycle of block production, voting, and finalization
   - Connects `All2All`, `Disseminator`, `Blockstore`, `Pool`, and `Votor` components
   - **Validator** (`src/validator.rs`) wraps an `Alpenglow` consensus instance
     together with an `ExecutionEngine` to form a full node.

2. **Block Flow Pipeline**
   ```
   Leader produces block → Shredder → Disseminator → Network
                                                         ↓
   Network → Repair (if needed) → Blockstore → Pool → Votor → All2All → Certificates
   ```

3. **Key State Machines**
   - `Blockstore` (`src/consensus/blockstore.rs`) - Stores shreds and reconstructs blocks
   - `Pool` (`src/consensus/pool.rs`) - Tracks votes and certificates, manages finalization
   - `Votor` (`src/consensus/votor.rs`) - Main voting state machine, produces votes based on events

### Network Architecture

The system uses multiple independent network channels:

- **All2All** (`src/all2all/`) - Broadcasts votes and certificates to all validators
- **Disseminator** (`src/disseminator/`) - Disseminates block shreds (Rotor or Turbine)
- **Repair** (`src/repair.rs`) - Point-to-point repair requests/responses
- **Transaction Network** - Receives incoming transactions

Each network type is abstracted via traits (`All2All`, `Disseminator`, `Network`) with multiple implementations (UDP, TCP, simulated).

### Shredding System

Blocks are split into **slices**, and each slice is erasure-coded into **shreds**:

```
Block → Slices (fixed size chunks)
Each Slice → n data shreds + (k-n) coding shreds = k total shreds
```

- **Shredder** (`src/shredder.rs`) - Encodes slices into shreds with Reed-Solomon erasure coding
- **Merkle Trees** - Double-Merkle structure: Block Merkle tree over slice roots, each slice has its own Merkle tree over shreds
- **Shred** - Single UDP-sized packet with slice header, Merkle proof, and leader signature

Shredder implementations:
- `RegularShredder` - Standard data + coding shreds
- `CodingOnlyShredder` - Only coding shreds (data-availability focused)
- `AontShredder` / `PetsShredder` - All-or-nothing transform variants

### Consensus Flow

1. **Block Production** (`src/consensus/block_producer.rs`)
   - Leader for a slot produces a block
   - Shreds the block and sends via disseminator
   - Timing constraints: `DELTA_BLOCK` (400ms), `DELTA_FIRST_SLICE` (10ms)

2. **Block Reception & Reconstruction**
   - Validators receive shreds via disseminator
   - `Blockstore::add_shred_from_disseminator` stores shreds
   - Once enough shreds received (n out of k), reconstruct full block
   - Triggers `VotorEvent::BlockReconstructed`

3. **Voting** (`src/consensus/votor.rs`)
   - `Votor` maintains voting state machine per slot
   - Reacts to events: block reconstruction, cert reception, timeouts
   - Produces `Vote` messages (Notar, Confirm, Finalize)
   - Broadcasts votes via `All2All`

4. **Certificate Formation** (`src/consensus/pool.rs`)
   - `Pool` aggregates votes into certificates
   - Once supermajority (2/3+ stake) reached, forms `Cert`
   - Certificate triggers next voting phase
   - Tracks finalized blocks and parent-child relationships

5. **Repair** (`src/repair.rs`)
   - Double-Merkle proofs enable individual shred verification
   - Repair requests: `LastSliceRoot`, `SliceRoot`, `Shred`
   - Stake-weighted sampling for repair targets
   - Timeout-based retries with different nodes

### Dissemination Protocols

**Rotor** (`src/disseminator/rotor/`) - Alpenglow's primary dissemination protocol:
- Evolution of Turbine with improved sampling strategies
- Configurable sampling: uniform, stake-weighted, Fait Accompli, decaying acceptance
- Push-based forwarding with probabilistic sampling
- Each node samples next hops based on strategy

**Turbine** (`src/disseminator/turbine/`) - Solana's original protocol:
- Tree-based dissemination
- Deterministic routing based on node positions

### Cryptography

**Signatures** (`src/crypto/signature.rs`):
- Ed25519 for block/shred signatures
- Fast batch verification

**Aggregate Signatures** (`src/crypto/aggsig.rs`):
- BLS signatures on BLS12-381 curve (via `blst`)
- Used for vote aggregation into certificates
- Enables compact certificate proofs

**Merkle Trees** (`src/crypto/merkle.rs`):
- Double-Merkle structure for blocks and slices
- Efficient individual shred verification during repair
- `MerkleRoot`, `MerkleTree`, `MerkleProof` abstractions

**Hashing**:
- SHA-256 for content addressing and Merkle trees

### Execution Engine

`ExecutionEngine` (`src/execution.rs`) is the interface between consensus and
transaction execution. It runs alongside consensus and processes transactions as
they arrive via dissemination, communicating results back over an
`ExecutionEvent` channel. Four operations: `begin_block` (first slice of a new
block), `execute_transactions` (per reconstructed slice, enabling pipelined
execution), `end_block` (last slice received), and `finalize` (block finalized by
consensus — commit state, prune unreachable forks). A placeholder implementation
lives in the same module; `Validator` (`src/validator.rs`) pairs an engine with a
consensus instance.

### Simulations

The `simulations` binary (`src/bin/simulations/`) provides discrete event simulations:

- **Latency Simulation** - Measures end-to-end latency using real-world ping data
- **Bandwidth Simulation** - Tests maximum supported throughput
- **Robustness Tests** - Evaluates safety under crash and Byzantine faults
- **Protocols Simulated**: Rotor, Alpenglow (full protocol), Ryse, Pyjama (one module each under `src/bin/simulations/`)

Simulation infrastructure:
- `discrete_event_simulator/` - Event-driven simulation engine
- Uses real validator distributions (Solana, Sui mainnet data)
- Real network latencies from public ping datasets (`data/pings-*.csv`)

Configure simulations via constants at top of `src/bin/simulations/main.rs`:
- `RUN_BANDWIDTH_TESTS`, `RUN_LATENCY_TESTS`, `RUN_ROTOR_ROBUSTNESS_TESTS`
- `SAMPLING_STRATEGIES`, `SHRED_COMBINATIONS`, `MAX_BANDWIDTHS`

## Key Types and Abstractions

### Core Types (`src/types.rs`, `src/lib.rs`)
```rust
type ValidatorId = u64;
type Stake = u64;
type BlockId = (Slot, BlockHash);
type Slot = types::Slot;  // Newtype wrapper around u64
```

### Trait Boundaries

Most components are generic over these traits:
- `All2All: Send + Sync` - Consensus message broadcasting
- `Disseminator: Send + Sync` - Block dissemination
- `Network<Send, Recv>` - Low-level network abstraction
- `SamplingStrategy` - Validator sampling for dissemination

This enables testing with simulated networks and swapping implementations.

### Message Types

Serialization via `wincode` (custom serialization library):
- `ConsensusMessage` - Votes and certificates
- `Shred` - Block fragments with proofs
- `RepairRequest` / `RepairResponse` - Repair protocol messages
- `Transaction` - User transactions

### Timing Constants (`src/consensus.rs`)

```rust
DELTA = 250ms              // Network synchrony bound
DELTA_BLOCK = 400ms        // Leader block production time
DELTA_FIRST_SLICE = 10ms   // First slice send deadline
DELTA_TIMEOUT = 750ms      // Base voting timeout (3 * DELTA)
DELTA_STANDSTILL = 10s     // Standstill detection timeout
```

## Testing Patterns

### Test Organization
- Unit tests: `#[cfg(test)] mod tests` at bottom of files
- Integration tests: `tests/` directory (`liveness.rs`, `smoke_tests.rs`)
- Slow/performance tests: marked with `#[ignore]` attribute (run via `just test-smoke` / `just test-slow`)
- Sequential tests: require `--jobs=1` to avoid interference (run via `just test-sequential`)

### Common Test Utilities (`src/test_utils.rs`)
- `create_test_nodes(count)` - Sets up local test cluster (defined in `src/lib.rs`, helpers in `src/test_utils.rs`)
- Returns `Vec<TestNode>` with UDP networks on localhost
- Useful for multi-node integration tests

### Async Testing
```rust
#[tokio::test]
async fn test_consensus() {
    let nodes = alpenglow::create_test_nodes(3);
    // ...
}
```

### Mock Objects
Uses `mockall` crate for mocking traits:
- `MockDisseminator`, `MockNetwork` available
- Defined via `#[automock]` attribute on traits

## Development Workflow

### Before Committing
1. `cargo +nightly fmt` - Format code
2. `just clippy` - Lint (`cargo clippy --all-targets --all-features -- -D warnings`)
3. `just test` - Run fast tests
4. Optionally `just check` - Full local CI validation

### File Structure Convention
1. Copyright header (Anza Technology, Apache-2.0)
2. Module doc comment (`//!`)
3. Submodule declarations
4. Imports (std, external, internal)
5. Public items
6. Private items
7. `#[cfg(test)] mod tests` at bottom

### Code Style

- **Equalizing operand types**: When two sides of a comparison (`==`, `assert_eq!`,
  etc.) differ only by a reference level, prefer lifting both to a reference with
  `&` over lowering both to a value with `*` — e.g. `assert_eq!(&hash, block_hash)`
  or `assert_eq!(hash, &block_hash)`, not `assert_eq!(*hash, block_hash)`. The two
  forms compile identically (the comparison macros re-borrow), but `&` doesn't imply
  a move/copy that isn't happening and reads the same whether or not the type is
  `Copy`. Keep this consistent within a file.

### Common Gotchas

- **64-bit assumption**: Code assumes `usize == 8 bytes`, 32-bit architectures unsupported
- **Nextest required**: Use `cargo nextest run`, not `cargo test`
- **Nightly formatting**: `cargo +nightly fmt` (rustfmt.toml uses nightly features)
- **Release builds**: Always use `--release` for realistic performance testing
- **Simulations data**: Run `./download_data.sh` before latency simulations
- **Background logging**: Use `RUST_LOG` env var to control log levels (via `logforth` crate)

### Adding a New Dissemination Protocol

1. Create module in `src/disseminator/`
2. Implement `Disseminator` trait (`send`, `forward`, `receive`)
3. Make generic over `Network<Shred, Shred>` and `SamplingStrategy`
4. Add to `src/disseminator.rs` exports
5. Update `create_test_nodes` in `lib.rs` if needed
6. Add simulation variant in `src/bin/simulations/`

### Adding a New Test

```bash
# Unit test - add to existing file
#[tokio::test]
async fn test_new_feature() { ... }

# Integration test - create tests/new_test.rs
cargo nextest run --test new_test

# Slow test - mark with #[ignore]
#[tokio::test]
#[ignore]
async fn test_performance() { ... }

# Run slow test explicitly
cargo nextest run --run-ignored only test_performance
```

## Important Implementation Details

### Blockstore Event Flow
When a block is fully reconstructed, `Blockstore` sends `VotorEvent::BlockReconstructed` to `Votor` via mpsc channel. The `Votor` then decides whether to vote based on parent availability and other factors.

### Vote Aggregation
Votes use BLS aggregate signatures. The `Pool` accumulates individual votes and when stake threshold reached, aggregates signatures into a single `Cert` with combined signature. This is broadcast to all validators.

### Repair Verification
Each repair response includes a `DoubleMerkleProof` proving the shred belongs to the claimed block. This allows validators to accept repair data from untrusted sources without risk of corruption.

### Standstill Recovery
If no progress detected for `DELTA_STANDSTILL`, the `standstill_loop` in `Alpenglow` triggers `Pool::recover_from_standstill()` which initiates recovery procedures (repair requests for missing blocks).

### Leader Schedule
Leader for a slot determined by `EpochInfo::leader(slot)`, which uses deterministic function of slot number and validator set. Default: stake-weighted random selection (see `src/consensus/epoch_info.rs`).

## References

- [Alpenglow Whitepaper](https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view)
- [Alpenglow Presentation](https://www.youtube.com/watch?v=x1sxtm-dvyE)
- Related protocols: Kudzu, DispersedSimplex, Simplex, Banyan, Solana TowerBFT
