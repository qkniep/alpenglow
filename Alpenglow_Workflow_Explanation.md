# Alpenglow: End-to-End Workflow and Feature Explanation

## Introduction

Alpenglow is a research reference implementation of a high-performance, proof-of-stake blockchain consensus protocol. It's designed for distributed systems where multiple nodes (computers) need to agree on the state of data (like transactions in a blockchain). The project is written in Rust and focuses on features like erasure coding, data dissemination, and fault tolerance.

This document explains how Alpenglow works from end to end, covering all major features, modules, and workflows based on the source code. We'll break it down step by step, assuming no prior knowledge.

## What is a Consensus Protocol?

In a distributed system, nodes communicate over a network. They need to agree on:
- What data (blocks) to add to the chain.
- Who gets to propose new data.
- How to handle failures (e.g., nodes going offline).

Alpenglow uses:
- **Proof-of-Stake**: Nodes "stake" value to participate (not compute power like Bitcoin).
- **Erasure Coding**: Data is split into pieces (shreds) for redundancy and efficiency.
- **Leader Election**: Random leaders propose blocks based on stake.
- **Voting and Finalization**: Nodes vote to approve blocks, making them permanent.

## Architecture Overview

The codebase is organized into modules in `src/`:

- **`main.rs`**: Entry point for the `alpenglow` binary (runs a local 2-node cluster).
- **`lib.rs`**: Main library exports, defines types like `ValidatorId`, `Stake`, `BlockId`.
- **`consensus/`**: Core protocol logic (voting, blocks, finalization).
- **`shredder/`**: Splits blocks into shreds using erasure coding.
- **`disseminator/`**: Spreads shreds to nodes (Rotor/Turbine algorithms).
- **`network/`**: Handles UDP communication between nodes.
- **`repair/`**: Reconstructs missing data from shreds.
- **`crypto/`**: Hashing, signatures, aggregate signatures.
- **`all2all/`**: All-to-all communication (simple broadcast).
- **`validator/`**: Individual node logic.
- **`types/`**: Common data types (Slot, Block, etc.).
- **`logging/`**: Logging setup.
- **`test_utils/`**: Helpers for testing.

Binaries in `src/bin/`:
- **`alpenglow`**: Main cluster runner.
- **`simulations`**: Test protocol under different conditions.
- **`node`**: Standalone node for multi-node tests.
- **`all2all_test`**, **`performance_test`**, **`workload_generator`**: Specialized tests.

## End-to-End Workflow

Here's how Alpenglow processes data from start to finish:

### 1. Setup and Initialization
- **Nodes Start**: Each node runs as a `Validator` with an ID, stake, and keys.
- **Cluster Formation**: Nodes connect via UDP (e.g., localhost ports). No gossip—peers are predefined.
- **Epoch Info**: Defines the current "epoch" (period) with validators, stakes, and slots.
- **Key Components Initialized**:
  - `Blockstore`: Stores shreds and reconstructed blocks per slot.
  - `Pool`: Manages votes and certificates.
  - `Votor`: Handles voting logic.
  - `BlockProducer`: Creates new blocks.
  - `Disseminator`: Spreads data (uses Rotor or Turbine).
  - `Repair`: Fixes missing data.

### 2. Block Production
- **Leader Selection**: Based on stake-weighted randomness, a node is chosen to produce a block for the current slot.
- **Block Creation**: The producer generates a block containing transactions (up to `MAX_TRANSACTION_SIZE`).
- **Shredding**: The block is split into shreds using Reed-Solomon erasure coding (in `shredder/`).
  - Shreds are small, redundant pieces. If some are lost, the block can be reconstructed.
  - Each shred has a header (slot, slice index, index in slice) and payload.

### 3. Data Dissemination
- **Spreading Shreds**: The disseminator sends shreds to other nodes.
  - **Rotor**: Stake-weighted sampling for efficient, fault-tolerant spread.
  - **Turbine**: Tree-based dissemination for large networks.
- **Network Layer**: Uses UDP for fast, unreliable transport. Messages include shreds, votes, certs.
- **All-to-All**: Simple broadcast for small clusters.

### 4. Shred Reception and Reconstruction
- **Receiving Shreds**: Nodes receive shreds via network.
- **Validation**: Check signatures, duplicates (drop if already seen).
- **Reconstruction**:
  - Collect shreds for a slice (group of shreds).
  - Use erasure coding to rebuild the slice.
  - Combine slices into the full block.
- **Repair**: If shreds are missing, request them from peers.

### 5. Voting and Notarization
- **Votor Logic**: When a block is reconstructed, the node votes.
  - **Notarization Vote**: Approves the block if conditions met (e.g., valid parent).
  - Uses aggregate signatures for efficiency.
- **Certificates**: Votes are aggregated into certs (Notar, NotarFallback, Final, etc.).
- **Pool Management**: Tracks certs per slot, handles duplicates.

### 6. Finalization
- **Fast Finalization**: Quick agreement on a block.
- **Slow Finalization**: Thorough checks for permanence.
- **Pruning**: Old data is cleaned up to save space.

### 7. Continuous Operation
- Slots advance in time windows.
- Nodes produce, disseminate, vote, and finalize in a loop.
- Handles failures: Nodes can crash/rejoin, data is repaired.

## Key Features Explained

### Erasure Coding (Shredder)
- **Purpose**: Makes data resilient to loss. Split blocks into shreds; reconstruct with fewer than all shreds.
- **Implementation**: Uses Reed-Solomon codes. Configurable redundancy.
- **Workflow**: Block → Shreds → Network → Reconstruction → Block.

### Dissemination Algorithms
- **Rotor**: Probabilistic, stake-weighted. Samples peers to send data, reducing load.
- **Turbine**: Hierarchical tree for scalability.
- **Sampling Strategy**: Stake-weighted sampler ensures high-stake nodes get priority.

### Consensus Mechanism
- **Slots and Epochs**: Time divided into slots (atomic units), grouped into epochs.
- **Voting Types**: Notar (approve), Final (commit), Skip (miss slot).
- **Aggregate Signatures**: Combine multiple signatures into one for efficiency.

### Networking
- **UDP**: Fast but unreliable. Handles packet loss.
- **Simulated Network**: For testing delays/latency.
- **TCP/UDP Variants**: Different transports for different needs.

### Repair System
- **Detection**: If shreds are missing, trigger repair.
- **Requests**: Ask peers for missing shreds.
- **Reconstruction**: Use erasure codes to fill gaps.

### Cryptography
- **Hashing**: SHA-256 or similar for block IDs.
- **Signatures**: BLS for aggregate sigs.
- **Keys**: Secret/public keys per validator.

### Testing and Simulations
- **Simulations**: Test latency, bandwidth, rotor safety.
- **Benchmarks**: Performance tests (e.g., crypto, network).
- **Unit Tests**: Check individual components.

## Running the Project

### Prerequisites
- Rust (install via rustup.rs).
- Git.

### Basic Run
1. Clone: `git clone https://github.com/suchit1010/alpenglow.git`
2. Build: `cargo build --release`
3. Run cluster: `./run.sh` (starts 2 nodes on localhost).

### Simulations
1. Download data: `./download_data.sh`
2. Run: `RUST_LOG="simulations=debug" cargo run --release --bin=simulations`

### Tests
- Basic: `./test.sh`
- Full: `./test.sh slow`
- Bench: `cargo bench`

### Standalone Nodes
1. Create `ip_list` file with addresses.
2. Generate configs: `cargo run --release --bin node -- --generate-config-files ip_list --config-name ag_node`
3. Run: `cargo run --release --bin node -- --config-name ag_node_0.toml &` (repeat for each).

## Debugging

See the main README.md for detailed debugging info, including log interpretation and verbose commands.

## References

- [Alpenglow Whitepaper](https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view?usp=sharing)
- [Kudzu](https://arxiv.org/pdf/2505.08771)
- [DispersedSimplex](https://iacr.steepath.eu/2023/1916-DispersedSimplexsimpleandefficientatomicbroadcast.pdf)
- [Simplex](https://eprint.iacr.org/2023/463.pdf)
- [Banyan](https://arxiv.org/pdf/2312.05869v3)
- [Solana Whitepaper](https://solana.com/solana-whitepaper.pdf)

This covers the full workflow and features. If you have questions on specific parts, ask!