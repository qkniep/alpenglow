# Alpenglow Formal Verification - Reproduction Guide

This guide provides step-by-step instructions for reproducing the formal verification results of the Alpenglow consensus protocol.

## Prerequisites

### 1. Java Runtime Environment
TLC model checker requires Java 8 or later.

```bash
# Check Java version
java -version
# Should output: java version "1.8.0" or higher
```

### 2. TLA+ Tools
Download the TLA+ toolbox (includes TLC model checker):

```bash
# Download TLA+ tools (tla2tools.jar)
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Or use direct link:
# https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
```

Place `tla2tools.jar` in the root directory of the alpenglow repository.

## File Structure

```
alpenglow/
├── tla2tools.jar                          # TLA+ model checker (download separately)
├── formal-verification/
│   ├── Alpenglow.tla                      # Main TLA+ specification
│   ├── MC.cfg                             # Model configuration
│   ├── MC.tla                             # Model parameters
│   ├── VERIFICATION_REPORT.md             # Detailed verification report
│   └── README.md                          # This file
└── src/                                   # Rust implementation (for reference)
```

## Running the Verification

### Step 1: Navigate to Repository Root

```bash
cd alpenglow
```

### Step 2: Run TLC Model Checker

#### Basic Verification (4 validators, 3 slots)
```bash
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC \
    -deadlock \
    -config formal-verification/MC.cfg \
    formal-verification/Alpenglow.tla
```

#### With More Workers (faster on multi-core systems)
```bash
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC \
    -workers 4 \
    -deadlock \
    -config formal-verification/MC.cfg \
    formal-verification/Alpenglow.tla
```

### Step 3: Interpreting Results

#### Successful Verification Output
```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 2.5E-7
6229333 states generated, 839515 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 19.
Finished in 01min 26s
```

**✅ This means ALL SAFETY INVARIANTS PASSED!**

#### If Invariant Violation Found
TLC will print:
```
Error: Invariant <InvariantName> is violated.
```
Followed by a counter-example trace showing the sequence of states leading to the violation.

## Verified Properties

The model checker verifies the following 12 safety invariants:

### Core Safety Properties
1. **NoConflictingFinalizations** - No two different blocks finalized in same slot
2. **FastFinalImpliesNotar** - Fast finalization requires notarization
3. **FinalRequiresNotar** - Slow finalization requires notarization
4. **ConsistentCertificates** - Certificates reference correct blocks

### Additional Safety Theorems
5. **CertificateUniqueness** - At most one certificate per type per slot
6. **StakeThresholdCorrectness** - Certificates require proper quorums (60%/80%)
7. **ChainConsistency** - Finalized blocks form valid chain
8. **NoEquivocation** - Validators vote at most once per slot
9. **FastPathRequiresStrongQuorum** - Fast path requires 80% stake
10. **FinalizedHaveValidCerts** - Finalized slots have valid certificates
11. **BlocksExistBeforeVoting** - Votes cast after block production
12. **CertificatesRequireVotes** - Certificates created with sufficient votes

## Configuration Options

### Adjusting Model Parameters

Edit `formal-verification/MC.cfg` to change:

```properties
CONSTANTS
    Validators = {"v1", "v2", "v3", "v4"}  # Number of validators
    MaxSlot = 3                             # Maximum slot number
    TotalStake = 100                        # Total stake (distributed equally)
```

**Warning:** Increasing validators or slots significantly increases state space and verification time.

### State Space Estimates

| Validators | MaxSlot | Distinct States | Time (approx) |
|-----------|---------|-----------------|---------------|
| 4         | 3       | ~840K           | 1-2 min       |
| 4         | 4       | ~5M             | 5-10 min      |
| 5         | 3       | ~50M            | 30-60 min     |
| 7         | 3       | TBD             | Hours         |

## Troubleshooting

### Issue: "OutOfMemoryError"
**Solution:** Increase Java heap size
```bash
java -Xmx4g -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC ...
```

### Issue: "Could not find or load main class tlc2.TLC"
**Solution:** Ensure `tla2tools.jar` is in current directory or provide full path
```bash
java -cp /path/to/tla2tools.jar tlc2.TLC ...
```

### Issue: Verification takes too long
**Solution:** 
1. Use multiple workers: `-workers <num_cores>`
2. Reduce model size (fewer validators or slots)
3. Use simulation mode: `-simulate num=1000000`

## Understanding the TLA+ Specification

### Key Files

#### `Alpenglow.tla`
Main specification containing:
- State variables (currentSlot, blocks, votes, certificates, finalized)
- Actions (ProduceBlock, Vote, CreateNotarCert, CreateFinalCert)
- Safety invariants (all properties to verify)
- Helper operators (HasQuorum, HasStrongQuorum, etc.)

#### `MC.cfg`
Configuration file specifying:
- Which specification to check (`SPECIFICATION Spec`)
- Constant values (Validators, MaxSlot, TotalStake)
- Which invariants to verify (`INVARIANTS ...`)

#### `MC.tla`
Model override file (if needed for specific model configurations)

## Correspondence with Rust Implementation

The TLA+ model accurately reflects the Rust implementation:

### Quorum Calculations
**Rust** (`src/consensus/pool/slot_state.rs`):
```rust
pub fn is_quorum(&self, stake: u64) -> bool {
    stake >= (self.total_stake * 3) / 5  // 60%
}
```

**TLA+**:
```tla
IsQuorum(stake) == stake >= (TotalStake * 3) \div 5
```

### Certificate Types
**Rust** (`src/consensus/cert.rs`):
```rust
pub enum Cert {
    NotarCert { ... },
    FastFinalCert { ... },
    FinalCert { ... },
}
```

**TLA+**:
```tla
CertType == {"Notar", "FastFinal", "Final"}
```

## Advanced Usage

### Running Specific Invariants Only

Edit `MC.cfg` to comment out invariants:
```properties
INVARIANTS
    NoConflictingFinalizations
    # FastFinalImpliesNotar  <- commented out
    FinalRequiresNotar
```

### Generating State Graph
```bash
java -cp tla2tools.jar tlc2.TLC \
    -dump dot,colorize,actionlabels state_graph.dot \
    -config formal-verification/MC.cfg \
    formal-verification/Alpenglow.tla
```

Then visualize with Graphviz:
```bash
dot -Tpng state_graph.dot -o state_graph.png
```

### Trace File Generation
Add to `MC.cfg`:
```properties
SPECIFICATION Spec
ALIAS Alias
```

And in `Alpenglow.tla`:
```tla
Alias == [
    slot |-> currentSlot,
    fin |-> finalized
]
```

## Performance Tips

1. **Use ParallelGC:** `-XX:+UseParallelGC` improves performance
2. **Multiple Workers:** `-workers <N>` for parallel state exploration
3. **Fingerprint Mode:** Smaller state space, slight chance of collision
4. **Depth-First Search:** `-dfid` for finding violations faster (but not exhaustive)

## Expected Verification Time

On a typical modern system (Intel i7, 16GB RAM):
- **Basic verification (4 validators, 3 slots):** 1-2 minutes
- **Extended verification (5 validators, 3 slots):** 30-60 minutes
- **Large-scale verification (7+ validators):** Several hours

## Getting Help

### TLA+ Resources
- [TLA+ Website](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Community Forum](https://groups.google.com/g/tlaplus)

### Alpenglow Resources
- [Alpenglow Repository](https://github.com/Sovereign-Labs/alpenglow)
- [Verification Report](./VERIFICATION_REPORT.md)

## Citation

If you use this verification work, please cite:

```
Alpenglow Consensus Protocol Formal Verification
TLA+ Model and Proof
October 2025
```

## License

This formal verification work is provided as part of the Alpenglow project.
See the main repository LICENSE file for details.

---

**Last Updated:** October 6, 2025  
**Verification Status:** ✅ PASSED (All 12 safety invariants verified)  
**Model Checker:** TLC 2.19
