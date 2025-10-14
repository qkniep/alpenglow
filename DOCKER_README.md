# Quick Start: Docker Verification

This directory contains a Docker environment for reproducible formal verification of Alpenglow.

## One-Command Verification

```bash
# Build the Docker image
docker build -t alpenglow-verification .

# Run interactive verification
docker run -it alpenglow-verification

# 🎯 INSIDE THE CONTAINER, TYPE THIS COMMAND:
verify

# Then select an option (1-10) from the menu
# Example: Type "1" then press Enter to run Core Safety verification
```

## Step-by-Step First Run

1. **Start the container:**
   ```bash
   docker run -it alpenglow-verification
   ```

2. **You'll see a welcome message** showing available verifications

3. **Type `verify` and press Enter:**
   ```bash
   root@abc123:/workspace/formal-verification# verify
   ```

4. **Select a verification** (e.g., type `1` for Core Safety):
   ```
   Enter your choice (1-10): 1
   ```

5. **Watch the verification run** - Progress updates every second

6. **See results** - "NO ERRORS FOUND" or error details

## What's Included

- **TLA+ Tools (TLC)** - Model checker for exhaustive state space exploration
- **TLAPS** - Theorem prover for deductive proofs (optional installation)
- **Python 3** - Verification automation scripts
- **Java 17** - Required for TLC execution
- **All TLA+ specifications** - Complete Alpenglow formal models

## Verification Commands

### Inside Docker Container:

**IMPORTANT:** The container shows a menu on startup, but you must type `verify` to start!

```bash
# ✅ STEP 1: Run this command first
verify

# ✅ STEP 2: Select option from menu (1-10)
# Example: Type "1" for Core Safety, then press Enter

# Alternative: Run specific verification directly
cd /workspace/formal-verification
python3 verify.py  # Then select option 1-10

# Run TLC model checker directly (advanced)
tlc -config MC.cfg Alpenglow.tla

# Check available files
ls -lh *.tla *.cfg
```

### Quick Test (Outside Container)

```bash
# Run verification non-interactively from host machine
docker run alpenglow-verification bash -c "echo '6' | verify"
# This will run option 6 (Rotor - fastest, ~10 seconds)
```

## Verification Options

| Option | Description | States | Time |
|--------|-------------|--------|------|
| 1 | Core Safety Properties | 6.2M | ~5 min |
| 2 | Byzantine Fault Tolerance | 10M+ | ~15 min |
| 3 | Liveness Properties | 3.2M | ~8 min |
| 4 | Network Partitions | 2.1M | ~5 min |
| 5 | Complete Verification | All | ~45 min |
| 6 | Rotor Propagation | 50K | ~1 min |

## Expected Output

All verifications should complete with:
```
✓ Model checking completed successfully
✓ No errors found
✓ All invariants passed
```

## Troubleshooting

### ❌ "bash: 1: command not found" or "bash: 2: command not found"

**Problem:** You typed a number at the bash prompt without running `verify` first.

**Solution:**
```bash
# ✅ Type this command first:
verify

# THEN you'll see the interactive menu where you can select 1-10
```

### Out of Memory
```bash
# Increase Java heap size
export JAVA_OPTS="-Xmx8g -Xms4g"
tlc MC.tla
```

### Verification Too Slow
```bash
# Run smaller verification first
verify  # Select option 6 (fastest)
```

## TLAPS Installation (Optional)

For deductive theorem proving:

```bash
# Inside container
/opt/install-tlaps.sh

# Follow interactive prompts
# Then verify TLAPS proofs:
tlapm SafetyProofs_TLAPS.tla
```

## Advanced Usage

### Mount Local Files

```bash
# Run with local files mounted
docker run -it -v $(pwd)/formal-verification:/workspace/formal-verification alpenglow-verification
```

### Run Specific Verification

```bash
# Run only Byzantine fault tolerance test
docker run -it alpenglow-verification bash -c "echo '2' | verify"
```

### Export Results

```bash
# Copy verification results out of container
docker cp <container-id>:/workspace/formal-verification/verification_output.txt ./results.txt
```

## System Requirements

- **Docker**: 20.10+
- **Memory**: 8GB minimum, 16GB recommended
- **Disk**: 2GB for image + verification artifacts
- **CPU**: Multi-core recommended (verification is CPU-intensive)

## Reproducibility

This Docker environment guarantees:
- ✅ Identical tool versions
- ✅ Consistent Java/Python environment
- ✅ Same TLA+ specifications
- ✅ Reproducible verification results

All verifications should produce identical state counts and pass/fail results across different machines.

## Quick Test

```bash
# Quick 1-minute test to verify environment
docker run alpenglow-verification bash -c "verify --test"
```

Expected output:
```
✓ TLC installed: OK
✓ Python installed: OK
✓ TLA+ specifications: OK
✓ Environment ready for verification
```
