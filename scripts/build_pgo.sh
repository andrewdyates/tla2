#!/usr/bin/env bash
# Build TLA2 with Profile-Guided Optimization (PGO)
#
# PGO improves performance by ~11-15% by optimizing for actual workload patterns.
# This script:
# 1. Builds an instrumented binary to collect profile data
# 2. Runs benchmarks to collect profile data
# 3. Builds an optimized binary using the collected profile
#
# Requirements:
# - llvm-profdata (via Xcode Command Line Tools on macOS)
# - Z3 installed via homebrew

set -euo pipefail

PGO_DIR="/tmp/pgo-data"
Z3_PREFIX="${Z3_PREFIX:-/opt/homebrew/opt/z3}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# PGO builds do `cargo clean`, which is unsafe when running from an isolated
# looper session that shares `CARGO_TARGET_DIR`. Force a dedicated target dir.
PGO_CARGO_TARGET_DIR="${PGO_CARGO_TARGET_DIR:-$PROJECT_ROOT/target-pgo}"
export CARGO_TARGET_DIR="$PGO_CARGO_TARGET_DIR"

echo "=== Step 1: Clean previous profile data ==="
rm -rf "$PGO_DIR"
mkdir -p "$PGO_DIR"

echo "=== Step 2: Build with profile generation ==="

Z3_SYS_Z3_HEADER="$Z3_PREFIX/include/z3.h" \
LIBRARY_PATH="$Z3_PREFIX/lib" \
RUSTFLAGS="-Cprofile-generate=$PGO_DIR" \

echo "=== Step 3: Collect profile data ==="
TLA2="$CARGO_TARGET_DIR/release/tla2"

# Use MCBakery N=2 (smaller) for fast profile collection
echo "Running MCBakery N=2 for profiling..."
"$TLA2" check \
  "$PROJECT_ROOT/test_specs/MCBakery.tla" \
  --config "$PROJECT_ROOT/test_specs/MCBakery.cfg" \
  2>&1 || true

# Also run a diverse spec for broader coverage
if [ -f ~/tlaplus-examples/specifications/lamport_mutex/MCLamportMutex.tla ]; then
  echo "Running MCLamportMutex for additional coverage..."
  "$TLA2" check \
    ~/tlaplus-examples/specifications/lamport_mutex/MCLamportMutex.tla \
    --config ~/tlaplus-examples/specifications/lamport_mutex/MCLamportMutex.cfg \
    --workers 1 2>&1 || true
fi

# Profile data from both specs provides good coverage

echo "=== Step 4: Merge profile data ==="
# Find llvm-profdata (macOS uses xcrun, Linux uses direct path)
if command -v xcrun &> /dev/null; then
    LLVM_PROFDATA="xcrun llvm-profdata"
else
    LLVM_PROFDATA="llvm-profdata"
fi

$LLVM_PROFDATA merge -o "$PGO_DIR/merged.profdata" "$PGO_DIR"/*.profraw

echo "=== Step 5: Build with profile optimization ==="

Z3_SYS_Z3_HEADER="$Z3_PREFIX/include/z3.h" \
LIBRARY_PATH="$Z3_PREFIX/lib" \
RUSTFLAGS="-Cprofile-use=$PGO_DIR/merged.profdata" \

echo "=== Done! ==="
echo "PGO-optimized binary available at: $TLA2"
echo "Expected improvement: ~10-20% faster execution"
