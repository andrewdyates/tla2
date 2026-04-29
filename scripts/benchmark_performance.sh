#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# PERFORMANCE BENCHMARK SCRIPT
# Run this BEFORE and AFTER performance changes
# Records timing for comparison

set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/target}"
if [[ "$TARGET_DIR" != /* ]]; then
    TARGET_DIR="$REPO_ROOT/$TARGET_DIR"
fi

echo "=== TLA2 Performance Benchmark ==="
echo "Date: $(date)"
echo "Git: $(git rev-parse --short HEAD)"
echo ""

# Build release binary
echo "Building release binary..."

TLA2="$TARGET_DIR/release/tla"

run_benchmark() {
    local name="$1"
    local spec="$2"
    local config="${3:-}"

    if [ ! -f "$spec" ]; then
        echo "| $name | SKIP | - | - |"
        return
    fi

    # Run with timing
    start=$(python3 -c 'import time; print(time.time())')
    if [ -n "$config" ] && [ -f "$config" ]; then
        output=$($TLA2 check "$spec" --config "$config" --workers 1 2>&1) || true
    else
        output=$($TLA2 check "$spec" --workers 1 2>&1) || true
    fi
    end=$(python3 -c 'import time; print(time.time())')

    # Calculate time
    time=$(python3 -c "print(f'{$end - $start:.3f}')")

    # Extract state count
    states=$(echo "$output" | grep -oE "States found: [0-9,]+" | tr -d ',' | grep -oE "[0-9]+" || echo "0")

    # Calculate rate
    if [ "$states" != "0" ]; then
        rate=$(python3 -c "print(int($states / ($end - $start)))")
    else
        rate="N/A"
    fi

    echo "| $name | $states | ${time}s | $rate |"
}

echo "| Spec | States | Time | States/sec |"
echo "|------|--------|------|------------|"

run_benchmark "DieHard" "$HOME/tlaplus-examples/specifications/DieHard/DieHard.tla"
run_benchmark "DiningPhilosophers" "$HOME/tlaplus-examples/specifications/DiningPhilosophers/DiningPhilosophers.tla"
run_benchmark "bcastFolklore" "$HOME/tlaplus-examples/specifications/bcastFolklore/bcastFolklore.tla" "$HOME/tlaplus-examples/specifications/bcastFolklore/bcastFolklore.cfg"

# Issue #284 benchmark: Disruptor_SPMC - key spec for LET caching performance
# Baseline: TLA2=190s, TLC=1.2s (160x gap)
# Target after fix: <20s (10x improvement minimum)
run_benchmark "Disruptor_SPMC (#284)" "examples/test/disruptor/Disruptor_SPMC.tla" "examples/test/disruptor/Disruptor_SPMC.cfg"

echo ""
echo "Benchmark complete. Compare with previous runs to verify improvement."
