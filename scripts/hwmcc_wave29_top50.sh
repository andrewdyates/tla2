#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# HWMCC Wave 29 top-50 sweep — runs the 50 smallest safety benchmarks with
# a 200s inner timeout (220s outer) sized for Sokoban-class SAT benchmarks
# that need deeper BMC unrolling than the default Wave 28 100s budget.
#
# Usage: ./scripts/hwmcc_wave29_top50.sh [BINARY] [RESULTS_CSV]
#
# Rationale (designs/2026-04-20-hwmcc-wave29-target.md):
#   - Wave 28 landed at 39/50 with a 100s inner timeout.
#   - Remaining unsolved includes Sokoban-class SAT instances whose shortest
#     counterexamples sit at depths that the default BMC ladder (step 25/50)
#     does not reach inside 100s.
#   - Wave 29 adds two SimpleSolver BMC engines (step 50 and step 100) and a
#     ternary_sim early-exit gate for SAT-likely inputs; both are cheap per
#     frame but need budget to expose a deeper counterexample. 200s/220s is
#     the sweep budget that matches the design doc's acceptance criteria.
#
# Budget: 50 benchmarks * 220s = ~183 minutes worst case (~3h).

set -u

INNER_TIMEOUT=200
OUTER_TIMEOUT=220
BINARY=${1:-/tmp/tla2-hwmcc/release/tla2}
BENCH_DIR="$HOME/hwmcc/benchmarks/bitlevel/safety"
RESULTS_CSV=${2:-/tmp/hwmcc_wave29_top50_results.csv}

if [ ! -x "$BINARY" ]; then
    echo "ERROR: binary not found or not executable: $BINARY" >&2
    echo "Build with: CARGO_TARGET_DIR=/tmp/tla2-hwmcc cargo build --release --bin tla2 --features z4" >&2
    exit 1
fi

if [ ! -d "$BENCH_DIR" ]; then
    echo "ERROR: benchmark dir not found: $BENCH_DIR" >&2
    exit 1
fi

echo "benchmark,result,time,size_bytes" > "$RESULTS_CSV"

# Select the 50 smallest .aig files by file size (the top-50 convention).
# Use a temp file + while-read to stay compatible with bash 3.2 (no mapfile).
TMP_LIST=$(mktemp)
trap 'rm -f "$TMP_LIST"' EXIT
find "$BENCH_DIR" -name "*.aig" -type f -exec stat -f '%z %N' {} \; 2>/dev/null \
    | sort -n | head -n 50 | awk '{$1=""; sub(/^ /, ""); print}' > "$TMP_LIST"

# Fall back to GNU stat if macOS stat produced nothing
if [ ! -s "$TMP_LIST" ]; then
    find "$BENCH_DIR" -name "*.aig" -type f -printf '%s %p\n' 2>/dev/null \
        | sort -n | head -n 50 | awk '{$1=""; sub(/^ /, ""); print}' > "$TMP_LIST"
fi

files=()
while IFS= read -r line; do
    files+=("$line")
done < "$TMP_LIST"

echo "Wave 29 top-50 sweep"
echo "Binary: $BINARY"
echo "Timeouts: inner=${INNER_TIMEOUT}s outer=${OUTER_TIMEOUT}s"
echo "Benchmarks: ${#files[@]}"
echo ""

total=0
sat=0
unsat=0
unknown=0
errors=0

for f in "${files[@]}"; do
    total=$((total + 1))
    rel=${f#"$BENCH_DIR/"}
    size=$(stat -f '%z' "$f" 2>/dev/null || stat -c '%s' "$f" 2>/dev/null || echo 0)

    start=$(python3 -c "import time; print(int(time.time()*1e9))")
    output=$(timeout "$OUTER_TIMEOUT" "$BINARY" aiger "$f" --engine sat --timeout "$INNER_TIMEOUT" 2>/dev/null)
    exit_code=$?
    end=$(python3 -c "import time; print(int(time.time()*1e9))")
    elapsed=$(python3 -c "print(f'{($end - $start) / 1e9:.3f}')" 2>/dev/null || echo "?")

    result_line=$(echo "$output" | head -1 | tr -d '[:space:]')

    if [ $exit_code -eq 124 ]; then
        result_line="timeout"
        unknown=$((unknown + 1))
    elif [ -z "$result_line" ]; then
        result_line="error"
        errors=$((errors + 1))
    elif [ "$result_line" = "sat" ]; then
        sat=$((sat + 1))
    elif [ "$result_line" = "unsat" ]; then
        unsat=$((unsat + 1))
    elif [ "$result_line" = "unknown" ]; then
        unknown=$((unknown + 1))
    else
        errors=$((errors + 1))
    fi

    echo "$rel,$result_line,$elapsed,$size" >> "$RESULTS_CSV"
    echo "[$total/${#files[@]}] $rel = $result_line (${elapsed}s, ${size}B)"
done

echo ""
echo "=== WAVE 29 TOP-50 RESULTS ==="
echo "Total:   $total"
echo "SAT:     $sat"
echo "UNSAT:   $unsat"
echo "UNKNOWN: $unknown"
echo "ERROR:   $errors"
echo "SOLVED:  $((sat + unsat)) / $total"
echo ""
echo "Results saved to: $RESULTS_CSV"
