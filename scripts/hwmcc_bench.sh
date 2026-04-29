#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# HWMCC safety benchmark runner for tla2 aiger SAT engine.
# Usage: ./scripts/hwmcc_bench.sh [INNER_TIMEOUT_SECS] [OUTER_TIMEOUT_SECS] [BINARY]
#
# Defaults match the HWMCC Tier 3 sweep budget:
#   INNER_TIMEOUT = 300s  (passed to `tla2 aiger --timeout`)
#   OUTER_TIMEOUT = 330s  (wall-clock cap via `timeout`; 30s margin over inner)
#
# Rationale (see issue #4283 / designs/2026-04-19-hwmcc-tier3-path.md): at 100s
# inner / 120s outer, benchmarks like diffeq (rIC3 best 241s) are structurally
# unsolvable. 300s inner gives the z4-sat IC3 loop room to converge on the
# hardest Tier 3 benchmarks while staying well under HWMCC's 3600s-per-benchmark
# competition budget.
#
# Runs all 330 safety benchmarks and tallies sat/unsat/unknown/error.

INNER_TIMEOUT=${1:-300}
OUTER_TIMEOUT=${2:-330}
BINARY=${3:-/tmp/tla2-hwmcc/release/tla2}
BENCH_DIR="$HOME/hwmcc/benchmarks/bitlevel/safety"
RESULTS_CSV="/tmp/hwmcc_tla2_results.csv"

# Sanity check: outer must exceed inner so the process gets a chance to print
# its verdict before the outer SIGKILL.
if [ "$OUTER_TIMEOUT" -le "$INNER_TIMEOUT" ]; then
    echo "WARN: OUTER_TIMEOUT ($OUTER_TIMEOUT) <= INNER_TIMEOUT ($INNER_TIMEOUT); expected >=30s margin" >&2
fi

echo "benchmark,result,time" > "$RESULTS_CSV"

total=0
sat=0
unsat=0
unknown=0
errors=0
wrong=0

# Collect all .aig files
mapfile -t files < <(find "$BENCH_DIR" -name "*.aig" | sort)

echo "Running ${#files[@]} benchmarks with inner=${INNER_TIMEOUT}s outer=${OUTER_TIMEOUT}s timeout..."
echo "Binary: $BINARY"
echo ""

for f in "${files[@]}"; do
    total=$((total + 1))
    # Get relative path for display
    rel=${f#"$BENCH_DIR/"}

    # Run with timeout
    start=$(date +%s%N 2>/dev/null || python3 -c "import time; print(int(time.time()*1e9))")
    output=$(timeout "$OUTER_TIMEOUT" "$BINARY" aiger "$f" --engine sat --timeout "$INNER_TIMEOUT" 2>/dev/null)
    exit_code=$?
    end=$(date +%s%N 2>/dev/null || python3 -c "import time; print(int(time.time()*1e9))")

    elapsed=$(python3 -c "print(f'{($end - $start) / 1e9:.3f}')" 2>/dev/null || echo "?")

    # Parse result
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

    echo "$rel,$result_line,$elapsed" >> "$RESULTS_CSV"

    # Progress every 10 benchmarks
    if [ $((total % 10)) -eq 0 ]; then
        echo "[$total/${#files[@]}] sat=$sat unsat=$unsat unknown=$unknown error=$errors (last: $rel = $result_line ${elapsed}s)"
    fi
done

echo ""
echo "=== FINAL RESULTS ==="
echo "Total:   $total"
echo "SAT:     $sat"
echo "UNSAT:   $unsat"
echo "UNKNOWN: $unknown"
echo "ERROR:   $errors"
echo "SOLVED:  $((sat + unsat)) / $total"
echo ""
echo "Results saved to: $RESULTS_CSV"
