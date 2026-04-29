#!/bin/bash
# Copyright 2026 Dropbox
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# MCC (Model Checking Contest) sweep — runs the 13 MCC examinations against
# a directory of Petri-net model directories and tallies results per-model.
#
# Each model directory must contain `model.pnml` and, for property-based
# examinations, the matching property XML files (e.g. `CTLFireability.xml`).
# See tests/mcc_benchmarks/*/ for the fixture layout.
#
# Modeled on scripts/hwmcc_wave29_top50.sh (Part of #4211 / #4212).
#
# Usage:
#   ./scripts/mcc_sweep.sh [BENCH_DIR] [RESULTS_CSV]
#
# Environment:
#   MCC_BINARY    — path to pnml-tools (default: /tmp/tla2-mcc-agent/agent/pnml-tools)
#   MCC_TIMEOUT   — per-examination inner timeout seconds (default: 60)
#   MCC_OUTER     — outer wall-clock cap seconds (default: 75)
#   MCC_EXAMS     — space-separated examination list (default: the 7 matching
#                   the mutex fixture — OneSafe + GlobalProperties + StateSpace +
#                   ReachabilityFireability + CTLFireability).
#
# This is the in-repo sanity sweep. For the full 1800+ model × 13-exam measurement
# run, use ~/win-all-software-proof-competitions/results/mcc-full-measurement/.

set -u

BENCH_DIR="${1:-tests/mcc_benchmarks}"
RESULTS_CSV="${2:-/tmp/mcc_sweep_results.csv}"
BINARY="${MCC_BINARY:-/tmp/tla2-mcc-agent/agent/pnml-tools}"
TIMEOUT="${MCC_TIMEOUT:-60}"
OUTER="${MCC_OUTER:-75}"
EXAMS="${MCC_EXAMS:-ReachabilityDeadlock OneSafe QuasiLiveness StableMarking Liveness StateSpace ReachabilityFireability CTLFireability}"

if [ ! -x "$BINARY" ]; then
    echo "ERROR: binary not found or not executable: $BINARY" >&2
    echo "Build with: CARGO_TARGET_DIR=/tmp/tla2-mcc-agent cargo build --profile agent --bin pnml-tools" >&2
    exit 1
fi

if [ ! -d "$BENCH_DIR" ]; then
    echo "ERROR: benchmark dir not found: $BENCH_DIR" >&2
    exit 1
fi

# Discover model directories: any subdir containing model.pnml.
TMP_LIST=$(mktemp)
trap 'rm -f "$TMP_LIST"' EXIT
find "$BENCH_DIR" -type f -name model.pnml -print 2>/dev/null \
    | sed 's|/model\.pnml$||' \
    | sort > "$TMP_LIST"

models=()
while IFS= read -r line; do
    [ -n "$line" ] && models+=("$line")
done < "$TMP_LIST"

if [ "${#models[@]}" -eq 0 ]; then
    echo "ERROR: no model.pnml found under $BENCH_DIR" >&2
    exit 1
fi

echo "MCC sweep"
echo "Binary:      $BINARY"
echo "Bench dir:   $BENCH_DIR"
echo "Examinations: $EXAMS"
echo "Timeouts:    inner=${TIMEOUT}s outer=${OUTER}s"
echo "Models:      ${#models[@]}"
echo ""

echo "model,examination,result,time_sec,exit_code" > "$RESULTS_CSV"

total=0
formula=0
cannot=0
timedout=0
errors=0

for model_dir in "${models[@]}"; do
    model_name=$(basename "$model_dir")
    for exam in $EXAMS; do
        total=$((total + 1))

        # Skip property exams when the XML is absent — avoids noisy CANNOT_COMPUTE lines.
        case "$exam" in
            ReachabilityCardinality|ReachabilityFireability|CTLCardinality|CTLFireability|LTLCardinality|LTLFireability|UpperBounds)
                if [ ! -f "$model_dir/$exam.xml" ]; then
                    echo "[$total] $model_name/$exam = SKIP (no $exam.xml)"
                    echo "$model_name,$exam,skip,0,0" >> "$RESULTS_CSV"
                    continue
                fi
                ;;
        esac

        start=$(date +%s)
        output=$(timeout "$OUTER" "$BINARY" --examination "$exam" --timeout "$TIMEOUT" "$model_dir" 2>/dev/null)
        exit_code=$?
        end=$(date +%s)
        elapsed=$((end - start))

        # Determine summary verdict: number of FORMULA lines, CANNOT_COMPUTE, timeout, or error.
        formula_lines=$(printf '%s\n' "$output" | grep -c '^FORMULA ' || true)
        cannot_lines=$(printf '%s\n' "$output" | grep -c 'CANNOT_COMPUTE' || true)
        if [ "$exit_code" -eq 124 ]; then
            verdict="timeout"
            timedout=$((timedout + 1))
        elif [ "$exit_code" -ne 0 ]; then
            verdict="error(exit=$exit_code)"
            errors=$((errors + 1))
        elif [ "$formula_lines" -gt 0 ] && [ "$cannot_lines" -eq 0 ]; then
            verdict="ok(${formula_lines} formula)"
            formula=$((formula + 1))
        elif [ "$cannot_lines" -gt 0 ]; then
            verdict="cannot_compute"
            cannot=$((cannot + 1))
        elif [ "$exam" = "StateSpace" ] && printf '%s' "$output" | grep -q '^STATE_SPACE '; then
            verdict="ok(state_space)"
            formula=$((formula + 1))
        else
            verdict="error(no_output)"
            errors=$((errors + 1))
        fi

        echo "$model_name,$exam,$verdict,$elapsed,$exit_code" >> "$RESULTS_CSV"
        echo "[$total] $model_name/$exam = $verdict (${elapsed}s)"
    done
done

echo ""
echo "=== MCC SWEEP RESULTS ==="
echo "Total runs:       $total"
echo "OK (FORMULA):     $formula"
echo "CANNOT_COMPUTE:   $cannot"
echo "Timeout:          $timedout"
echo "Error:            $errors"
echo ""
echo "Results saved to: $RESULTS_CSV"
