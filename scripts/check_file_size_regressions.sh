#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# check_file_size_regressions.sh — detect production Rust files exceeding size thresholds
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Two modes:
#   1. Threshold scan: find all production .rs files over THRESHOLD lines (default 1000)
#   2. Baseline regression: compare known-split files against .file_size_baselines.json
#
# Usage:
#   scripts/check_file_size_regressions.sh [--threshold N] [--baseline] [--flags]
#
# --threshold N   Set line count threshold (default: 1000)
# --baseline      Also check .file_size_baselines.json for regrowth (2x baseline = warning)
# --flags         Write results to .flags/large_file_regressions (for looper startup)
# --quiet         Suppress informational output, only show violations

set -euo pipefail

THRESHOLD=1000
CHECK_BASELINE=false
WRITE_FLAGS=false
QUIET=false
EXIT_CODE=0
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --threshold) THRESHOLD="$2"; shift 2 ;;
        --threshold=*) THRESHOLD="${1#*=}"; shift ;;
        --baseline) CHECK_BASELINE=true; shift ;;
        --flags) WRITE_FLAGS=true; shift ;;
        --quiet) QUIET=true; shift ;;
        -h|--help)
            echo "Usage: $0 [--threshold N] [--baseline] [--flags] [--quiet]"
            exit 0
            ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

BASELINE_FILE="$REPO_ROOT/.file_size_baselines.json"
FLAGS_DIR="$REPO_ROOT/.flags"
FLAGS_OUTPUT="$FLAGS_DIR/large_file_regressions"

violations=()
baseline_regressions=()

# --- Threshold scan ---
while IFS= read -r file; do
    lines=$(wc -l < "$file")
    if [ "$lines" -gt "$THRESHOLD" ]; then
        rel="${file#$REPO_ROOT/}"
        violations+=("OVER ($lines > $THRESHOLD): $rel")
    fi
done < <(find "$REPO_ROOT/crates" -name '*.rs' \
    ! -name 'tests.rs' \
    ! -name '*_tests.rs' \
    ! -path '*/kani_harnesses/*' \
    ! -path '*/tests/*' \
    ! -path '*/test_*' \
    ! -path '*build_tests*' \
    -type f 2>/dev/null | sort)

if [ "$QUIET" = false ] && [ ${#violations[@]} -gt 0 ]; then
    echo "=== Files exceeding ${THRESHOLD}-line threshold ==="
    for v in "${violations[@]}"; do
        echo "  $v"
    done
    echo ""
fi

if [ ${#violations[@]} -gt 0 ]; then
    EXIT_CODE=1
fi

# --- Baseline regression check ---
if [ "$CHECK_BASELINE" = true ] && [ -f "$BASELINE_FILE" ]; then
    if ! command -v jq &>/dev/null; then
        echo "WARNING: jq not found, skipping baseline regression check" >&2
    else
        while IFS=$'\t' read -r filepath baseline_lines split_issue; do
            full_path="$REPO_ROOT/$filepath"
            if [ ! -f "$full_path" ]; then
                continue
            fi
            current_lines=$(wc -l < "$full_path")
            regrowth_limit=$((baseline_lines * 2))
            if [ "$current_lines" -gt "$regrowth_limit" ]; then
                baseline_regressions+=("REGROWTH ($current_lines > 2x$baseline_lines): $filepath (split: #$split_issue)")
                EXIT_CODE=1
            fi
        done < <(jq -r '.baselines | to_entries[] | [.key, .value.baseline, .value.split_issue] | @tsv' "$BASELINE_FILE")

        if [ "$QUIET" = false ] && [ ${#baseline_regressions[@]} -gt 0 ]; then
            echo "=== Baseline regrowth regressions (>2x post-split size) ==="
            for r in "${baseline_regressions[@]}"; do
                echo "  $r"
            done
            echo ""
        fi
    fi
fi

# --- Write flags output ---
if [ "$WRITE_FLAGS" = true ]; then
    mkdir -p "$FLAGS_DIR"
    {
        date -u +"%Y-%m-%dT%H:%M:%SZ"
        if [ ${#violations[@]} -gt 0 ]; then
            echo "Threshold violations (>${THRESHOLD} lines):"
            for v in "${violations[@]}"; do
                echo "  $v"
            done
        fi
        if [ ${#baseline_regressions[@]} -gt 0 ]; then
            echo "Baseline regressions (>2x post-split):"
            for r in "${baseline_regressions[@]}"; do
                echo "  $r"
            done
        fi
        if [ ${#violations[@]} -eq 0 ] && [ ${#baseline_regressions[@]} -eq 0 ]; then
            echo "No regressions detected."
        fi
    } > "$FLAGS_OUTPUT"
fi

# --- Summary ---
if [ "$QUIET" = false ]; then
    total=$((${#violations[@]} + ${#baseline_regressions[@]}))
    if [ "$total" -eq 0 ]; then
        echo "No file size regressions detected (threshold: $THRESHOLD)."
    else
        echo "Found $total file size issue(s)."
    fi
fi

exit $EXIT_CODE
