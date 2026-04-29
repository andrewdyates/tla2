#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# bisect_regression.sh — Automated bisection for #2834 spec regressions
#
# Usage:
#   git bisect start
#   git bisect bad 6f2082b8     # current: failing (37 states, invariant error)
#   git bisect good 215137ebd   # baseline: passing (77 states, exact match)
#   git bisect run scripts/bisect_regression.sh
#
# This script builds tla2 and runs MCVoting. Exit code 0 = good (77 states),
# exit code 1 = bad (wrong count or error), exit code 125 = skip (build failure).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Part of #2834

set -euo pipefail

SPEC_DIR="$HOME/tlaplus-examples/specifications/Paxos"
SPEC="$SPEC_DIR/MCVoting.tla"
CFG="$SPEC_DIR/MCVoting.cfg"
EXPECTED_STATES=77

# Build — skip commit if it doesn't compile
if ! cargo build --profile release-canary --bin tla2 2>/dev/null; then
    echo "BISECT: build failed, skipping"
    exit 125
fi

# Run MCVoting — capture output
OUTPUT=$(timeout 120 target/release-canary/tla2 check "$SPEC" --config "$CFG" 2>&1) || true

# Extract state count from output
# Look for patterns like "N distinct states found" or "states: N"
STATE_COUNT=$(echo "$OUTPUT" | grep -oP '(\d+)\s+distinct states' | grep -oP '^\d+' || true)
if [ -z "$STATE_COUNT" ]; then
    STATE_COUNT=$(echo "$OUTPUT" | grep -oP 'states:\s*(\d+)' | grep -oP '\d+' || true)
fi

# Check for error indicators
HAS_ERROR=$(echo "$OUTPUT" | grep -ci "error\|violation\|invariant.*violated" || true)

if [ -z "$STATE_COUNT" ]; then
    echo "BISECT: could not extract state count"
    echo "OUTPUT: $OUTPUT" | tail -20
    # If we can't extract states, check if it completed without error
    if [ "$HAS_ERROR" -gt 0 ]; then
        echo "BISECT: BAD — has errors"
        exit 1
    fi
    echo "BISECT: SKIP — indeterminate"
    exit 125
fi

echo "BISECT: MCVoting states=$STATE_COUNT (expected=$EXPECTED_STATES)"

if [ "$STATE_COUNT" -eq "$EXPECTED_STATES" ] && [ "$HAS_ERROR" -eq 0 ]; then
    echo "BISECT: GOOD"
    exit 0
else
    echo "BISECT: BAD (states=$STATE_COUNT, errors=$HAS_ERROR)"
    exit 1
fi
