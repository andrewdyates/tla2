#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# API consumer compatibility gate (Part of #1325).
# Runs `cargo check` on canary crates that import stable public API paths.
# Compile failure = public API contract was broken.
#
# Usage: ./scripts/check_api_canary_gate.sh [--verbose]
set -euo pipefail

VERBOSE="${1:-}"
PASS=0
FAIL=0
FAILURES=""

CANARY_DIR="tests/api_canaries"

# Canary crates — one per API surface contract.
CANARIES=(
    core_translate_canary
    check_fingerprint_canary
    eval_value_canary
)

echo "=== API Consumer Compatibility Gate (#1325) ==="
echo "Canary directory: $CANARY_DIR"
echo "Canaries: ${CANARIES[*]}"
echo ""

for canary in "${CANARIES[@]}"; do
    canary_dir="$CANARY_DIR/$canary"
    if [ ! -d "$canary_dir" ]; then
        echo "FAIL: $canary — canary directory not found: $canary_dir"
        FAIL=$((FAIL+1))
        FAILURES="${FAILURES}  - $canary: directory not found\n"
        continue
    fi

    echo -n "Checking $canary ... "
    log=$(mktemp -t "api_canary_${canary}.XXXXXX")
    set +e
    cargo check -p "$canary" >"$log" 2>&1
    status=$?
    set -e

    if [ "$status" -eq 0 ]; then
        echo "PASS"
        PASS=$((PASS+1))
    else
        echo "FAIL (exit $status)"
        FAIL=$((FAIL+1))
        # Extract the first error line for quick triage.
        first_error=$(grep -m1 "^error" "$log" || echo "(no error line found)")
        FAILURES="${FAILURES}  - $canary: $first_error\n"
        if [ "$VERBOSE" = "--verbose" ]; then
            echo "--- $canary build output ---"
            cat "$log"
            echo "--- end $canary ---"
        fi
    fi
    rm -f "$log"
done

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
if [ "$FAIL" -eq 0 ]; then
    echo "ALL API CANARY GATES PASSED"
else
    echo "API CANARY GATES FAILING:"
    echo -e "$FAILURES"
fi
exit "$FAIL"
