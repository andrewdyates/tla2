#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# MANDATORY VERIFICATION SCRIPT
# Run this BEFORE and AFTER any performance changes
# If ANY spec changes state count, the change is REJECTED
#
# Environment:
#   TLA2_KEEP_STATES=1          Keep TLC metadata in `spec_dir/states` (do not use a temp metadir).
#   TLA2_PRESERVE_STATES_DIR=1  When using a temp metadir, do not delete a pre-existing `spec_dir/states`.
#   TLA2_TLC_METADIR_ROOT=PATH  Root directory for temp TLC metadirs (default: `$REPO_ROOT/target/tlc_metadir`).
#   COMMUNITY_MODULES=PATH      Path to CommunityModules.jar (default: ~/tlaplus/CommunityModules.jar).

set -eo pipefail

echo "=== TLA2 Correctness Verification ==="
echo "Date: $(date)"
echo ""

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if command -v git >/dev/null 2>&1 && git -C "$SCRIPT_DIR" rev-parse --show-toplevel >/dev/null 2>&1; then
    REPO_ROOT="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)"
else
    REPO_ROOT="$(dirname "$SCRIPT_DIR")"
fi

# Run from repo root so relative paths in this script are stable.
cd "$REPO_ROOT"

if [ ! -f "$REPO_ROOT/Cargo.toml" ]; then
    echo "[ FAIL ] verify_correctness.sh: REPO_ROOT does not look like repo root: $REPO_ROOT" >&2
    exit 2
fi

if [ "${1:-}" = "--preflight" ]; then
    echo "[ OK ] SCRIPT_DIR=$SCRIPT_DIR"
    echo "[ OK ] REPO_ROOT=$REPO_ROOT"
    exit 0
fi

TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/target}"
if [[ "$TARGET_DIR" != /* ]]; then
    TARGET_DIR="$REPO_ROOT/$TARGET_DIR"
fi

VERIFY_CORRECTNESS_LIB_DIR="$SCRIPT_DIR/lib/verify_correctness"
source "$VERIFY_CORRECTNESS_LIB_DIR/common.sh"
source "$VERIFY_CORRECTNESS_LIB_DIR/trace_utils.sh"
source "$VERIFY_CORRECTNESS_LIB_DIR/runners.sh"
source "$VERIFY_CORRECTNESS_LIB_DIR/suites_core.sh"
source "$VERIFY_CORRECTNESS_LIB_DIR/suites_examples.sh"
source "$VERIFY_CORRECTNESS_LIB_DIR/python_fast_subset.sh"

# Build release binary
echo "Building release-canary binary..."

TLA2="$TARGET_DIR/release-canary/tla"
if [ ! -x "$TLA2" ]; then
    echo "[ FAIL ] release binary not found/executable: $TLA2" >&2
    exit 2
fi

PASS=0
FAIL=0
SKIP=0
EVAL=0   # Evaluator-only tests (1 state, no transitions)

echo "Running correctness checks..."
echo ""
run_verify_correctness_core_suite
run_verify_correctness_examples_suite
run_verify_correctness_python_fast_suite

echo ""
echo "=== Summary ==="
echo "PASS:  $PASS (checks passed)"
echo "EVAL:  $EVAL (evaluator-only tests - no state transitions)"
echo "FAIL:  $FAIL"
echo "SKIP:  $SKIP"
echo ""

PASSED=$((PASS + EVAL))
if [ $FAIL -gt 0 ]; then
    echo "VERIFICATION FAILED - DO NOT COMMIT"
    exit 1
elif [ $SKIP -gt 0 ]; then
    echo "VERIFICATION INCOMPLETE ($SKIP skipped) - DO NOT COMMIT"
    exit 1
else
    echo "VERIFICATION PASSED ($PASSED passed)"
    exit 0
fi
