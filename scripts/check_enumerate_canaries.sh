#!/usr/bin/env bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# Enumerate canary state-count gate (#1570)
#
# Runs a small set of spec comparisons when enumerate-sensitive files change.
# Detects state-count or error-type drift before regressions land.
#
# Usage:
#   scripts/check_enumerate_canaries.sh [--mode warn|enforce] [--changed-files FILE...]
#   scripts/check_enumerate_canaries.sh --mode enforce  # blocking gate
#   scripts/check_enumerate_canaries.sh                  # default: warn mode
#
# Builds tla2 from current source before running diagnose (#1638).
# In pre-commit context, pass staged files via --changed-files.
# Without --changed-files, checks git diff --name-only HEAD.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CANARY_LIST="$REPO_ROOT/tests/tlc_comparison/enumerate_canary_specs.txt"
source "$SCRIPT_DIR/canary_gate_common.sh"

MODE="warn"
CHANGED_FILES=()

# Parse arguments
while [[ $# -gt 0 ]]; do
    case "$1" in
        --mode)
            MODE="$2"
            shift 2
            ;;
        --changed-files)
            shift
            while [[ $# -gt 0 ]] && [[ "$1" != --* ]]; do
                CHANGED_FILES+=("$1")
                shift
            done
            ;;
        -h|--help)
            echo "Usage: $0 [--mode warn|enforce] [--changed-files FILE...]"
            echo ""
            echo "Modes:"
            echo "  warn    (default) Print warning on drift, exit 0"
            echo "  enforce           Fail hard on drift, exit 1"
            exit 0
            ;;
        *)
            echo "Unknown argument: $1" >&2
            exit 1
            ;;
    esac
done

# Validate mode
if [[ "$MODE" != "warn" && "$MODE" != "enforce" ]]; then
    echo "Error: --mode must be 'warn' or 'enforce'" >&2
    exit 1
fi

# Validate prerequisites
if [[ ! -f "$CANARY_LIST" ]]; then
    echo "Error: canary spec list not found: $CANARY_LIST" >&2
    exit 1
fi

# Get changed files if not provided
if [[ ${#CHANGED_FILES[@]} -eq 0 ]]; then
    while IFS= read -r f; do
        CHANGED_FILES+=("$f")
    done < <(git diff --name-only HEAD 2>/dev/null || true)
fi

# Enumerate-sensitive trigger globs
TRIGGER_PATTERNS=(
    "crates/tla-check/src/enumerate/"
    "crates/tla-check/src/eval/"
    "crates/tla-check/src/compiled_guard/"
    "crates/tla-check/src/check/model_checker/setup.rs"
)

# Check if any changed file matches a trigger pattern
triggered=false
for f in "${CHANGED_FILES[@]}"; do
    for pattern in "${TRIGGER_PATTERNS[@]}"; do
        if [[ "$f" == $pattern* ]]; then
            triggered=true
            break 2
        fi
    done
done

if [[ "$triggered" != "true" ]]; then
    # No enumerate-sensitive changes, skip silently
    exit 0
fi

echo "[canary-gate] Enumerate-sensitive files changed — running canary specs..."
TARGET_DIR="$(resolve_canary_target_dir "$REPO_ROOT")"
TLA2="$(resolve_canary_binary "$TARGET_DIR")"

# Build the current tree first so diagnose cannot reuse a stale binary (#1638).
echo "[canary-gate] Building current tla2 canary binary..."
build_exit=0
(
    cd "$REPO_ROOT"
    CARGO_TARGET_DIR="$TARGET_DIR" cargo build --profile release-canary --bin tla2
) || build_exit=$?

if [[ $build_exit -ne 0 ]]; then
    if [[ "$MODE" == "enforce" ]]; then
        echo "[canary-gate] FAIL: cargo build --profile release-canary --bin tla2 failed." >&2
        exit 1
    else
        echo "[canary-gate] WARNING: cargo build --profile release-canary --bin tla2 failed." >&2
        echo "[canary-gate] This is advisory — investigate before marking work complete." >&2
        exit 0
    fi
fi

if [[ ! -x "$TLA2" ]]; then
    if [[ "$MODE" == "enforce" ]]; then
        echo "[canary-gate] FAIL: release tla2 binary not found after build: $TLA2" >&2
        exit 1
    else
        echo "[canary-gate] WARNING: release tla2 binary not found after build: $TLA2" >&2
        echo "[canary-gate] This is advisory — investigate before marking work complete." >&2
        exit 0
    fi
fi

# Run tla2 diagnose with canary spec list
DIAG_ARGS=(
    "$TLA2" diagnose
    --spec-list "$CANARY_LIST"
    --fail-on-mismatch
    --fail-on-non-pass
)

diag_exit=0
"${DIAG_ARGS[@]}" 2>&1 || diag_exit=$?

if [[ $diag_exit -eq 0 ]]; then
    echo "[canary-gate] All canary specs pass."
    exit 0
fi

# Drift detected
if [[ "$MODE" == "enforce" ]]; then
    echo ""
    echo "[canary-gate] FAIL: State-count drift detected in canary specs."
    echo "[canary-gate] Fix the regression before committing enumerate/ changes."
    exit 1
else
    echo ""
    echo "[canary-gate] WARNING: State-count drift detected in canary specs."
    echo "[canary-gate] This is advisory — investigate before marking work complete."
    exit 0
fi
