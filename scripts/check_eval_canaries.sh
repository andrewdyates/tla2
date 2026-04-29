#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# Eval/check canary state-count gate (#3037 Layer 1)
#
# Runs canary specs when tla-eval or tla-check source files change.
# Catches evaluator regressions (INSTANCE resolution, property classification,
# cache invalidation) before they land. These specs have regressed 3+ times
# each during optimization work.
#
# Usage:
#   scripts/check_eval_canaries.sh [--mode warn|enforce] [--changed-files FILE...]
#   scripts/check_eval_canaries.sh --mode enforce  # blocking gate
#   scripts/check_eval_canaries.sh                  # default: warn mode
#
# In pre-commit context, pass staged files via --changed-files.
# Without --changed-files, checks git diff --name-only HEAD.
#
# Environment:
#   TLA2_EVAL_CANARY_SKIP=1   Skip the gate entirely (emergency bypass)
#   TLA2_EVAL_CANARY_TIMEOUT  Per-spec timeout in seconds (default: 30)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CANARY_LIST="$REPO_ROOT/tests/tlc_comparison/eval_canary_specs.txt"
source "$SCRIPT_DIR/canary_gate_common.sh"

# Emergency bypass
if [[ "${TLA2_EVAL_CANARY_SKIP:-}" == "1" ]]; then
    exit 0
fi

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
            echo ""
            echo "Environment:"
            echo "  TLA2_EVAL_CANARY_SKIP=1   Skip entirely"
            echo "  TLA2_EVAL_CANARY_TIMEOUT  Per-spec timeout (default: 30s)"
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

if [[ ${#CHANGED_FILES[@]} -eq 0 ]]; then
    exit 0
fi

# Eval/check trigger patterns — broader than enumerate canary gate.
# Any change to the evaluator or model checker source triggers this gate.
TRIGGER_PATTERNS=(
    "crates/tla-eval/src/"
    "crates/tla-check/src/"
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
    # No eval/check source changes, skip silently
    exit 0
fi

echo "[eval-canary] Eval/check source files changed — running canary specs..."
TARGET_DIR="$(resolve_canary_target_dir "$REPO_ROOT")"
TLA2="$(resolve_canary_binary "$TARGET_DIR")"

# Build the current tree first so diagnose cannot reuse a stale binary (#1638).
echo "[eval-canary] Building current tla2 canary binary..."
build_exit=0
(
    cd "$REPO_ROOT"
    CARGO_TARGET_DIR="$TARGET_DIR" cargo build --profile release-canary --bin tla2
) || build_exit=$?

if [[ $build_exit -ne 0 ]]; then
    if [[ "$MODE" == "enforce" ]]; then
        echo "[eval-canary] FAIL: cargo build --profile release-canary --bin tla2 failed." >&2
        exit 1
    else
        echo "[eval-canary] WARNING: cargo build --profile release-canary --bin tla2 failed." >&2
        echo "[eval-canary] This is advisory — investigate before marking work complete." >&2
        exit 0
    fi
fi

if [[ ! -x "$TLA2" ]]; then
    if [[ "$MODE" == "enforce" ]]; then
        echo "[eval-canary] FAIL: release tla2 binary not found after build: $TLA2" >&2
        exit 1
    else
        echo "[eval-canary] WARNING: release tla2 binary not found after build: $TLA2" >&2
        echo "[eval-canary] This is advisory — investigate before marking work complete." >&2
        exit 0
    fi
fi

# Default timeout raised from 10s to 30s to accommodate MCBakery (~14s release).
# Small specs still finish in <2s; the higher ceiling only affects the medium spec.
TIMEOUT="${TLA2_EVAL_CANARY_TIMEOUT:-30}"

# Run tla2 diagnose with canary spec list
DIAG_ARGS=(
    "$TLA2" diagnose
    --spec-list "$CANARY_LIST"
    --timeout "$TIMEOUT"
    --fail-on-mismatch
    --fail-on-non-pass
)

diag_exit=0
"${DIAG_ARGS[@]}" 2>&1 || diag_exit=$?

if [[ $diag_exit -eq 0 ]]; then
    echo "[eval-canary] All canary specs pass."
    exit 0
fi

# Drift detected
if [[ "$MODE" == "enforce" ]]; then
    echo ""
    echo "[eval-canary] FAIL: Regression detected in eval/check canary specs."
    echo "[eval-canary] Fix the regression before committing eval/check changes."
    echo "[eval-canary] Bypass: TLA2_EVAL_CANARY_SKIP=1 git commit ..."
    exit 1
else
    echo ""
    echo "[eval-canary] WARNING: Regression detected in eval/check canary specs."
    echo "[eval-canary] This is advisory — investigate before marking work complete."
    exit 0
fi
