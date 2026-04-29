#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# TLC Comparison Test Suite
# Runs both TLC and TLA2 on specs, compares results for semantic equivalence
#
# Usage:
#   ./scripts/compare_with_tlc.sh                    # Run all comparison tests
#   ./scripts/compare_with_tlc.sh spec.tla spec.cfg  # Compare single spec
#
# Environment:
#   TLA2_KEEP_STATES=1          Keep TLC metadata in `spec_dir/states` (do not use a temp metadir).
#   TLA2_PRESERVE_STATES_DIR=1  When using a temp metadir, do not delete a pre-existing `spec_dir/states`.
#   TLA2_TLC_METADIR_ROOT=PATH  Root directory for temp TLC metadirs (default: `$REPO_ROOT/target/tlc_metadir`).

set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/target}"
if [[ "$TARGET_DIR" != /* ]]; then
    TARGET_DIR="$REPO_ROOT/$TARGET_DIR"
fi
TLA2="$TARGET_DIR/release-canary/tla"
TLA2TOOLS_JAR="${TLA2TOOLS_JAR:-${TLC_JAR:-$HOME/tlaplus/tla2tools.jar}}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

PASS=0
FAIL=0
SKIP=0

# Build TLA2 if needed
if [ ! -f "$TLA2" ]; then
    echo "Building TLA2..."
fi

# Check TLC is available (z4-tla-bridge-compatible discovery order)
if [ -n "${TLC_BIN:-}" ]; then
    if [ ! -x "$TLC_BIN" ]; then
        echo "ERROR: TLC_BIN not executable: $TLC_BIN" >&2
        exit 1
    fi
elif command -v tlc >/dev/null 2>&1; then
    : # ok
else
    if [ ! -f "$TLA2TOOLS_JAR" ]; then
        echo "ERROR: TLC jar not found at $TLA2TOOLS_JAR" >&2
        echo "Fix: set TLA2TOOLS_JAR (or compat TLC_JAR) to tla2tools.jar, or provide TLC_BIN, or install tlc on PATH" >&2
        exit 1
    fi
fi

# Parse TLC output to extract state count
parse_tlc_states() {
    local output="$1"
    # Match "N distinct states found" and extract N
    local match=$(echo "$output" | grep -oE '[0-9,]+ distinct states found' | tail -1 | tr -d ',')
    if [ -n "$match" ]; then
        echo "$match" | grep -oE '^[0-9]+'
    else
        echo "0"
    fi
}

# Parse TLA2 JSON output to extract summary fields.
parse_tla2_json_summary() {
    local json_path="$1"
    python3 "$SCRIPT_DIR/tla2_json_summary.py" "$json_path"
}

# Check if TLC found an error
tlc_has_error() {
    local output="$1"
    echo "$output" | grep -qE 'Error:|Invariant .* is violated|Deadlock reached'
}

# Check if TLA2 found an error
tla2_has_error() {
    local status="$1"
    case "$status" in
        ok | limit_reached)
            return 1
            ;;
        *)
            return 0
            ;;
    esac
}

# Compare single spec
compare_spec() {
    local name="$1"
    local spec="$2"
    local config="$3"

    if [ ! -f "$spec" ]; then
        echo -e "${YELLOW}[ SKIP ]${NC} $name - spec not found: $spec"
        SKIP=$((SKIP + 1))
        return
    fi

    if [ -n "$config" ] && [ ! -f "$config" ]; then
        echo -e "${YELLOW}[ SKIP ]${NC} $name - config not found: $config"
        SKIP=$((SKIP + 1))
        return
    fi

    local spec_dir=$(dirname "$spec")
    local states_dir="$spec_dir/states"

    # Run TLC
    local tlc_metadir=""
    local -a tlc_cmd=()
    if [ -n "${TLC_BIN:-}" ]; then
        tlc_cmd=("$TLC_BIN")
    elif command -v tlc >/dev/null 2>&1; then
        tlc_cmd=(tlc)
    else
        tlc_cmd=(java -XX:+UseParallelGC -Xmx4g -cp "$TLA2TOOLS_JAR" tlc2.TLC)
    fi
    if [ "${TLA2_KEEP_STATES:-0}" != "1" ]; then
        local tlc_metadir_root="${TLA2_TLC_METADIR_ROOT:-$REPO_ROOT/target/tlc_metadir}"
        mkdir -p "$tlc_metadir_root"
        tlc_metadir="$(mktemp -d "$tlc_metadir_root/tlc_XXXXXX")"
        tlc_cmd+=( -metadir "$tlc_metadir" )
    fi
    if [ -n "$config" ]; then
        local cfg_arg="$config"
        if [ "$(dirname "$config")" = "$spec_dir" ]; then
            cfg_arg="$(basename "$config")"
        fi
        tlc_cmd+=( -config "$cfg_arg" )
    fi
    tlc_cmd+=( -workers 1 "$(basename "$spec")" )

    local tlc_output
    tlc_output=$(cd "$spec_dir" && "${tlc_cmd[@]}" 2>&1) || true
    if [ -n "$tlc_metadir" ]; then
        rm -rf "$tlc_metadir"
    fi
    if [ "${TLA2_KEEP_STATES:-0}" != "1" ] && [ "${TLA2_PRESERVE_STATES_DIR:-0}" != "1" ] && [ -d "$states_dir" ]; then
        # Safety: never delete `/states` if someone points a spec at `/`.
        if [ -z "${spec_dir:-}" ] || [ "$spec_dir" = "/" ] || [ "$states_dir" = "/states" ] || [ "$(basename -- "$states_dir")" != "states" ]; then
            echo "[ WARN ] refusing to delete suspicious states dir: spec_dir=$spec_dir states_dir=$states_dir" >&2
        else
            rm -rf "$states_dir"
        fi
    fi
    local tlc_states=$(parse_tlc_states "$tlc_output")

    # Run TLA2 (JSON on stdout; everything else on stderr)
    local -a tla2_cmd=("$TLA2" check --workers 1 --output json)
    if [ -n "$config" ]; then
        tla2_cmd+=( --config "$config" )
    fi
    tla2_cmd+=( "$spec" )

    local tla2_json_file
    tla2_json_file="$(mktemp)"
    local tla2_stderr_file
    tla2_stderr_file="$(mktemp)"

    local tla2_rc=0
    set +e
    "${tla2_cmd[@]}" >"$tla2_json_file" 2>"$tla2_stderr_file"
    tla2_rc=$?
    set -e

    local tla2_summary
    tla2_summary="$(parse_tla2_json_summary "$tla2_json_file")"

    local tla2_status=""
    local tla2_error_type=""
    local tla2_error_code=""
    local tla2_violated_type=""
    local tla2_violated_name=""
    local tla2_states="0"
    local tla2_states_distinct="0"
    local tla2_has_counterexample="0"
    IFS=$'\t' read -r \
        tla2_status \
        tla2_error_type \
        tla2_error_code \
        tla2_violated_type \
        tla2_violated_name \
        tla2_states \
        tla2_states_distinct \
        tla2_has_counterexample <<<"$tla2_summary"

    # Compare results
    local result="PASS"
    local details=""

    # Check state count match
    if [ "$tlc_states" != "$tla2_states" ]; then
        result="FAIL"
        details="states: TLC=$tlc_states, TLA2=$tla2_states"
    fi

    # Check error detection consistency
    local tlc_error=0
    local tla2_error=0
    tlc_has_error "$tlc_output" && tlc_error=1
    tla2_has_error "$tla2_status" && tla2_error=1

    if [ "$tlc_error" != "$tla2_error" ]; then
        result="FAIL"
        details="$details error_detection: TLC=$tlc_error, TLA2=$tla2_error"
        if [ "$tla2_error" = "1" ]; then
            details="$details tla2_error=$tla2_error_type:$tla2_error_code:$tla2_violated_type:$tla2_violated_name"
        fi
    fi

    # Output result
    if [ "$result" = "PASS" ]; then
        echo -e "${GREEN}[ PASS ]${NC} $name: $tla2_states states"
        PASS=$((PASS + 1))
    else
        echo -e "${RED}[ FAIL ]${NC} $name: $details"
        FAIL=$((FAIL + 1))

        # Show detailed comparison on failure
        echo "  TLC output (last 10 lines):"
        echo "$tlc_output" | tail -10 | sed 's/^/    /'
        echo "  TLA2 stderr (last 10 lines):"
        tail -10 "$tla2_stderr_file" | sed 's/^/    /'
        echo "  TLA2 JSON summary:"
        echo "    status=$tla2_status states=$tla2_states distinct=$tla2_states_distinct error=$tla2_error_type:$tla2_error_code violated=$tla2_violated_type:$tla2_violated_name counterexample=$tla2_has_counterexample rc=$tla2_rc"
    fi

    rm -f "$tla2_json_file" "$tla2_stderr_file"
}

# Main test suite
run_test_suite() {
    echo "=== TLC vs TLA2 Comparison Test Suite ==="
    echo "Date: $(date)"
    echo ""

    local examples_dir="$HOME/tlaplus-examples/specifications"
    local test_specs="$REPO_ROOT/test_specs"

    # Core algorithm specs
    echo "--- Core Algorithms ---"
    compare_spec "DieHard" "$examples_dir/DieHard/DieHard.tla" "$examples_dir/DieHard/DieHard.cfg"
    compare_spec "TwoPhase" "$examples_dir/transaction_commit/TwoPhase.tla" "$examples_dir/transaction_commit/TwoPhase.cfg"
    compare_spec "TCommit" "$examples_dir/transaction_commit/TCommit.tla" "$examples_dir/transaction_commit/TCommit.cfg"

    # Mutual exclusion
    echo ""
    echo "--- Mutual Exclusion ---"
    compare_spec "Peterson" "$examples_dir/locks_auxiliary_vars/Peterson.tla" "$examples_dir/locks_auxiliary_vars/Peterson.cfg"
    compare_spec "Lock" "$examples_dir/locks_auxiliary_vars/Lock.tla" "$examples_dir/locks_auxiliary_vars/Lock.cfg"
    compare_spec "MCBakery" "$examples_dir/Bakery-Boulangerie/MCBakery.tla" "$test_specs/MCBakery.cfg"

    # Distributed systems
    echo ""
    echo "--- Distributed Systems ---"
    compare_spec "TokenRing" "$examples_dir/ewd426/TokenRing.tla" "$examples_dir/ewd426/TokenRing.cfg"
    compare_spec "EWD840" "$examples_dir/ewd840/EWD840.tla" "$examples_dir/ewd840/EWD840.cfg"
    compare_spec "MCChangRoberts" "$examples_dir/chang_roberts/MCChangRoberts.tla" "$examples_dir/chang_roberts/MCChangRoberts.cfg"
    compare_spec "Huang" "$examples_dir/Huang/Huang.tla" "$examples_dir/Huang/Huang.cfg"

    # Resource allocation
    echo ""
    echo "--- Resource Allocation ---"
    compare_spec "SimpleAllocator" "$examples_dir/allocator/SimpleAllocator.tla" "$examples_dir/allocator/SimpleAllocator.cfg"
    compare_spec "SchedulingAllocator" "$examples_dir/allocator/SchedulingAllocator.tla" "$examples_dir/allocator/SchedulingAllocator.cfg"

    # Classic problems
    echo ""
    echo "--- Classic Problems ---"
    compare_spec "DiningPhilosophers" "$examples_dir/DiningPhilosophers/DiningPhilosophers.tla" "$examples_dir/DiningPhilosophers/DiningPhilosophers.cfg"
    compare_spec "MissionariesAndCannibals" "$examples_dir/MissionariesAndCannibals/MissionariesAndCannibals.tla" "$examples_dir/MissionariesAndCannibals/MissionariesAndCannibals.cfg"

    # Summary
    echo ""
    echo "=== Summary ==="
    echo -e "PASS: ${GREEN}$PASS${NC}"
    echo -e "FAIL: ${RED}$FAIL${NC}"
    echo -e "SKIP: ${YELLOW}$SKIP${NC}"

    if [ $FAIL -gt 0 ]; then
        echo ""
        echo -e "${RED}COMPARISON FAILED${NC}: TLA2 differs from TLC on $FAIL spec(s)"
        exit 1
    else
        echo ""
        echo -e "${GREEN}ALL COMPARISONS PASSED${NC}"
        exit 0
    fi
}

# Entry point
if [ $# -eq 2 ]; then
    # Single spec comparison
    compare_spec "$(basename "$1" .tla)" "$1" "$2"
elif [ $# -eq 1 ]; then
    # Single spec without config
    compare_spec "$(basename "$1" .tla)" "$1" ""
else
    # Full test suite
    run_test_suite
fi
