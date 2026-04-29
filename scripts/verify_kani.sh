#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Kani batch verification script for TLA2
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Part of #410: Create Kani harness batch verification script
#
# Runs all known-working Kani harnesses and reports results.
# BigInt-dependent harnesses are skipped (documented below).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Timeout per harness in seconds (30 minutes default)
# Prevents runaway CBMC processes (see: 10-hour stuck process incident 2026-01-26)
HARNESS_TIMEOUT=${HARNESS_TIMEOUT:-1800}

# Find timeout command (gtimeout on macOS via coreutils, timeout on Linux)
if command -v gtimeout &> /dev/null; then
    TIMEOUT_CMD="gtimeout"
elif command -v timeout &> /dev/null; then
    TIMEOUT_CMD="timeout"
else
    TIMEOUT_CMD=""
fi

# Known-working harnesses (bool/string paths, no BigInt dependencies)
WORKING_HARNESSES=(
    # Boolean operations
    verify_bool_fingerprint_deterministic
    verify_bool_equality_reflexive
    verify_bool_equality_symmetric
    verify_bool_fingerprint_sensitive
    verify_bool_and_identity
    verify_bool_and_annihilator
    verify_bool_and_commutative
    verify_bool_and_associative
    verify_bool_and_complement
    verify_bool_or_identity
    verify_bool_or_annihilator
    verify_bool_or_commutative
    verify_bool_or_associative
    verify_bool_or_complement
    verify_bool_double_negation
    verify_bool_ord_antisymmetric
    verify_bool_ord_transitive
    verify_bool_ord_total
    verify_bool_ord_eq_consistency

    # String operations
    verify_string_fingerprint_deterministic
    verify_string_equality_reflexive
    verify_string_equality_symmetric
    verify_string_ord_total
    verify_string_ord_transitive
    verify_string_ord_eq_consistency

    # Type discrimination (different primitive types)
    verify_bool_string_not_equal

    # Boolean logic
    verify_de_morgan_and
    verify_de_morgan_or
    verify_implies_definition
    verify_implies_reflexive
    verify_equiv_definition
    verify_equiv_reflexive
    verify_equiv_symmetric

    # Conditional operations
    verify_if_true_returns_then_branch
    verify_if_false_returns_else_branch
    verify_if_same_branches_equals_branch
    verify_nested_if_consistency

    # Empty state (no BigInt)
    verify_empty_state_fingerprint_deterministic
)

# Harnesses blocked by BigInt limitations
# These are documented but not run
BIGINT_BLOCKED=(
    verify_int_fingerprint_deterministic
    verify_int_equality_reflexive
    verify_int_equality_symmetric
    verify_int_add_commutative
    verify_int_add_associative
    verify_int_add_identity
    verify_int_add_inverse
    verify_int_mul_commutative
    verify_int_mul_associative
    verify_int_mul_identity
    verify_int_mul_distributes_over_add
    verify_int_div_mod_relationship
    verify_int_mod_range
    verify_int_leq_reflexive
    verify_int_lt_irreflexive
    verify_int_lt_transitive
    verify_int_trichotomy
    verify_int_ord_antisymmetric
    verify_int_ord_transitive
    verify_int_ord_total
    verify_int_ord_eq_consistency
    verify_adjacent_int_fingerprint_sensitive
    verify_bool_int_not_equal
    verify_int_string_not_equal
    verify_interval_cardinality
    verify_interval_length
    verify_interval_contains_bounds
    verify_interval_excludes_outside
    verify_interval_membership_correctness
    verify_interval_iteration_count
    verify_interval_iteration_order
    verify_interval_contains_all_iterated
    verify_singleton_interval_cardinality
    # Many more - any harness using Value::Int or intervals
)

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

usage() {
    echo "Usage: $0 [OPTIONS]"
    echo ""
    echo "Options:"
    echo "  -h, --help       Show this help message"
    echo "  -l, --list       List harnesses without running"
    echo "  -q, --quick      Run quick subset (first 5 harnesses)"
    echo "  -v, --verbose    Show Kani output for each harness"
    echo "  -s, --single N   Run single harness by name"
    echo "  -t, --timeout S  Timeout per harness in seconds (default: $HARNESS_TIMEOUT)"
    echo ""
    echo "Environment:"
    echo "  HARNESS_TIMEOUT  Override default timeout (seconds)"
    echo ""
    echo "Exit codes:"
    echo "  0  All harnesses passed"
    echo "  1  One or more harnesses failed (or timeout)"
    echo "  2  Script error"
}

list_harnesses() {
    echo "=== Known-Working Harnesses (${#WORKING_HARNESSES[@]}) ==="
    for h in "${WORKING_HARNESSES[@]}"; do
        echo "  $h"
    done
    echo ""
    echo "=== BigInt-Blocked Harnesses (${#BIGINT_BLOCKED[@]} documented) ==="
    echo "  (see script source for full list)"
}

run_harness() {
    local harness=$1
    local verbose=${2:-false}

    echo -n "Running $harness... "

    local output
    local status=0

    # Use timeout if available, otherwise run without (with warning)
    if [[ -n "$TIMEOUT_CMD" ]]; then
        output=$($TIMEOUT_CMD "$HARNESS_TIMEOUT" cargo kani --package tla-check --harness "$harness" --no-default-features 2>&1) || status=$?
    else
        if [[ -z "${TIMEOUT_WARNED:-}" ]]; then
            echo -e "${YELLOW}WARNING: No timeout command available. Install coreutils for timeout support.${NC}" >&2
            TIMEOUT_WARNED=1
        fi
        output=$(cargo kani --package tla-check --harness "$harness" --no-default-features 2>&1) || status=$?
    fi

    # Exit code 124 = timeout killed the process
    if [[ $status -eq 124 ]]; then
        echo -e "${RED}TIMEOUT${NC} (>${HARNESS_TIMEOUT}s)"
        echo "  Harness exceeded ${HARNESS_TIMEOUT}s limit - likely stuck CBMC"
        return 1
    fi

    # Kani prints either `VERIFICATION: SUCCESSFUL` or `VERIFICATION:- SUCCESSFUL` (note the hyphen),
    # depending on version/output formatting.
    if [[ $status -eq 0 ]] && echo "$output" | grep -qE "VERIFICATION: *-? *SUCCESSFUL"; then
        echo -e "${GREEN}PASS${NC}"
        if [[ "$verbose" == "true" ]]; then
            echo "$output" | tail -10
        fi
        return 0
    else
        echo -e "${RED}FAIL${NC}"
        if echo "$output" | grep -qE "VERIFICATION: *-? *FAILED"; then
            echo "  Verification failed"
        elif echo "$output" | grep -q "error\["; then
            echo "  Compilation error"
        else
            echo "  Unknown error (exit code: $status)"
        fi
        if [[ "$verbose" == "true" ]]; then
            echo "$output"
        fi
        return 1
    fi
}

main() {
    local list_only=false
    local quick=false
    local verbose=false
    local single_harness=""

    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                usage
                exit 0
                ;;
            -l|--list)
                list_only=true
                shift
                ;;
            -q|--quick)
                quick=true
                shift
                ;;
            -v|--verbose)
                verbose=true
                shift
                ;;
            -s|--single)
                single_harness="$2"
                shift 2
                ;;
            -t|--timeout)
                HARNESS_TIMEOUT="$2"
                shift 2
                ;;
            *)
                echo "Unknown option: $1"
                usage
                exit 2
                ;;
        esac
    done

    if [[ "$list_only" == "true" ]]; then
        list_harnesses
        exit 0
    fi

    cd "$PROJECT_ROOT"

    # Check Kani is installed
    if ! command -v kani &> /dev/null; then
        echo -e "${RED}ERROR: Kani not installed${NC}"
        echo "Install with: cargo install --locked kani-verifier"
        exit 2
    fi

    local harnesses_to_run=()

    if [[ -n "$single_harness" ]]; then
        harnesses_to_run=("$single_harness")
    elif [[ "$quick" == "true" ]]; then
        harnesses_to_run=("${WORKING_HARNESSES[@]:0:5}")
    else
        harnesses_to_run=("${WORKING_HARNESSES[@]}")
    fi

    echo "========================================"
    echo "TLA2 Kani Batch Verification"
    echo "========================================"
    echo "Harnesses to run: ${#harnesses_to_run[@]}"
    echo "BigInt-blocked: ${#BIGINT_BLOCKED[@]} (skipped)"
    echo "Timeout per harness: ${HARNESS_TIMEOUT}s"
    if [[ -z "$TIMEOUT_CMD" ]]; then
        echo -e "${YELLOW}WARNING: No timeout command - install coreutils${NC}"
    fi
    echo ""

    local passed=0
    local failed=0
    local failed_names=()

    for harness in "${harnesses_to_run[@]}"; do
        if run_harness "$harness" "$verbose"; then
            ((passed++))
        else
            ((failed++))
            failed_names+=("$harness")
        fi
    done

    echo ""
    echo "========================================"
    echo "Summary"
    echo "========================================"
    echo -e "Passed: ${GREEN}$passed${NC}"
    echo -e "Failed: ${RED}$failed${NC}"
    echo "Skipped (BigInt): ${#BIGINT_BLOCKED[@]}"

    if [[ $failed -gt 0 ]]; then
        echo ""
        echo "Failed harnesses:"
        for name in "${failed_names[@]}"; do
            echo "  - $name"
        done
        exit 1
    fi

    exit 0
}

main "$@"
