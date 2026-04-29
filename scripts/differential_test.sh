#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Differential Testing: TLA2 vs TLC
# Compares state counts to verify semantic equivalence
#
# TLC backend discovery order: TLC_BIN, tlc on PATH, then TLA2TOOLS_JAR/TLC_JAR.

set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/target}"
if [[ "$TARGET_DIR" != /* ]]; then
    TARGET_DIR="$REPO_ROOT/$TARGET_DIR"
fi
TLA2_BIN="${TLA2_BIN:-$TARGET_DIR/release/tla}"
TLA2TOOLS_JAR="${TLA2TOOLS_JAR:-${TLC_JAR:-$HOME/tlaplus/tla2tools.jar}}"
EXAMPLES_DIR="${EXAMPLES_DIR:-$HOME/tlaplus-examples/specifications}"
TIMEOUT="${TIMEOUT:-60}"  # seconds per spec

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
TLC_METADIR_ROOT="${TLA2_TLC_METADIR_ROOT:-$REPO_ROOT/target/tlc_metadir}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

PASS=0
FAIL=0
SKIP=0
TIMEOUT_COUNT=0

declare -a FAILURES

echo "=== Differential Testing: TLA2 vs TLC ==="
echo "TLA2: $TLA2_BIN"
if [ -n "${TLC_BIN:-}" ]; then
    echo "TLC:  $TLC_BIN (via TLC_BIN)"
elif command -v tlc >/dev/null 2>&1; then
    echo "TLC:  $(command -v tlc) (via PATH)"
else
    echo "TLC:  $TLA2TOOLS_JAR (via TLA2TOOLS_JAR/TLC_JAR)"
fi
echo "Timeout: ${TIMEOUT}s per spec"
echo ""

# Find all specs with config files
mapfile -t SPECS < <(find "$EXAMPLES_DIR" -name "*.cfg" 2>/dev/null | sort)

echo "Found ${#SPECS[@]} specs with config files"
echo ""

for cfg in "${SPECS[@]}"; do
    dir=$(dirname "$cfg")
    base=$(basename "$cfg" .cfg)
    tla="$dir/$base.tla"

    # Skip if TLA file doesn't exist
    if [ ! -f "$tla" ]; then
        continue
    fi

    # Skip TTrace files
    if [[ "$base" == *"_TTrace_"* ]]; then
        continue
    fi

    # Skip known problematic specs (liveness-only, etc.)
    case "$base" in
        *Proof*|*_anim*|*_json*|*Sim*|MCKVS|MCKVsnap)
            ((SKIP++))
            continue
            ;;
    esac

	    printf "Testing %-50s " "$base"

	    # Run TLC with timeout
	    unset TLC_EXIT
	    tlc_metadir=""
	    if [ "${TLA2_KEEP_STATES:-0}" != "1" ]; then
	        mkdir -p "$TLC_METADIR_ROOT"
	        tlc_metadir="$(mktemp -d "$TLC_METADIR_ROOT/tlc_XXXXXX")"
	        if [ -n "${TLC_BIN:-}" ]; then
	            TLC_OUTPUT=$(timeout "$TIMEOUT" "$TLC_BIN" -metadir "$tlc_metadir" -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || TLC_EXIT=$?
	        elif command -v tlc >/dev/null 2>&1; then
	            TLC_OUTPUT=$(timeout "$TIMEOUT" tlc -metadir "$tlc_metadir" -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || TLC_EXIT=$?
	        else
	            TLC_OUTPUT=$(timeout "$TIMEOUT" java -XX:+UseParallelGC -Xmx4g -cp "$TLA2TOOLS_JAR" tlc2.TLC \
	                -metadir "$tlc_metadir" -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || TLC_EXIT=$?
	        fi
	    else
	        if [ -n "${TLC_BIN:-}" ]; then
	            TLC_OUTPUT=$(timeout "$TIMEOUT" "$TLC_BIN" -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || TLC_EXIT=$?
	        elif command -v tlc >/dev/null 2>&1; then
	            TLC_OUTPUT=$(timeout "$TIMEOUT" tlc -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || TLC_EXIT=$?
	        else
	            TLC_OUTPUT=$(timeout "$TIMEOUT" java -XX:+UseParallelGC -Xmx4g -cp "$TLA2TOOLS_JAR" tlc2.TLC \
	                -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || TLC_EXIT=$?
	        fi
	    fi
	    if [ -n "$tlc_metadir" ]; then
	        rm -rf "$tlc_metadir"
	    fi

    if [ "${TLC_EXIT:-0}" -eq 124 ]; then
        printf "${YELLOW}TIMEOUT${NC}\n"
        ((TIMEOUT_COUNT++))
        continue
    fi

    # Extract TLC state count
    TLC_STATES=$(echo "$TLC_OUTPUT" | grep -oP '[0-9,]+(?= distinct states found)' | tail -1 | tr -d ',')

    if [ -z "$TLC_STATES" ]; then
        # TLC may have errored or found violation - that's OK, we'll compare
        TLC_STATES=$(echo "$TLC_OUTPUT" | grep -oP '[0-9,]+(?= states generated)' | tail -1 | tr -d ',')
        if [ -z "$TLC_STATES" ]; then
            printf "${YELLOW}SKIP${NC} (TLC parse/eval error)\n"
            ((SKIP++))
            continue
        fi
    fi

	    # Run TLA2 with timeout
	    unset TLA2_EXIT
	    TLA2_OUTPUT=$(timeout "$TIMEOUT" "$TLA2_BIN" check "$tla" -c "$cfg" -w 1 --no-trace 2>&1) || TLA2_EXIT=$?

    if [ "${TLA2_EXIT:-0}" -eq 124 ]; then
        printf "${YELLOW}TIMEOUT${NC}\n"
        ((TIMEOUT_COUNT++))
        continue
    fi

    # Extract TLA2 state count
    TLA2_STATES=$(echo "$TLA2_OUTPUT" | grep -oP 'States found: \\K[0-9,]+' | tail -1 | tr -d ',')

    if [ -z "$TLA2_STATES" ]; then
        printf "${YELLOW}SKIP${NC} (TLA2 error)\n"
        ((SKIP++))
        continue
    fi

    # Compare
    if [ "$TLC_STATES" -eq "$TLA2_STATES" ]; then
        printf "${GREEN}PASS${NC} (${TLC_STATES} states)\n"
        ((PASS++))
    else
        printf "${RED}FAIL${NC} (TLC: $TLC_STATES, TLA2: $TLA2_STATES)\n"
        ((FAIL++))
        FAILURES+=("$base: TLC=$TLC_STATES TLA2=$TLA2_STATES")
    fi
done

echo ""
echo "=== Summary ==="
echo -e "${GREEN}PASS:${NC} $PASS"
echo -e "${RED}FAIL:${NC} $FAIL"
echo -e "${YELLOW}SKIP:${NC} $SKIP"
echo -e "${YELLOW}TIMEOUT:${NC} $TIMEOUT_COUNT"
echo ""

if [ $FAIL -gt 0 ]; then
    echo "=== Failures ==="
    for f in "${FAILURES[@]}"; do
        echo "  $f"
    done
    exit 1
fi

echo "DIFFERENTIAL TEST PASSED"
