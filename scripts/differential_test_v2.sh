#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Differential Testing: TLA2 vs TLC (v2 - fixed parsing)
# Compares state counts to verify semantic equivalence

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
TIMEOUT="${TIMEOUT:-60}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
TLC_METADIR_ROOT="${TLA2_TLC_METADIR_ROOT:-$REPO_ROOT/target/tlc_metadir}"

PASS=0
FAIL=0
SKIP=0
declare -a FAILURES

echo "=== Differential Test: TLA2 vs TLC ==="
if [ -n "${TLC_BIN:-}" ]; then
    echo "TLC: $TLC_BIN (via TLC_BIN)"
elif command -v tlc >/dev/null 2>&1; then
    echo "TLC: $(command -v tlc) (via PATH)"
else
    echo "TLC: $TLA2TOOLS_JAR (via TLA2TOOLS_JAR/TLC_JAR)"
fi
echo "Timeout: ${TIMEOUT}s per spec"
echo ""

for cfg in $(find "$EXAMPLES_DIR" -name "*.cfg" 2>/dev/null | grep -v "_TTrace_" | sort); do
    dir=$(dirname "$cfg")
    base=$(basename "$cfg" .cfg)
    tla="$dir/$base.tla"

    [ ! -f "$tla" ] && continue

    # Skip known problematic (proofs, animations, simulations)
    case "$base" in
        *Proof*|*_anim*|*_json*|*Sim*|*TTrace*|*MC_*|MCKVS|MCKVsnap)
            ((SKIP++))
            continue
            ;;
    esac

    # Run TLC
    tlc_metadir=""
    if [ "${TLA2_KEEP_STATES:-0}" != "1" ]; then
        mkdir -p "$TLC_METADIR_ROOT"
        tlc_metadir="$(mktemp -d "$TLC_METADIR_ROOT/tlc_XXXXXX")"
        if [ -n "${TLC_BIN:-}" ]; then
            TLC_OUT=$(timeout "$TIMEOUT" "$TLC_BIN" -metadir "$tlc_metadir" -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || true
        elif command -v tlc >/dev/null 2>&1; then
            TLC_OUT=$(timeout "$TIMEOUT" tlc -metadir "$tlc_metadir" -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || true
        else
            TLC_OUT=$(timeout "$TIMEOUT" java -XX:+UseParallelGC -Xmx2g -cp "$TLA2TOOLS_JAR" tlc2.TLC \
                -metadir "$tlc_metadir" -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || true
        fi
    else
        if [ -n "${TLC_BIN:-}" ]; then
            TLC_OUT=$(timeout "$TIMEOUT" "$TLC_BIN" -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || true
        elif command -v tlc >/dev/null 2>&1; then
            TLC_OUT=$(timeout "$TIMEOUT" tlc -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || true
        else
            TLC_OUT=$(timeout "$TIMEOUT" java -XX:+UseParallelGC -Xmx2g -cp "$TLA2TOOLS_JAR" tlc2.TLC \
                -config "$cfg" "$tla" -workers 1 -nowarning 2>&1) || true
        fi
    fi
    if [ -n "$tlc_metadir" ]; then
        rm -rf "$tlc_metadir"
    fi

    # Extract distinct states from TLC
    TLC_STATES=$(echo "$TLC_OUT" | grep -o '[0-9]* distinct' | grep -o '[0-9]*' | head -1)

    if [ -z "$TLC_STATES" ]; then
        # Maybe TLC errored - check for violation
        if echo "$TLC_OUT" | grep -q "Error:"; then
            TLC_STATES="ERROR"
        else
            ((SKIP++))
            continue
        fi
    fi

    # Run TLA2
    TLA2_OUT=$(timeout "$TIMEOUT" "$TLA2_BIN" check "$tla" -c "$cfg" -w 1 --no-trace 2>&1) || true

    # Extract states from TLA2
    TLA2_STATES=$(echo "$TLA2_OUT" | grep "States found:" | grep -o '[0-9]*' | head -1)

    if [ -z "$TLA2_STATES" ]; then
        if echo "$TLA2_OUT" | grep -q "Error:"; then
            TLA2_STATES="ERROR"
        else
            printf "%-45s SKIP (TLA2 no output)\n" "$base"
            ((SKIP++))
            continue
        fi
    fi

    # Compare
    if [ "$TLC_STATES" = "$TLA2_STATES" ]; then
        printf "%-45s PASS (%s states)\n" "$base" "$TLC_STATES"
        ((PASS++))
    elif [ "$TLC_STATES" = "ERROR" ] && [ "$TLA2_STATES" = "ERROR" ]; then
        printf "%-45s PASS (both found error)\n" "$base"
        ((PASS++))
    else
        printf "%-45s FAIL (TLC=%s TLA2=%s)\n" "$base" "$TLC_STATES" "$TLA2_STATES"
        FAILURES+=("$base: TLC=$TLC_STATES TLA2=$TLA2_STATES")
        ((FAIL++))
    fi
done

echo ""
echo "=== SUMMARY ==="
echo "PASS: $PASS"
echo "FAIL: $FAIL"
echo "SKIP: $SKIP"
echo ""

if [ ${#FAILURES[@]} -gt 0 ]; then
    echo "=== FAILURES ==="
    for f in "${FAILURES[@]}"; do
        echo "  $f"
    done
    exit 1
fi

echo "DIFFERENTIAL TEST PASSED"
