#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Test all liveness specs against TLC baseline
# This script discovers which liveness specs TLA2 handles correctly

set -eo pipefail

echo "=== TLA2 Liveness Spec Testing ==="
echo "Date: $(date)"
echo ""

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/target}"
if [[ "$TARGET_DIR" != /* ]]; then
    TARGET_DIR="$REPO_ROOT/$TARGET_DIR"
fi

# Per-test timeouts (seconds). Some TLC example specs can take a long time.
# Huang takes ~300s total (TLC + TLA2), so allow 600s per tool.
TLC_TIMEOUT_SECS="${TLC_TIMEOUT_SECS:-600}"
TLA2_TIMEOUT_SECS="${TLA2_TIMEOUT_SECS:-600}"

# Run a command with a timeout, capturing stdout/stderr to stdout.
# Exits with the command's exit code, or 124 on timeout.
run_with_timeout() {
    local timeout_secs="$1"
    shift

    python3 - "$timeout_secs" "$@" <<'PY'
import subprocess
import sys

timeout = float(sys.argv[1])
cmd = sys.argv[2:]

try:
    p = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=timeout,
    )
    sys.stdout.write(p.stdout)
    sys.exit(p.returncode)
except subprocess.TimeoutExpired as e:
    # Handle partial output - may be bytes in some Python versions
    if e.stdout:
        if isinstance(e.stdout, bytes):
            sys.stdout.write(e.stdout.decode('utf-8', errors='replace'))
        else:
            sys.stdout.write(e.stdout)
    sys.stdout.write(f"\n[TIMEOUT] after {timeout:.0f}s: {' '.join(cmd)}\n")
    sys.exit(124)
PY
}

# Classify a single tool's output using liveness_verdict_lib.py
# Usage: classify_tool <scripts_dir> <output_file> <return_code> <tool>
# tool: "tlc" or "tla2"
# Outputs one line: status|states (states may be empty if unparseable)
classify_tool() {
    local scripts_dir="$1"
    local output_file="$2"
    local rc="$3"
    local tool="$4"

    python3 - "$scripts_dir" "$output_file" "$rc" "$tool" <<'PY'
import sys
from pathlib import Path

sys.path.insert(0, sys.argv[1])
from liveness_verdict_lib import classify_tlc_status, classify_tla2_status, parse_tlc_states, parse_tla2_states

output = Path(sys.argv[2]).read_text(encoding="utf-8", errors="replace")
rc = int(sys.argv[3])
tool = sys.argv[4]

if tool == "tlc":
    status = classify_tlc_status(output, rc)
    states = parse_tlc_states(output)
else:
    status = classify_tla2_status(output, rc)
    states = parse_tla2_states(output)

print(f"{status}|{states if states is not None else ''}")
PY
}

# Build release binary
echo "Building release-canary binary..."

TLA2="$TARGET_DIR/release-canary/tla"
TLC_JAR="${TLC_JAR:-$HOME/tlaplus/tla2tools.jar}"
COMMUNITY_MODULES="${COMMUNITY_MODULES:-$HOME/tlaplus/CommunityModules.jar}"
if [ -f "$COMMUNITY_MODULES" ]; then
    TLC_CP="$TLC_JAR:$COMMUNITY_MODULES"
else
    TLC_CP="$TLC_JAR"
fi
EXAMPLES="$HOME/tlaplus-examples/specifications"
TLC_TLA_LIBRARY="$REPO_ROOT/test_specs/tla_library"
export TLA_PATH="$TLC_TLA_LIBRARY${TLA_PATH:+:$TLA_PATH}"

PASS=0
FAIL=0
SKIP=0
ERROR=0

# Results file
RESULTS_FILE="$REPO_ROOT/tests/liveness/results.txt"
mkdir -p "$REPO_ROOT/tests/liveness"
echo "# Liveness Test Results - $(date)" > "$RESULTS_FILE"
echo "" >> "$RESULTS_FILE"

run_liveness_test() {
    local name="$1"
    local spec="$2"
    local config="$3"
    local extra_args="${4:-}"

    if [ ! -f "$spec" ]; then
        echo "[ SKIP ] $name - spec not found"
        echo "SKIP: $name (spec not found)" >> "$RESULTS_FILE"
        SKIP=$((SKIP + 1))
        return
    fi

    if [ ! -f "$config" ]; then
        echo "[ SKIP ] $name - config not found"
        echo "SKIP: $name (config not found)" >> "$RESULTS_FILE"
        SKIP=$((SKIP + 1))
        return
    fi

    # Temp files for tool outputs (used by verdict classifier)
    local _tlc_tmp _tla2_tmp
    _tlc_tmp=$(mktemp)
    _tla2_tmp=$(mktemp)

    # Run TLC first to get baseline
    local tlc_metadir=""
    if [ "${TLA2_KEEP_STATES:-0}" != "1" ]; then
        local tlc_metadir_root="${TLA2_TLC_METADIR_ROOT:-$REPO_ROOT/target/tlc_metadir}"
        mkdir -p "$tlc_metadir_root"
        tlc_metadir="$(mktemp -d "$tlc_metadir_root/tlc_XXXXXX")"
    fi
    set +e
    if [ -n "$tlc_metadir" ]; then
        run_with_timeout "$TLC_TIMEOUT_SECS" java -DTLA-Library="$TLC_TLA_LIBRARY" -cp "$TLC_CP" tlc2.TLC -metadir "$tlc_metadir" -config "$config" "$spec" -workers 1 > "$_tlc_tmp" 2>&1
    else
        run_with_timeout "$TLC_TIMEOUT_SECS" java -DTLA-Library="$TLC_TLA_LIBRARY" -cp "$TLC_CP" tlc2.TLC -config "$config" "$spec" -workers 1 > "$_tlc_tmp" 2>&1
    fi
    local tlc_rc=$?
    set -e
    if [ -n "$tlc_metadir" ]; then
        rm -rf "$tlc_metadir"
    fi

    # Classify TLC verdict via liveness_verdict_lib.py
    local tlc_verdict tlc_status tlc_states
    tlc_verdict=$(classify_tool "$SCRIPT_DIR" "$_tlc_tmp" "$tlc_rc" "tlc")
    IFS='|' read -r tlc_status tlc_states <<< "$tlc_verdict"

    if [ "$tlc_status" = "timeout" ]; then
        echo "[ SKIP ] $name - TLC timeout (${TLC_TIMEOUT_SECS}s)"
        echo "SKIP: $name (TLC timeout)" >> "$RESULTS_FILE"
        SKIP=$((SKIP + 1))
        rm -f "$_tlc_tmp" "$_tla2_tmp"
        return
    fi

    if [ "$tlc_status" = "error" ] || [ "$tlc_status" = "unknown" ]; then
        echo "[ SKIP ] $name - TLC $tlc_status"
        echo "RESULT|name=$name|tlc_status=$tlc_status|tla2_status=skipped|overall=SKIP" >> "$RESULTS_FILE"
        SKIP=$((SKIP + 1))
        rm -f "$_tlc_tmp" "$_tla2_tmp"
        return
    fi

    # Run TLA2
    set +e
    run_with_timeout "$TLA2_TIMEOUT_SECS" $TLA2 check "$spec" --config "$config" --workers 1 $extra_args > "$_tla2_tmp" 2>&1
    local tla2_rc=$?
    set -e

    # Classify TLA2 verdict via liveness_verdict_lib.py
    local tla2_verdict tla2_status tla2_states
    tla2_verdict=$(classify_tool "$SCRIPT_DIR" "$_tla2_tmp" "$tla2_rc" "tla2")
    IFS='|' read -r tla2_status tla2_states <<< "$tla2_verdict"

    # Clean up temp files
    rm -f "$_tlc_tmp" "$_tla2_tmp"

    evaluate_verdicts "$name" "$tlc_status" "$tla2_status" "$tlc_states" "$tla2_states"
}

# Apply two-axis verdict gate and emit results.
# Modifies global PASS/FAIL/ERROR counters and writes to RESULTS_FILE.
evaluate_verdicts() {
    local name="$1"
    local tlc_status="$2" tla2_status="$3"
    local tlc_states="$4" tla2_states="$5"

    # Handle TLA2 timeout/error
    if [ "$tla2_status" = "timeout" ]; then
        echo "[ ERROR ] $name: TLA2 timeout (${TLA2_TIMEOUT_SECS}s) (TLC: ${tlc_states:-?} states)"
        echo "RESULT|name=$name|tlc_status=$tlc_status|tla2_status=timeout|tlc_states=${tlc_states:-}|tla2_states=|overall=ERROR" >> "$RESULTS_FILE"
        ERROR=$((ERROR + 1))
        return
    fi

    if [ "$tla2_status" = "error" ] || [ "$tla2_status" = "unknown" ]; then
        echo "[ ERROR ] $name: TLA2 $tla2_status (TLC: ${tlc_states:-?} states)"
        echo "RESULT|name=$name|tlc_status=$tlc_status|tla2_status=$tla2_status|tlc_states=${tlc_states:-}|tla2_states=${tla2_states:-}|overall=ERROR" >> "$RESULTS_FILE"
        ERROR=$((ERROR + 1))
        return
    fi

    # Two-axis verdict gate (design doc §2): compare verdict class + state count
    local verdict_match="no" state_match="no" overall="FAIL"

    [ "$tlc_status" = "$tla2_status" ] && verdict_match="yes"
    [ -n "$tlc_states" ] && [ -n "$tla2_states" ] && [ "$tlc_states" = "$tla2_states" ] && state_match="yes"

    if [ "$verdict_match" = "no" ]; then
        overall="FAIL"
    elif [ "$tlc_status" = "success" ] && [ -n "$tlc_states" ] && [ -n "$tla2_states" ] && [ "$tlc_states" != "$tla2_states" ]; then
        overall="FAIL"
    else
        overall="PASS"
    fi

    # Structured result line (design doc §3)
    echo "RESULT|name=$name|tlc_status=$tlc_status|tla2_status=$tla2_status|tlc_states=${tlc_states:-}|tla2_states=${tla2_states:-}|verdict_match=$verdict_match|state_match=$state_match|overall=$overall" >> "$RESULTS_FILE"

    if [ "$overall" = "PASS" ]; then
        echo "[ PASS ] $name: ${tla2_states:-?} states (TLC: ${tlc_states:-?})"
        echo "PASS: $name (${tla2_states:-?} states)" >> "$RESULTS_FILE"
        PASS=$((PASS + 1))
    else
        echo "[ FAIL ] $name: verdict=$tlc_status/$tla2_status states=TLA2:${tla2_states:-?}/TLC:${tlc_states:-?}"
        echo "FAIL: $name (verdict=$tlc_status/$tla2_status, TLA2=${tla2_states:-?}, TLC=${tlc_states:-?})" >> "$RESULTS_FILE"
        FAIL=$((FAIL + 1))
    fi
}

echo "Running liveness spec tests..."
echo ""

# SpecifyingSystems/Liveness specs
echo "=== SpecifyingSystems/Liveness ==="
run_liveness_test "LiveHourClock" \
    "$EXAMPLES/SpecifyingSystems/Liveness/LiveHourClock.tla" \
    "$EXAMPLES/SpecifyingSystems/Liveness/LiveHourClock.cfg"

run_liveness_test "MCLiveInternalMemory" \
    "$EXAMPLES/SpecifyingSystems/Liveness/MCLiveInternalMemory.tla" \
    "$EXAMPLES/SpecifyingSystems/Liveness/MCLiveInternalMemory.cfg"

run_liveness_test "MCLiveWriteThroughCache" \
    "$EXAMPLES/SpecifyingSystems/Liveness/MCLiveWriteThroughCache.tla" \
    "$EXAMPLES/SpecifyingSystems/Liveness/MCLiveWriteThroughCache.cfg"

echo ""
echo "=== Allocator Specs ==="
run_liveness_test "SimpleAllocator" \
    "$EXAMPLES/allocator/SimpleAllocator.tla" \
    "$EXAMPLES/allocator/SimpleAllocator.cfg"

run_liveness_test "SchedulingAllocator" \
    "$EXAMPLES/allocator/SchedulingAllocator.tla" \
    "$EXAMPLES/allocator/SchedulingAllocator.cfg"

echo ""
echo "=== EWD Termination Detection ==="
run_liveness_test "EWD840+Liveness" \
    "$EXAMPLES/ewd840/EWD840.tla" \
    "$REPO_ROOT/test_specs/EWD840_Liveness.cfg"

run_liveness_test "SyncTerminationDetection" \
    "$EXAMPLES/ewd840/SyncTerminationDetection.tla" \
    "$EXAMPLES/ewd840/SyncTerminationDetection.cfg"

echo ""
echo "=== Other Liveness Specs ==="

# TokenRing (ewd426) has liveness property
run_liveness_test "TokenRing" \
    "$EXAMPLES/ewd426/TokenRing.tla" \
    "$EXAMPLES/ewd426/TokenRing.cfg"

# glowingRaccoon specs have temporal properties
run_liveness_test "stages" \
    "$EXAMPLES/glowingRaccoon/stages.tla" \
    "$EXAMPLES/glowingRaccoon/stages.cfg"

run_liveness_test "product" \
    "$EXAMPLES/glowingRaccoon/product.tla" \
    "$EXAMPLES/glowingRaccoon/product.cfg"

run_liveness_test "clean" \
    "$EXAMPLES/glowingRaccoon/clean.tla" \
    "$EXAMPLES/glowingRaccoon/clean.cfg"

# CigaretteSmokers has fairness
run_liveness_test "CigaretteSmokers" \
    "$EXAMPLES/CigaretteSmokers/CigaretteSmokers.tla" \
    "$EXAMPLES/CigaretteSmokers/CigaretteSmokers.cfg"

# DiningPhilosophers
run_liveness_test "DiningPhilosophers" \
    "$EXAMPLES/DiningPhilosophers/DiningPhilosophers.tla" \
    "$EXAMPLES/DiningPhilosophers/DiningPhilosophers.cfg"

# ChangRoberts ring election
run_liveness_test "MCChangRoberts" \
    "$EXAMPLES/chang_roberts/MCChangRoberts.tla" \
    "$EXAMPLES/chang_roberts/MCChangRoberts.cfg"

# MCEcho - distributed echo algorithm
run_liveness_test "MCEcho" \
    "$EXAMPLES/echo/MCEcho.tla" \
    "$EXAMPLES/echo/MCEcho.cfg"

# Bakery algorithm (mutex)
run_liveness_test "MCBakery" \
    "$EXAMPLES/Bakery-Boulangerie/MCBakery.tla" \
    "$EXAMPLES/Bakery-Boulangerie/MCBakery.cfg"

# Paxos specs (Voting instances Consensus)
run_liveness_test "MCVoting" \
    "$EXAMPLES/Paxos/MCVoting.tla" \
    "$EXAMPLES/Paxos/MCVoting.cfg"

# bcastFolklore - broadcast folklore algorithm
run_liveness_test "bcastFolklore" \
    "$EXAMPLES/bcastFolklore/bcastFolklore.tla" \
    "$EXAMPLES/bcastFolklore/bcastFolklore.cfg"

echo ""
echo "=== Additional Liveness Specs ==="

# EWD998 - Termination detection (extended)
run_liveness_test "EWD998" \
    "$EXAMPLES/ewd998/EWD998.tla" \
    "$EXAMPLES/ewd998/EWD998.cfg"

run_liveness_test "AsyncTerminationDetection" \
    "$EXAMPLES/ewd998/AsyncTerminationDetection.tla" \
    "$EXAMPLES/ewd998/AsyncTerminationDetection.cfg"

# ReadersWriters - classic concurrent programming
run_liveness_test "ReadersWriters" \
    "$EXAMPLES/ReadersWriters/MC.tla" \
    "$EXAMPLES/ReadersWriters/MC.cfg"

# Peterson - mutual exclusion
run_liveness_test "Peterson" \
    "$EXAMPLES/locks_auxiliary_vars/Peterson.tla" \
    "$EXAMPLES/locks_auxiliary_vars/Peterson.cfg"

# Huang - leader election
run_liveness_test "Huang" \
    "$EXAMPLES/Huang/Huang.tla" \
    "$EXAMPLES/Huang/Huang.cfg"

# Prisoners - logic puzzle with liveness
run_liveness_test "Prisoners" \
    "$EXAMPLES/Prisoners/Prisoners.tla" \
    "$EXAMPLES/Prisoners/Prisoners.cfg"

# Barrier - synchronization barrier
run_liveness_test "Barrier" \
    "$EXAMPLES/barriers/Barrier.tla" \
    "$EXAMPLES/barriers/Barrier.cfg"

# KeyValueStore - distributed key-value store
run_liveness_test "MCKVsnap" \
    "$EXAMPLES/KeyValueStore/MCKVsnap.tla" \
    "$EXAMPLES/KeyValueStore/MCKVsnap.cfg"

# ReplicatedLog - distributed consensus log
run_liveness_test "MCReplicatedLog" \
    "$EXAMPLES/FiniteMonotonic/MCReplicatedLog.tla" \
    "$EXAMPLES/FiniteMonotonic/MCReplicatedLog.cfg"

# Disruptor - high-performance queue liveness
run_liveness_test "Disruptor_MPMC_liveliness" \
    "$EXAMPLES/Disruptor/Disruptor_MPMC.tla" \
    "$EXAMPLES/Disruptor/Disruptor_MPMC_liveliness.cfg"

# EWD687a - termination detection variant
run_liveness_test "MCEWD687a" \
    "$EXAMPLES/ewd687a/MCEWD687a.tla" \
    "$EXAMPLES/ewd687a/MCEWD687a.cfg"

# SpanTree - spanning tree construction
run_liveness_test "SpanTree" \
    "$EXAMPLES/SpanningTree/SpanTree.tla" \
    "$EXAMPLES/SpanningTree/SpanTree.cfg"

# Standalone local temporal-pattern specs for #1518 acceptance criteria
echo ""
echo "=== Local Pattern Specs (#1518) ==="

run_liveness_test "Pattern_AlwaysEventually" \
    "$REPO_ROOT/test_specs/liveness_patterns/AlwaysEventually.tla" \
    "$REPO_ROOT/test_specs/liveness_patterns/AlwaysEventually.cfg"

run_liveness_test "Pattern_EventuallyAlways" \
    "$REPO_ROOT/test_specs/liveness_patterns/EventuallyAlways.tla" \
    "$REPO_ROOT/test_specs/liveness_patterns/EventuallyAlways.cfg"

run_liveness_test "Pattern_WeakFairness" \
    "$REPO_ROOT/test_specs/liveness_patterns/WeakFairness.tla" \
    "$REPO_ROOT/test_specs/liveness_patterns/WeakFairness.cfg"

run_liveness_test "Pattern_StrongFairness" \
    "$REPO_ROOT/test_specs/liveness_patterns/StrongFairness.tla" \
    "$REPO_ROOT/test_specs/liveness_patterns/StrongFairness.cfg"

run_liveness_test "Pattern_LeadsTo" \
    "$REPO_ROOT/test_specs/liveness_patterns/LeadsTo.tla" \
    "$REPO_ROOT/test_specs/liveness_patterns/LeadsTo.cfg"

# DijkstraMutex - Dijkstra mutual exclusion
# NOTE: Skipped - MC.tla uses spec aliases (spec_1293897152943429000 == LSpec) which TLA2
# cannot resolve (operator not found error). TLC baseline passes with 90882 states.
# run_liveness_test "DijkstraMutex" \
#     "$EXAMPLES/dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC.tla" \
#     "$EXAMPLES/dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC.cfg"

echo ""
echo "=== Summary ==="
echo "PASS:  $PASS"
echo "FAIL:  $FAIL"
echo "ERROR: $ERROR"
echo "SKIP:  $SKIP"
echo ""
echo "Results saved to: $RESULTS_FILE"

if [ $FAIL -gt 0 ] || [ $ERROR -gt 0 ]; then
    echo "SOME TESTS FAILED OR HAD ERRORS"
    exit 1
else
    echo "ALL TESTS PASSED"
    exit 0
fi
