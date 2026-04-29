#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Mass TLC Comparison Script
# Compares TLA2 against TLC for all specs with .cfg files in tlaplus/Examples
# Part of Phase 2: Mass Model Check Validation

set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/target}"
if [[ "$TARGET_DIR" != /* ]]; then
    TARGET_DIR="$REPO_ROOT/$TARGET_DIR"
fi

# Build release binary
echo "Building release-canary binary..."

TLA2="$TARGET_DIR/release-canary/tla"
TLC_JAR="${TLC_JAR:-$HOME/tlaplus/tla2tools.jar}"
EXAMPLES_DIR="$HOME/tlaplus-examples/specifications"
REPORTS_DIR="$REPO_ROOT/reports"
DATE=$(date +%Y-%m-%d)
REPORT_FILE="$REPORTS_DIR/tlc_comparison_$DATE.md"
CSV_FILE="$REPORTS_DIR/tlc_comparison_$DATE.csv"

# Timeout for each spec (seconds)
TIMEOUT=${TIMEOUT:-60}

# Temp directories
TLC_META=$(mktemp -d)
trap "rm -rf $TLC_META" EXIT

# Ensure reports directory exists
mkdir -p "$REPORTS_DIR"

# CSV header
echo "spec,cfg,tla2_states,tlc_states,tla2_time,tlc_time,match,error" > "$CSV_FILE"

# Counters
TOTAL=0
PASS=0
FAIL=0
SKIP=0
ERROR=0

# Arrays for results
declare -a RESULTS

echo "=== TLA2 vs TLC Mass Comparison ==="
echo "Date: $(date)"
echo "Testing against: $EXAMPLES_DIR"
echo "Timeout: ${TIMEOUT}s per spec"
echo ""

# Check prerequisites
if [ ! -d "$EXAMPLES_DIR" ]; then
    echo "ERROR: tlaplus-examples not found at $EXAMPLES_DIR"
    exit 1
fi

if [ ! -f "$TLC_JAR" ]; then
    echo "ERROR: TLC jar not found at $TLC_JAR"
    exit 1
fi

# Build classpath with CommunityModules if available
COMMUNITY_MODULES="${COMMUNITY_MODULES:-$HOME/tlaplus/CommunityModules.jar}"
if [ -f "$COMMUNITY_MODULES" ]; then
    TLC_CP="$TLC_JAR:$COMMUNITY_MODULES"
else
    TLC_CP="$TLC_JAR"
fi

# Find all .tla files with corresponding .cfg
echo "Finding specs with config files..."
while IFS= read -r cfg; do
    tla="${cfg%.cfg}.tla"
    if [ -f "$tla" ]; then
        TOTAL=$((TOTAL + 1))
    fi
done < <(find "$EXAMPLES_DIR" -name "*.cfg" -type f | sort)

echo "Found $TOTAL spec/config pairs"
echo ""

process_spec() {
    local tla="$1"
    local cfg="$2"
    local rel_path="${tla#$EXAMPLES_DIR/}"
    local spec_name=$(basename "$tla" .tla)

    local tla2_states="-"
    local tlc_states="-"
    local tla2_time="-"
    local tlc_time="-"
    local match="SKIP"
    local error=""

    # Run TLA2 with timeout
    local tla2_start=$(date +%s.%N)
    local tla2_out=$(timeout "${TIMEOUT}s" "$TLA2" check "$tla" --config "$cfg" --workers 1 2>&1) && tla2_rc=$? || tla2_rc=$?
    local tla2_end=$(date +%s.%N)

    if [ $tla2_rc -eq 124 ]; then
        error="TLA2 timeout"
    elif [ $tla2_rc -ne 0 ]; then
        error="TLA2 exit $tla2_rc"
    else
        tla2_states=$(echo "$tla2_out" | grep -oE "States found: [0-9,]+" | tr -d ',' | grep -oE "[0-9]+" || echo "-")
        tla2_time=$(echo "$tla2_end - $tla2_start" | bc 2>/dev/null || echo "-")
    fi

    # Run TLC with timeout (only if TLA2 succeeded)
    if [ -z "$error" ]; then
        local tlc_meta_spec=$(mktemp -d)
        local tlc_start=$(date +%s.%N)
        local tlc_out=$(timeout "${TIMEOUT}s" java -cp "$TLC_CP" tlc2.TLC \
            -metadir "$tlc_meta_spec" \
            -teSpecOutDir "$tlc_meta_spec" \
            -deadlock \
            -config "$cfg" \
            "$tla" 2>&1) && tlc_rc=$? || tlc_rc=$?
        local tlc_end=$(date +%s.%N)
        rm -rf "$tlc_meta_spec"

        if [ $tlc_rc -eq 124 ]; then
            error="TLC timeout"
        elif [ $tlc_rc -eq 13 ]; then
            # TLC exit 13 = successful completion with liveness check
            tlc_states=$(echo "$tlc_out" | grep -oE "[0-9,]+ distinct states found" | tail -1 | tr -d ',' | grep -oE "^[0-9]+" || echo "-")
            tlc_time=$(echo "$tlc_end - $tlc_start" | bc 2>/dev/null || echo "-")
        elif [ $tlc_rc -ne 0 ]; then
            # Try to get states even on non-zero exit (might be safety violation)
            tlc_states=$(echo "$tlc_out" | grep -oE "[0-9,]+ distinct states found" | tail -1 | tr -d ',' | grep -oE "^[0-9]+" || echo "-")
            if [ "$tlc_states" = "-" ]; then
                error="TLC exit $tlc_rc"
            else
                tlc_time=$(echo "$tlc_end - $tlc_start" | bc 2>/dev/null || echo "-")
            fi
        else
            tlc_states=$(echo "$tlc_out" | grep -oE "[0-9,]+ distinct states found" | tail -1 | tr -d ',' | grep -oE "^[0-9]+" || echo "-")
            tlc_time=$(echo "$tlc_end - $tlc_start" | bc 2>/dev/null || echo "-")
        fi
    fi

    # Compare results
    if [ -n "$error" ]; then
        match="ERROR"
    elif [ "$tla2_states" = "-" ] || [ "$tlc_states" = "-" ]; then
        match="SKIP"
    elif [ "$tla2_states" = "$tlc_states" ]; then
        match="YES"
    else
        match="NO"
    fi

    # Output result
    echo "$spec_name,$cfg,$tla2_states,$tlc_states,$tla2_time,$tlc_time,$match,$error" >> "$CSV_FILE"

    case "$match" in
        YES)
            echo "[ PASS ] $rel_path: $tla2_states states (TLA2) = $tlc_states (TLC)"
            return 0
            ;;
        NO)
            echo "[ FAIL ] $rel_path: $tla2_states (TLA2) != $tlc_states (TLC)"
            return 1
            ;;
        ERROR)
            echo "[ERROR ] $rel_path: $error"
            return 2
            ;;
        *)
            echo "[ SKIP ] $rel_path"
            return 3
            ;;
    esac
}

# Process each spec
find "$EXAMPLES_DIR" -name "*.cfg" -type f | sort | while read cfg; do
    tla="${cfg%.cfg}.tla"
    if [ -f "$tla" ]; then
        rel_cfg="${cfg#$EXAMPLES_DIR/}"

        process_spec "$tla" "$cfg"
        rc=$?

        case $rc in
            0) echo "PASS" >> "$CSV_FILE.counts" ;;
            1) echo "FAIL" >> "$CSV_FILE.counts" ;;
            2) echo "ERROR" >> "$CSV_FILE.counts" ;;
            3) echo "SKIP" >> "$CSV_FILE.counts" ;;
        esac
    fi
done

# Count results
PASS=$(grep -c "^PASS$" "$CSV_FILE.counts" 2>/dev/null || echo 0)
FAIL=$(grep -c "^FAIL$" "$CSV_FILE.counts" 2>/dev/null || echo 0)
ERROR=$(grep -c "^ERROR$" "$CSV_FILE.counts" 2>/dev/null || echo 0)
SKIP=$(grep -c "^SKIP$" "$CSV_FILE.counts" 2>/dev/null || echo 0)
rm -f "$CSV_FILE.counts"

echo ""
echo "=== Summary ==="
echo "Total specs: $TOTAL"
echo "TLC Match (PASS): $PASS"
echo "TLC Mismatch (FAIL): $FAIL"
echo "Errors/Timeouts: $ERROR"
echo "Skipped: $SKIP"

# Generate markdown report
cat > "$REPORT_FILE" << EOF
# TLA2 vs TLC Comparison Report

**Date:** $DATE
**Test Set:** tlaplus/Examples repository
**Timeout:** ${TIMEOUT}s per spec

## Summary

| Metric | Count |
|--------|-------|
| Total specs | $TOTAL |
| TLC Match (PASS) | $PASS |
| TLC Mismatch (FAIL) | $FAIL |
| Errors/Timeouts | $ERROR |
| Skipped | $SKIP |

## Detailed Results

See \`tlc_comparison_$DATE.csv\` for full results.

### Matching Specs (TLA2 = TLC)

EOF

# Add matching specs
grep ",YES," "$CSV_FILE" | while IFS=',' read spec cfg t2s tlcs t2t tlct match err; do
    echo "- \`$spec\`: $t2s states" >> "$REPORT_FILE"
done

cat >> "$REPORT_FILE" << EOF

### Mismatched Specs (TLA2 != TLC)

EOF

# Add mismatched specs
grep ",NO," "$CSV_FILE" | while IFS=',' read spec cfg t2s tlcs t2t tlct match err; do
    echo "- \`$spec\`: TLA2=$t2s, TLC=$tlcs" >> "$REPORT_FILE"
done

cat >> "$REPORT_FILE" << EOF

### Errors/Timeouts

EOF

# Add error specs
grep ",ERROR," "$CSV_FILE" | while IFS=',' read spec cfg t2s tlcs t2t tlct match err; do
    echo "- \`$spec\`: $err" >> "$REPORT_FILE"
done

cat >> "$REPORT_FILE" << EOF

---

*Generated by scripts/mass_tlc_compare.sh*
EOF

echo ""
echo "Reports written to:"
echo "  $REPORT_FILE"
echo "  $CSV_FILE"

# Return appropriate exit code
if [ "$FAIL" -gt 0 ]; then
    exit 1
else
    exit 0
fi
