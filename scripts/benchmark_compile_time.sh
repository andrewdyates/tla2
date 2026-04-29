#!/bin/bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# CODEGEN COMPILE-TIME BENCHMARK
# Measures LLVM vs Cranelift backend compile times for generated Rust code.
#
# Usage:
#   ./scripts/benchmark_compile_time.sh [--runs N] [--output-dir DIR] [--with-timings]
#
# Output:
#   - metadata.json: environment and configuration
#   - results.json: timing measurements
#   - timing-llvm.ndjson: per-crate timings (LLVM, when --with-timings)
#   - timing-cranelift.ndjson: per-crate timings (Cranelift, when --with-timings)
#
# Part of #526, #403, #527

set -euo pipefail

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUNS=${RUNS:-3}
# Default OUTPUT_DIR uses absolute path to handle cd in run_timing
OUTPUT_DIR=${OUTPUT_DIR:-"$REPO_ROOT/benchmarks/results/compile-time-$(date +%Y%m%d-%H%M%S)"}
WITH_TIMINGS=${WITH_TIMINGS:-false}
SCRATCH_DIR=$(mktemp -d)
SNAPSHOT="crates/tla-codegen/tests/snapshots/integration__counter_codegen.snap"
RUNTIME_PATH="$REPO_ROOT/crates/tla-runtime"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --runs)
            RUNS="$2"
            shift 2
            ;;
        --output-dir)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --with-timings)
            WITH_TIMINGS=true
            shift
            ;;
        -h|--help)
            echo "Usage: $0 [--runs N] [--output-dir DIR] [--with-timings]"
            echo ""
            echo "Options:"
            echo "  --runs N        Number of runs per measurement (default: 3)"
            echo "  --output-dir    Directory for output files (default: benchmarks/results/...)"
            echo "  --with-timings  Capture per-crate cargo timings (NDJSON)"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Cleanup on exit
cleanup() {
    rm -rf "$SCRATCH_DIR"
}
trap cleanup EXIT

# Normalize OUTPUT_DIR to an absolute path (script `cd`s into a scratch dir).
if [[ "$OUTPUT_DIR" != /* ]]; then
    OUTPUT_DIR="$REPO_ROOT/$OUTPUT_DIR"
fi

echo "=== Codegen Compile-Time Benchmark ==="
echo "Runs per measurement: $RUNS"
echo "Output directory: $OUTPUT_DIR"
echo "Capture timings: $WITH_TIMINGS"
echo ""

# Basic validation
if ! [[ "$RUNS" =~ ^[0-9]+$ ]] || [ "$RUNS" -lt 1 ]; then
    echo "ERROR: --runs must be a positive integer (got: $RUNS)" >&2
    exit 1
fi

# Check prerequisites
if [ ! -f "$SNAPSHOT" ]; then
    echo "ERROR: Snapshot file not found: $SNAPSHOT"
    echo "Run 'cargo test -p tla-codegen' to generate it."
    exit 1
fi

if [ ! -d "$RUNTIME_PATH" ]; then
    echo "ERROR: tla-runtime not found at: $RUNTIME_PATH"
    exit 1
fi

# Check for timing parser script (used with --with-timings)
TIMING_PARSER="$REPO_ROOT/scripts/parse_cargo_timings_ndjson.py"
if [ "$WITH_TIMINGS" = true ] && [ ! -f "$TIMING_PARSER" ]; then
    echo "ERROR: Timing parser script not found at: $TIMING_PARSER"
    exit 1
fi

# Check for nightly with Cranelift component installed
HAVE_CRANELIFT=false
if rustup component list --toolchain nightly 2>/dev/null | grep -q 'rustc-codegen-cranelift.*installed'; then
    HAVE_CRANELIFT=true
fi

echo "Cranelift available: $HAVE_CRANELIFT"
echo ""

# Create scratch crate
echo "Setting up scratch crate..."
mkdir -p "$SCRATCH_DIR/codegen-bench/src"

# Extract generated code from snapshot (skip YAML header)
tail -n +5 "$SNAPSHOT" > "$SCRATCH_DIR/codegen-bench/src/counter.rs"

# Create lib.rs
cat > "$SCRATCH_DIR/codegen-bench/src/lib.rs" << 'EOF'
pub mod counter;

pub use counter::{Counter, CounterState};
EOF

# Create Cargo.toml
cat > "$SCRATCH_DIR/codegen-bench/Cargo.toml" << EOF
[package]
name = "codegen-bench"
version = "0.1.0"
edition = "2021"

[dependencies]
tla-runtime = { path = "$RUNTIME_PATH" }

[profile.release]
opt-level = 3
EOF

# Create Cranelift variant
if [ "$HAVE_CRANELIFT" = true ]; then
    mkdir -p "$SCRATCH_DIR/codegen-bench-cranelift/src"
    cp "$SCRATCH_DIR/codegen-bench/src/counter.rs" "$SCRATCH_DIR/codegen-bench-cranelift/src/"
    cp "$SCRATCH_DIR/codegen-bench/src/lib.rs" "$SCRATCH_DIR/codegen-bench-cranelift/src/"
    # Create Cargo.toml with cargo-features at top (required for codegen-backend)
    cat > "$SCRATCH_DIR/codegen-bench-cranelift/Cargo.toml" << EOF
cargo-features = ["codegen-backend"]

[package]
name = "codegen-bench-cranelift"
version = "0.1.0"
edition = "2021"

[dependencies]
tla-runtime = { path = "$RUNTIME_PATH" }

[profile.release]
opt-level = 3
codegen-backend = "cranelift"
EOF
fi

# Collect environment info
COMMIT=$(git -C "$REPO_ROOT" rev-parse --short HEAD 2>/dev/null || echo "unknown")
BRANCH=$(git -C "$REPO_ROOT" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")
OS=$(uname -s)
ARCH=$(uname -m)
OS_VERSION=$(uname -r)

# Get Rust toolchain versions
STABLE_RUSTC=$(rustc --version 2>/dev/null || echo "not installed")
STABLE_CARGO=$(cargo --version 2>/dev/null || echo "not installed")
NIGHTLY_RUSTC=$(rustup run nightly rustc --version 2>/dev/null || echo "not installed")
NIGHTLY_CARGO=$(rustup run nightly cargo --version 2>/dev/null || echo "not installed")

# Count lines of generated code
GEN_LINES=$(wc -l < "$SCRATCH_DIR/codegen-bench/src/counter.rs" | tr -d ' ')

echo "Environment:"
echo "  OS: $OS $OS_VERSION ($ARCH)"
echo "  Stable rustc: $STABLE_RUSTC"
echo "  Nightly rustc: $NIGHTLY_RUSTC"
echo "  Nightly cargo: $NIGHTLY_CARGO"
echo "  Generated code: $GEN_LINES lines"
echo ""

# Run timing function
# Args: $1=name $2=dir $3=toolchain $4=extra_flags $5=timings_output (optional)
run_timing() {
    local name="$1"
    local dir="$2"
    local toolchain="$3"
    local extra_flags="$4"
    local timings_output="$5"

    cd "$dir"

    local times=()

    for i in $(seq 1 $RUNS); do
        # Clean build
        cargo clean 2>/dev/null || true

        local start=$(python3 -c 'import time; print(time.time())')
        # Capture timings on first run only if output file is specified
        if [ "$i" -eq 1 ] && [ -n "$timings_output" ]; then
            if [ -n "$toolchain" ]; then
                if ! cargo +"$toolchain" build --release --timings=json -Z unstable-options $extra_flags 2>&1 | tee "$timings_output" | tail -1; then
                    echo "ERROR: cargo build failed while capturing timings: $name" >&2
                    return 1
                fi
            else
                if ! cargo build --release --timings=json -Z unstable-options 2>&1 | tee "$timings_output" | tail -1; then
                    echo "ERROR: cargo build failed while capturing timings: $name" >&2
                    return 1
                fi
            fi
            if [ ! -s "$timings_output" ]; then
                echo "ERROR: timings capture produced an empty file: $timings_output" >&2
                return 1
            fi
        elif [ -n "$toolchain" ]; then
            if ! cargo +"$toolchain" build --release $extra_flags 2>&1 | tail -1; then
                echo "ERROR: cargo build failed: $name" >&2
                return 1
            fi
        else
            if ! cargo build --release 2>&1 | tail -1; then
                echo "ERROR: cargo build failed: $name" >&2
                return 1
            fi
        fi
        local end=$(python3 -c 'import time; print(time.time())')

        local elapsed=$(python3 -c "print(f'{$end - $start:.3f}')")
        times+=("$elapsed")
    done

    # Calculate stats (convert to comma-separated for Python)
    local times_csv=$(IFS=,; echo "${times[*]}")
    local sum=$(python3 -c "print(sum([$times_csv]))")
    local mean=$(python3 -c "print(f'{$sum / $RUNS:.3f}')")
    local min=$(python3 -c "print(min([$times_csv]))")
    local max=$(python3 -c "print(max([$times_csv]))")

    echo "$name: mean=${mean}s min=${min}s max=${max}s (n=$RUNS)"

    # Return JSON fragment
    echo "{\"name\": \"$name\", \"mean\": $mean, \"min\": $min, \"max\": $max, \"runs\": $RUNS, \"samples\": [$times_csv]}"
}

# Run incremental timing function
# Args: $1=name $2=dir $3=toolchain $4=extra_flags
run_incremental_timing() {
    local name="$1"
    local dir="$2"
    local toolchain="$3"
    local extra_flags="$4"

    cd "$dir"

    # Initial build
    if [ -n "$toolchain" ]; then
        if ! cargo +"$toolchain" build --release $extra_flags 2>/dev/null; then
            echo "ERROR: initial cargo build failed: $name" >&2
            return 1
        fi
    else
        if ! cargo build --release 2>/dev/null; then
            echo "ERROR: initial cargo build failed: $name" >&2
            return 1
        fi
    fi

    local times=()

    for i in $(seq 1 $RUNS); do
        # Touch generated file
        touch src/counter.rs

        local start=$(python3 -c 'import time; print(time.time())')
        if [ -n "$toolchain" ]; then
            if ! cargo +"$toolchain" build --release $extra_flags 2>&1 | tail -1; then
                echo "ERROR: incremental cargo build failed: $name" >&2
                return 1
            fi
        else
            if ! cargo build --release 2>&1 | tail -1; then
                echo "ERROR: incremental cargo build failed: $name" >&2
                return 1
            fi
        fi
        local end=$(python3 -c 'import time; print(time.time())')

        local elapsed=$(python3 -c "print(f'{$end - $start:.3f}')")
        times+=("$elapsed")
    done

    # Calculate stats (convert to comma-separated for Python)
    local times_csv=$(IFS=,; echo "${times[*]}")
    local sum=$(python3 -c "print(sum([$times_csv]))")
    local mean=$(python3 -c "print(f'{$sum / $RUNS:.3f}')")
    local min=$(python3 -c "print(min([$times_csv]))")
    local max=$(python3 -c "print(max([$times_csv]))")

    echo "$name: mean=${mean}s min=${min}s max=${max}s (n=$RUNS)"

    # Return JSON fragment
    echo "{\"name\": \"$name\", \"mean\": $mean, \"min\": $min, \"max\": $max, \"runs\": $RUNS, \"samples\": [$times_csv]}"
}

# Run benchmarks
echo "Running benchmarks..."
echo ""

# Create output directory early (needed for timings files)
mkdir -p "$OUTPUT_DIR"
OUTPUT_DIR="$(cd "$OUTPUT_DIR" && pwd)"

# Capture start time for metadata
START_TIME=$(date -u +%Y-%m-%dT%H:%M:%SZ)

RESULTS=()

echo "=== Clean Build (LLVM/nightly) ==="
if [ "$WITH_TIMINGS" = true ]; then
    LLVM_TIMINGS_FILE="$OUTPUT_DIR/timing-llvm.ndjson"
else
    LLVM_TIMINGS_FILE=""
fi
LLVM_CLEAN=$(run_timing "llvm_clean" "$SCRATCH_DIR/codegen-bench" "nightly" "" "$LLVM_TIMINGS_FILE")
RESULTS+=("$LLVM_CLEAN")
echo ""

echo "=== Incremental Build (LLVM/nightly) ==="
LLVM_INC=$(run_incremental_timing "llvm_incremental" "$SCRATCH_DIR/codegen-bench" "nightly" "")
RESULTS+=("$LLVM_INC")
echo ""

if [ "$HAVE_CRANELIFT" = true ]; then
    echo "=== Clean Build (Cranelift/nightly) ==="
    # Backend is configured via Cargo.toml codegen-backend setting
    if [ "$WITH_TIMINGS" = true ]; then
        CRAN_TIMINGS_FILE="$OUTPUT_DIR/timing-cranelift.ndjson"
    else
        CRAN_TIMINGS_FILE=""
    fi
    CRAN_CLEAN=$(run_timing "cranelift_clean" "$SCRATCH_DIR/codegen-bench-cranelift" "nightly" "" "$CRAN_TIMINGS_FILE")
    RESULTS+=("$CRAN_CLEAN")
    echo ""

    echo "=== Incremental Build (Cranelift/nightly) ==="
    CRAN_INC=$(run_incremental_timing "cranelift_incremental" "$SCRATCH_DIR/codegen-bench-cranelift" "nightly" "")
    RESULTS+=("$CRAN_INC")
    echo ""
else
    echo "Skipping Cranelift benchmarks (not installed)"
    echo "To install: rustup component add rustc-codegen-cranelift --toolchain nightly"
    echo ""
fi

# Write metadata.json
cat > "$OUTPUT_DIR/metadata.json" << EOF
{
    "benchmark_name": "codegen-compile-time",
    "run_id": "$(basename "$OUTPUT_DIR")",
    "runs_per_measurement": $RUNS,
    "started_at": "$START_TIME",
    "completed_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "commit": "$COMMIT",
    "branch": "$BRANCH",
    "environment": {
        "os": "$OS",
        "os_version": "$OS_VERSION",
        "arch": "$ARCH",
        "stable_rustc": "$STABLE_RUSTC",
        "stable_cargo": "$STABLE_CARGO",
        "nightly_rustc": "$NIGHTLY_RUSTC",
        "nightly_cargo": "$NIGHTLY_CARGO",
        "cranelift_available": $HAVE_CRANELIFT
    },
    "spec": {
        "name": "Counter",
        "generated_lines": $GEN_LINES,
        "source": "$SNAPSHOT"
    },
    "commands": {
        "llvm_clean": "cargo +nightly build --release",
        "llvm_incremental": "touch src/counter.rs && cargo +nightly build --release",
        "cranelift_clean": "cargo +nightly build --release (with Cargo.toml codegen-backend=cranelift)",
        "cranelift_incremental": "touch src/counter.rs && cargo +nightly build --release (with Cargo.toml codegen-backend=cranelift)"
    },
    "timings_captured": $WITH_TIMINGS
}
EOF

# Write results.json
# Parse JSON results back
echo "[" > "$OUTPUT_DIR/results.json"
first=true
for result in "${RESULTS[@]}"; do
    # Extract the JSON line (second line of output)
    json_line=$(echo "$result" | tail -1)
    if [ "$first" = true ]; then
        first=false
    else
        echo "," >> "$OUTPUT_DIR/results.json"
    fi
    echo "  $json_line" >> "$OUTPUT_DIR/results.json"
done
echo "]" >> "$OUTPUT_DIR/results.json"

echo "=== Summary ==="
echo "Results written to: $OUTPUT_DIR"
echo ""
echo "Files:"
echo "  - metadata.json: environment and configuration"
echo "  - results.json: timing measurements"
if [ "$WITH_TIMINGS" = true ]; then
    echo "  - timing-llvm.ndjson: per-crate timings (LLVM)"
    if [ "$HAVE_CRANELIFT" = true ]; then
        echo "  - timing-cranelift.ndjson: per-crate timings (Cranelift)"
    fi
fi
echo ""

# Print summary table from results.json
echo "| Benchmark | Mean | Min | Max |"
echo "|-----------|------|-----|-----|"
python3 -c "
import json
with open('$OUTPUT_DIR/results.json') as f:
    results = json.load(f)
for r in results:
    print(f\"| {r['name']} | {r['mean']}s | {r['min']}s | {r['max']}s |\")"

# Parse and display top-N slowest crates from timings
if [ "$WITH_TIMINGS" = true ]; then
    echo ""
    echo "=== Top 5 Slowest Crates (LLVM) ==="
    if [ -f "$OUTPUT_DIR/timing-llvm.ndjson" ]; then
        python3 "$TIMING_PARSER" "$OUTPUT_DIR/timing-llvm.ndjson" --top 5
    else
        echo "(no timing data)"
    fi

    if [ "$HAVE_CRANELIFT" = true ] && [ -f "$OUTPUT_DIR/timing-cranelift.ndjson" ]; then
        echo ""
        echo "=== Top 5 Slowest Crates (Cranelift) ==="
        python3 "$TIMING_PARSER" "$OUTPUT_DIR/timing-cranelift.ndjson" --top 5
    elif [ "$HAVE_CRANELIFT" = true ]; then
        echo ""
        echo "=== Top 5 Slowest Crates (Cranelift) ==="
        echo "(no timing data)"
    fi
fi

echo ""
echo "Done."
