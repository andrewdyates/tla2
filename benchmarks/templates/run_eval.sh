#!/usr/bin/env bash
# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# run_eval.sh - Standardized benchmark evaluation runner
#
# TEMPLATE USAGE:
# 1. Copy to your project's benchmarks/ directory
# 2. Implement run_evaluation() function for your benchmark suite
# 3. Update BENCHMARK_NAME and default configurations
#
# Usage:
#   ./benchmarks/run_eval.sh --run-id myrun --timeout 60
#   ./benchmarks/run_eval.sh --list-suites
#   ./benchmarks/run_eval.sh --suite extra-small

set -euo pipefail
trap '' PIPE  # Ignore SIGPIPE from early-exit pipe consumers (#4432)

# ═══════════════════════════════════════════════════════════════════════════════
# Configuration - CUSTOMIZE THESE FOR YOUR PROJECT
# ═══════════════════════════════════════════════════════════════════════════════

BENCHMARK_NAME="${BENCHMARK_NAME:-project-bench}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Default directories (SWE-bench compatible structure)
LOGS_DIR="${LOGS_DIR:-$SCRIPT_DIR/logs}"
RESULTS_DIR="${RESULTS_DIR:-$SCRIPT_DIR/results}"
DATA_DIR="${DATA_DIR:-$SCRIPT_DIR/data}"

# Default settings
DEFAULT_TIMEOUT=300
DEFAULT_WORKERS=4
DEFAULT_SUITE="default"

# ═══════════════════════════════════════════════════════════════════════════════
# Logging
# ═══════════════════════════════════════════════════════════════════════════════

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log_info() { echo -e "${BLUE}[INFO]${NC} $1"; }
log_ok() { echo -e "${GREEN}[OK]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1" >&2; }

# ═══════════════════════════════════════════════════════════════════════════════
# Argument parsing
# ═══════════════════════════════════════════════════════════════════════════════

RUN_ID="${RUN_ID:-$(date +%Y%m%d-%H%M%S)}"
TIMEOUT="${TIMEOUT:-$DEFAULT_TIMEOUT}"
MAX_WORKERS="${MAX_WORKERS:-$DEFAULT_WORKERS}"
SUITE="${SUITE:-$DEFAULT_SUITE}"
LIST_SUITES=false

# Sanitize RUN_ID to prevent path traversal and special char issues
RUN_ID="${RUN_ID//[^a-zA-Z0-9._-]/_}"

print_usage() {
    cat <<EOF
Usage: $0 [OPTIONS]

Run reproducible benchmark evaluations.

Options:
  --run-id ID       Unique identifier for this run (default: timestamp)
  --timeout SEC     Per-test timeout in seconds (default: $DEFAULT_TIMEOUT)
  --workers N       Maximum parallel workers (default: $DEFAULT_WORKERS)
  --suite NAME      Benchmark suite to run (default: $DEFAULT_SUITE)
  --list-suites     List available benchmark suites
  -h, --help        Show this help message

Environment variables:
  RUN_ID            Same as --run-id
  TIMEOUT           Same as --timeout
  MAX_WORKERS       Same as --workers
  SUITE             Same as --suite
  LOGS_DIR          Override logs directory
  RESULTS_DIR       Override results directory
  DATA_DIR          Override data directory

Output structure:
  logs/run_evaluation/<run_id>/   Evaluation logs
  logs/build_images/              Docker build logs (if using containers)
  results/<run_id>/               Benchmark results JSON
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
    --run-id)
        [[ -z "${2:-}" ]] && {
            log_error "--run-id requires a value"
            exit 1
        }
        RUN_ID="$2"
        shift 2
        ;;
    --timeout)
        [[ -z "${2:-}" ]] && {
            log_error "--timeout requires a value"
            exit 1
        }
        TIMEOUT="$2"
        shift 2
        ;;
    --workers)
        [[ -z "${2:-}" ]] && {
            log_error "--workers requires a value"
            exit 1
        }
        MAX_WORKERS="$2"
        shift 2
        ;;
    --suite)
        [[ -z "${2:-}" ]] && {
            log_error "--suite requires a value"
            exit 1
        }
        SUITE="$2"
        shift 2
        ;;
    --list-suites)
        LIST_SUITES=true
        shift
        ;;
    -h | --help)
        print_usage
        exit 0
        ;;
    *)
        log_error "Unknown option: $1"
        print_usage
        exit 1
        ;;
    esac
done

# ═══════════════════════════════════════════════════════════════════════════════
# Suite definitions - CUSTOMIZE FOR YOUR PROJECT
# ═══════════════════════════════════════════════════════════════════════════════

list_suites() {
    cat <<EOF
Available benchmark suites:

  default       Standard test suite
  quick         Fast smoke tests
  full          Complete benchmark suite

Add your suites by editing the list_suites() and run_evaluation() functions.
EOF
}

if [[ "$LIST_SUITES" == "true" ]]; then
    list_suites
    exit 0
fi

# ═══════════════════════════════════════════════════════════════════════════════
# Setup
# ═══════════════════════════════════════════════════════════════════════════════

setup_directories() {
    mkdir -p "$LOGS_DIR/run_evaluation/$RUN_ID"
    mkdir -p "$LOGS_DIR/build_images"
    mkdir -p "$RESULTS_DIR/$RUN_ID"
}

log_metadata() {
    local metadata_file="$RESULTS_DIR/$RUN_ID/metadata.json"
    cat >"$metadata_file" <<EOF
{
    "benchmark_name": "$BENCHMARK_NAME",
    "run_id": "$RUN_ID",
    "suite": "$SUITE",
    "timeout": $TIMEOUT,
    "max_workers": $MAX_WORKERS,
    "started_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "commit": "$(git -C "$PROJECT_ROOT" rev-parse HEAD 2>/dev/null || echo "unknown")",
    "branch": "$(git -C "$PROJECT_ROOT" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")"
}
EOF
    log_info "Metadata written to $metadata_file"
}

# ═══════════════════════════════════════════════════════════════════════════════
# Evaluation runner - IMPLEMENT THIS FOR YOUR PROJECT
# ═══════════════════════════════════════════════════════════════════════════════

run_evaluation() {
    local suite="$1"
    local result_file="$RESULTS_DIR/$RUN_ID/results.json"
    # Log directory available for custom implementations:
    export EVAL_LOG_DIR="$LOGS_DIR/run_evaluation/$RUN_ID"

    log_info "Running suite: $suite"
    log_info "Timeout: ${TIMEOUT}s per test"
    log_info "Workers: $MAX_WORKERS"

    # ════════════════════════════════════════════════════════════════════════════
    # TEMPLATE: Replace this section with your evaluation logic
    # ════════════════════════════════════════════════════════════════════════════

    case "$suite" in
    default | quick | full)
        log_warn "This is a template - implement run_evaluation() for your project"
        log_info "Would run $suite suite with timeout=$TIMEOUT workers=$MAX_WORKERS"

        # Example result format
        cat >"$result_file" <<EOF
{
    "suite": "$suite",
    "passed": 0,
    "failed": 0,
    "skipped": 0,
    "total": 0,
    "duration_seconds": 0,
    "tests": []
}
EOF
        ;;
    *)
        log_error "Unknown suite: $suite"
        log_info "Run with --list-suites to see available options"
        exit 1
        ;;
    esac

    # ════════════════════════════════════════════════════════════════════════════

    log_ok "Results written to $result_file"
}

finalize_results() {
    local metadata_file="$RESULTS_DIR/$RUN_ID/metadata.json"
    local tmp_file
    tmp_file=$(mktemp)

    # Ensure tmp_file cleanup on exit
    trap 'rm -f "$tmp_file"' EXIT

    # Add completion timestamp
    if command -v jq &>/dev/null; then
        if jq --arg ts "$(date -u +%Y-%m-%dT%H:%M:%SZ)" '.completed_at = $ts' "$metadata_file" >"$tmp_file"; then
            mv "$tmp_file" "$metadata_file"
        fi
    fi

    log_ok "Evaluation complete"
    log_info "Logs: $LOGS_DIR/run_evaluation/$RUN_ID/"
    log_info "Results: $RESULTS_DIR/$RUN_ID/"
}

# ═══════════════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════════════

main() {
    log_info "═══════════════════════════════════════════════════════════════"
    log_info "  $BENCHMARK_NAME Evaluation"
    log_info "  Run ID: $RUN_ID"
    log_info "═══════════════════════════════════════════════════════════════"

    setup_directories
    log_metadata
    run_evaluation "$SUITE"
    finalize_results
}

main
