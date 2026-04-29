#!/usr/bin/env bash
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DEFAULT_POLICY_FILE="$REPO_ROOT/tests/tlc_comparison/single_thread_supremacy_gate.json"
POLICY_FILE="$DEFAULT_POLICY_FILE"
BENCHMARK_SCRIPT="$REPO_ROOT/scripts/benchmark_single_thread_backends_vs_tlc.py"
source "$SCRIPT_DIR/canary_gate_common.sh"

MODE="enforce"
GATE_MODE="${TLA2_SINGLE_THREAD_SUPREMACY_GATE_MODE:-}"
if [[ "${TLA2_SINGLE_THREAD_SUPREMACY_RUNS+x}" == "x" ]]; then
    RUNS="$TLA2_SINGLE_THREAD_SUPREMACY_RUNS"
    RUNS_SOURCE="TLA2_SINGLE_THREAD_SUPREMACY_RUNS"
else
    RUNS="3"
    RUNS_SOURCE="default"
fi
TLA2_BIN="${TLA2_SINGLE_THREAD_SUPREMACY_TLA2_BIN:-}"
OUTPUT_DIR=""
LLVM2_ENV_OVERRIDES=()

require_arg() {
    local option="$1"
    if [[ $# -lt 2 || -z "${2:-}" || "${2:-}" == --* ]]; then
        echo "Error: $option requires an argument" >&2
        exit 1
    fi
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --mode)
            require_arg "$@"
            MODE="$2"
            shift 2
            ;;
        --runs)
            require_arg "$@"
            RUNS="$2"
            RUNS_SOURCE="--runs"
            shift 2
            ;;
        --gate-mode)
            require_arg "$@"
            GATE_MODE="$2"
            shift 2
            ;;
        --output-dir)
            require_arg "$@"
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --tla2-bin)
            require_arg "$@"
            TLA2_BIN="$2"
            shift 2
            ;;
        --llvm2-env)
            require_arg "$@"
            if [[ "$2" != *=* || "$2" == =* ]]; then
                echo "Error: --llvm2-env expects KEY=VALUE" >&2
                exit 1
            fi
            LLVM2_ENV_OVERRIDES+=(--llvm2-env "$2")
            shift 2
            ;;
        -h|--help)
            cat <<'EOF'
Usage: scripts/check_single_thread_supremacy_gate.sh [--mode warn|enforce] [--gate-mode MODE] [--runs N] [--output-dir DIR] [--tla2-bin PATH] [--llvm2-env KEY=VALUE]

Environment:
  TLA2_SINGLE_THREAD_SUPREMACY_SKIP=1  Skip the gate in warn mode only
  TLA2_SINGLE_THREAD_SUPREMACY_GATE_MODE Explicit policy gate mode outside enforce
  TLA2_SINGLE_THREAD_SUPREMACY_RUNS     Default run count (default: 3)
  TLA2_SINGLE_THREAD_SUPREMACY_TLA2_BIN Reuse an already-built tla2 binary

Options:
  --llvm2-env KEY=VALUE                 Additional LLVM2 env override; may be repeated and overrides defaults.
                                        In enforce/full_native_fused mode, required gate env keys may
                                        only be repeated with the exact required value.
EOF
            exit 0
            ;;
        *)
            echo "Unknown argument: $1" >&2
            exit 1
            ;;
    esac
done

if [[ "$MODE" != "warn" && "$MODE" != "enforce" ]]; then
    echo "Error: --mode must be 'warn' or 'enforce'" >&2
    exit 1
fi

if [[ "$MODE" == "enforce" && "${TLA2_SINGLE_THREAD_SUPREMACY_POLICY_FILE+x}" == "x" ]]; then
    echo "Error: TLA2_SINGLE_THREAD_SUPREMACY_POLICY_FILE is not allowed in enforce mode" >&2
    exit 1
fi

if [[ "$MODE" != "enforce" && "${TLA2_SINGLE_THREAD_SUPREMACY_POLICY_FILE+x}" == "x" ]]; then
    POLICY_FILE="$TLA2_SINGLE_THREAD_SUPREMACY_POLICY_FILE"
fi

if [[ "${TLA2_SINGLE_THREAD_SUPREMACY_SKIP:-}" == "1" ]]; then
    if [[ "$MODE" == "enforce" ]]; then
        echo "Error: TLA2_SINGLE_THREAD_SUPREMACY_SKIP is not allowed in enforce mode" >&2
        exit 1
    fi
    exit 0
fi

if [[ ! "$RUNS" =~ ^[0-9]+$ ]]; then
    echo "Error: $RUNS_SOURCE must be a non-negative integer" >&2
    exit 1
fi

if [[ "$MODE" == "enforce" && "$RUNS" -lt 3 ]]; then
    if [[ "$RUNS_SOURCE" == "TLA2_SINGLE_THREAD_SUPREMACY_RUNS" ]]; then
        echo "Error: TLA2_SINGLE_THREAD_SUPREMACY_RUNS must be at least 3 in enforce mode" >&2
    else
        echo "Error: --runs must be at least 3 in enforce mode" >&2
    fi
    exit 1
fi

if [[ ! -f "$POLICY_FILE" ]]; then
    echo "Error: policy file not found: $POLICY_FILE" >&2
    exit 1
fi

if [[ ! -f "$BENCHMARK_SCRIPT" ]]; then
    echo "Error: benchmark script not found: $BENCHMARK_SCRIPT" >&2
    exit 1
fi

POLICY_SPECS=()
while IFS= read -r spec; do
    POLICY_SPECS+=("$spec")
done < <(python3 - "$POLICY_FILE" <<'PY'
import json
import sys

policy = json.load(open(sys.argv[1], encoding="utf-8"))
for spec in policy.get("specs", []):
    print(spec)
PY
)

if [[ ${#POLICY_SPECS[@]} -eq 0 ]]; then
    echo "Error: no specs configured in policy file: $POLICY_FILE" >&2
    exit 1
fi

POLICY_GATE_CONFIG="$(python3 - "$POLICY_FILE" "$GATE_MODE" "$MODE" <<'PY'
import json
import sys
from pathlib import Path

policy = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
requested = sys.argv[2]
run_mode = sys.argv[3]
modes = policy.get("gate_modes") or {}

def string_list(value, path):
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item for item in value
    ):
        raise SystemExit(
            f"Error: policy {path} must be a list of non-empty strings"
        )
    return value

if modes:
    if run_mode == "enforce":
        mode_name = policy.get("final_gate_mode") or policy.get("default_gate_mode")
    elif requested:
        mode_name = requested
    else:
        available = ", ".join(sorted(modes))
        raise SystemExit(
            "Error: --gate-mode is required outside --mode enforce; "
            f"available: {available}"
        )
    if not mode_name:
        raise SystemExit("Error: policy has gate_modes but no final_gate_mode")
    mode = modes.get(mode_name)
    if mode is None:
        available = ", ".join(sorted(modes))
        raise SystemExit(f"Error: unknown gate mode {mode_name!r}; available: {available}")
    flags = string_list(
        mode.get("benchmark_flags", []),
        f"gate_modes.{mode_name}.benchmark_flags",
    )
    string_list(
        mode.get("forbidden_benchmark_flags", []),
        f"gate_modes.{mode_name}.forbidden_benchmark_flags",
    )
    string_list(
        mode.get("required_llvm2_compilation_total_matches", []),
        f"gate_modes.{mode_name}.required_llvm2_compilation_total_matches",
    )
else:
    mode_name = requested or "legacy"
    flags = string_list(
        policy.get("required_llvm2_gate_flags", []),
        "required_llvm2_gate_flags",
    )

if not flags:
    raise SystemExit(f"Error: no benchmark flags configured for gate mode {mode_name!r}")

print(mode_name)
for flag in flags:
    print("--" + flag.replace("_", "-"))
PY
)" || exit 1

POLICY_GATE_LINES=()
while IFS= read -r line; do
    POLICY_GATE_LINES+=("$line")
done <<< "$POLICY_GATE_CONFIG"
GATE_MODE="${POLICY_GATE_LINES[0]}"
LLVM2_TRUTH_FLAGS=("${POLICY_GATE_LINES[@]:1}")

required_full_native_fused_llvm2_env_value() {
    case "$1" in
        TLA2_LLVM2|TLA2_LLVM2_BFS|TLA2_LLVM2_EXISTS|TLA2_COMPILED_BFS|TLA2_FLAT_BFS|TLA2_BYTECODE_VM|TLA2_BYTECODE_VM_STATS|TLA2_LLVM2_NATIVE_FUSED_STRICT|TLA2_DISABLE_ARTIFACT_CACHE|TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP)
            printf '1\n'
            return 0
            ;;
        TLA2_AUTO_POR)
            printf '0\n'
            return 0
            ;;
        TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST)
            printf 'strict\n'
            return 0
            ;;
        TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL|TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL)
            printf 'O3\n'
            return 0
            ;;
        TLA2_LLVM2_DISABLE_POST_RA_OPT)
            printf '0\n'
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

if [[ "$MODE" == "enforce" && "$GATE_MODE" == "full_native_fused" ]]; then
    for ((i = 1; i < ${#LLVM2_ENV_OVERRIDES[@]}; i += 2)); do
        env_override="${LLVM2_ENV_OVERRIDES[$i]}"
        env_key="${env_override%%=*}"
        env_value="${env_override#*=}"
        if required_env_value="$(required_full_native_fused_llvm2_env_value "$env_key")"; then
            if [[ "$env_value" != "$required_env_value" ]]; then
                echo "Error: enforce/full_native_fused requires $env_key=$required_env_value; --llvm2-env supplied $env_override" >&2
                exit 1
            fi
        fi
    done
fi

TARGET_DIR="$(resolve_canary_target_dir "$REPO_ROOT")"
if [[ -z "$OUTPUT_DIR" ]]; then
    OUTPUT_DIR="$REPO_ROOT/reports/perf/$(date +%Y-%m-%dT%H%M%S)/single-thread-supremacy-gate"
fi
mkdir -p "$OUTPUT_DIR"
(uptime || true) > "$OUTPUT_DIR/loadavg.txt"

while IFS='=' read -r key _; do
    if [[ "$key" == TLA2_* ]]; then
        unset "$key"
    fi
done < <(env)

bench_exit=0
BENCHMARK_ARGS=(
    --runs "$RUNS" \
    --output-dir "$OUTPUT_DIR" \
    --target-dir "$TARGET_DIR" \
    --interp-env TLA2_LLVM2=0 \
    --interp-env TLA2_LLVM2_BFS=0 \
    --interp-env TLA2_BYTECODE_VM=1 \
    --interp-env TLA2_AUTO_POR=0 \
    --llvm2-env TLA2_LLVM2=1 \
    --llvm2-env TLA2_LLVM2_BFS=1 \
    --llvm2-env TLA2_LLVM2_EXISTS=1 \
    --llvm2-env TLA2_COMPILED_BFS=1 \
    --llvm2-env TLA2_FLAT_BFS=1 \
    --llvm2-env TLA2_BYTECODE_VM=1 \
    --llvm2-env TLA2_BYTECODE_VM_STATS=1 \
    --llvm2-env TLA2_AUTO_POR=0 \
    --llvm2-env "TLA2_CACHE_DIR=$OUTPUT_DIR/llvm2-artifact-cache"
)
if [[ "$GATE_MODE" == "full_native_fused" ]]; then
    BENCHMARK_ARGS+=(
        --llvm2-env TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST=strict
        --llvm2-env TLA2_LLVM2_NATIVE_FUSED_STRICT=1
        --llvm2-env TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL=O3
        --llvm2-env TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL=O3
        --llvm2-env TLA2_LLVM2_DISABLE_POST_RA_OPT=0
        --llvm2-env TLA2_DISABLE_ARTIFACT_CACHE=1
        --llvm2-env TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP=1
    )
fi
if [[ ${#LLVM2_ENV_OVERRIDES[@]} -gt 0 ]]; then
    BENCHMARK_ARGS+=("${LLVM2_ENV_OVERRIDES[@]}")
fi
BENCHMARK_ARGS+=("${LLVM2_TRUTH_FLAGS[@]}" --specs "${POLICY_SPECS[@]}")
if [[ -n "$TLA2_BIN" ]]; then
    BENCHMARK_ARGS+=(--tla2-bin "$TLA2_BIN")
fi

python3 "$BENCHMARK_SCRIPT" "${BENCHMARK_ARGS[@]}" || bench_exit=$?

if [[ $bench_exit -ne 0 ]]; then
    if [[ "$MODE" == "enforce" ]]; then
        echo "[single-thread-supremacy] FAIL: benchmark run failed." >&2
        exit 1
    fi
    echo "[single-thread-supremacy] WARNING: benchmark run failed." >&2
    exit 0
fi

SUMMARY_JSON="$OUTPUT_DIR/summary.json"
if [[ ! -f "$SUMMARY_JSON" ]]; then
    if [[ "$MODE" == "enforce" ]]; then
        echo "[single-thread-supremacy] FAIL: summary not found: $SUMMARY_JSON" >&2
        exit 1
    fi
    echo "[single-thread-supremacy] WARNING: summary not found: $SUMMARY_JSON" >&2
    exit 0
fi

gate_exit=0
python3 - "$POLICY_FILE" "$SUMMARY_JSON" "$GATE_MODE" "$RUNS" <<'PY' || gate_exit=$?
import json
import math
import re
import statistics
import sys
from pathlib import Path

policy_path = Path(sys.argv[1])
summary_path = Path(sys.argv[2])
gate_mode = sys.argv[3]
expected_run_count = int(sys.argv[4])
policy = json.loads(policy_path.read_text(encoding="utf-8"))
summary = json.loads(summary_path.read_text(encoding="utf-8"))

rows = {row["spec"]: row for row in summary["rows"]}
errors = []
expected_state_counts = policy.get("expected_state_counts", {})
expected_generated_state_counts = policy.get("expected_generated_state_counts", {})
repo_root = policy_path.parent.parent.parent
FLAT_PRIMARY_REBUILD_MARKER = (
    "[compiled-bfs] clearing layout-sensitive compiled artifacts before rebuild: "
    "reason=flat_state_primary layout promotion"
)
STRICT_SELFTEST_FALSE_RESULT_KINDS = {"invariant", "state_constraint"}
SELFTEST_KEY_VALUE_REGEX = re.compile(
    r"(?<!\S)([A-Za-z_][A-Za-z0-9_]*)=([^,\s]+)"
)
SELFTEST_LEADING_KIND_REGEX = re.compile(
    r"^\s*\[llvm2-selftest\]\s+(?P<kind>[A-Za-z_][A-Za-z0-9_]*)\s+callout\b"
)


def policy_string_list(value, path):
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item for item in value
    ):
        errors.append(f"policy {path} must be a list of non-empty strings")
        return []
    return value


def policy_string_map(value, path):
    if not isinstance(value, dict) or any(
        not isinstance(key, str)
        or not key
        or not isinstance(item, str)
        or not item
        for key, item in value.items()
    ):
        errors.append(
            f"policy {path} must be an object with non-empty string keys and values"
        )
        return {}
    return value


def median_or_none(values):
    if not values:
        return None
    return float(statistics.median(values))


def run_elapsed_seconds(spec, mode_name, mode):
    values = []
    for run in mode.get("runs") or []:
        returncode = run.get("returncode")
        if returncode != 0 or isinstance(returncode, bool):
            continue
        elapsed = run.get("elapsed_seconds")
        if (
            not isinstance(elapsed, (int, float))
            or isinstance(elapsed, bool)
            or not math.isfinite(elapsed)
            or elapsed < 0
        ):
            errors.append(
                f"{spec}: {mode_name} run {run.get('run_index')}: elapsed_seconds "
                f"was {elapsed!r}, expected a non-negative finite number"
            )
            continue
        values.append(float(elapsed))
    return values


def recomputed_median(spec, mode_name, mode):
    values = run_elapsed_seconds(spec, mode_name, mode)
    median = median_or_none(values)
    advertised = mode.get("median_seconds")
    if advertised is not None:
        if (
            not isinstance(advertised, (int, float))
            or isinstance(advertised, bool)
            or not math.isfinite(advertised)
        ):
            errors.append(
                f"{spec}: {mode_name} advertised median_seconds was {advertised!r}, "
                "expected a finite number or null"
            )
        elif median is None or not math.isclose(float(advertised), median, rel_tol=1e-9, abs_tol=1e-12):
            errors.append(
                f"{spec}: {mode_name} advertised median_seconds {advertised!r} "
                f"did not match recomputed median {median!r}"
            )
    return median


def speedup_from_medians(tlc_median, mode_median):
    if tlc_median is None or mode_median in (None, 0):
        return None
    return tlc_median / mode_median


def successful_runs(mode):
    return [
        run
        for run in mode.get("runs") or []
        if run.get("returncode") == 0 and not isinstance(run.get("returncode"), bool)
    ]


def require_successful_run_indexes(spec, mode_name, mode):
    runs = successful_runs(mode)
    indexes = []
    seen = set()
    for position, run in enumerate(runs, start=1):
        run_index = run.get("run_index")
        if not isinstance(run_index, int) or isinstance(run_index, bool):
            errors.append(
                f"{spec}: {mode_name} successful run at position {position}: "
                f"run_index was {run_index!r}, expected an integer"
            )
            continue
        if run_index in seen:
            errors.append(
                f"{spec}: {mode_name} successful run_index {run_index} "
                "was duplicated"
            )
            continue
        seen.add(run_index)
        indexes.append(run_index)
    expected_indexes = list(range(1, expected_run_count + 1))
    if indexes != expected_indexes:
        errors.append(
            f"{spec}: {mode_name} successful run_index values were {indexes!r}, "
            f"expected sequential {expected_indexes!r}"
        )


def generated_state_count_by_run_index(spec, mode_name, mode):
    generated_state_counts = {}
    source_field = "states_generated" if mode_name == "tlc" else "transitions"
    for run in successful_runs(mode):
        run_index = run.get("run_index")
        if not isinstance(run_index, int) or isinstance(run_index, bool):
            continue
        generated_state_count = run.get(source_field)
        if not isinstance(generated_state_count, int) or isinstance(generated_state_count, bool):
            errors.append(
                f"{spec}: {mode_name} run {run_index}: generated-state count "
                f"({source_field}) was {generated_state_count!r}, expected an integer"
            )
            continue
        generated_state_counts[run_index] = generated_state_count
    return generated_state_counts


def require_expected_generated_state_counts(spec, row, expected_generated_states):
    if not isinstance(expected_generated_states, int) or isinstance(expected_generated_states, bool) or expected_generated_states <= 0:
        errors.append(
            f"{spec}: invalid fixed expected generated-state count in policy: "
            f"{expected_generated_states!r}"
        )
        return
    by_mode = {
        mode_name: generated_state_count_by_run_index(spec, mode_name, row[mode_name])
        for mode_name in ("tlc", "interp", "llvm2")
    }
    for mode_name, generated_state_counts in by_mode.items():
        source_field = "states_generated" if mode_name == "tlc" else "transitions"
        for run_index in range(1, expected_run_count + 1):
            actual_generated_states = generated_state_counts.get(run_index)
            if actual_generated_states is None:
                errors.append(
                    f"{spec}: {mode_name} run {run_index}: generated-state count "
                    "was missing or invalid"
                )
                continue
            if actual_generated_states != expected_generated_states:
                errors.append(
                    f"{spec}: {mode_name} run {run_index}: generated-state count "
                    f"({source_field}) was {actual_generated_states!r}, "
                    f"expected fixed {expected_generated_states}"
                )


def positive_float(value):
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(value)
        and value > 0
    )


def positive_int(value):
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def compiled_bfs_execution_seconds(spec, run, require_timing):
    telemetry = run.get("llvm2_telemetry") or {}
    seconds = telemetry.get("compiled_bfs_execution_seconds")
    nanos = telemetry.get("compiled_bfs_execution_nanos")
    if positive_int(nanos):
        derived_seconds = nanos / 1_000_000_000.0
        if positive_float(seconds) and not math.isclose(
            float(seconds),
            derived_seconds,
            rel_tol=1e-6,
            abs_tol=1e-6,
        ):
            errors.append(
                f"{spec} llvm2 run {run.get('run_index')}: compiled BFS "
                "execution seconds/nanos mismatch "
                f"(compiled_bfs_execution_seconds={float(seconds)!r}, "
                f"compiled_bfs_execution_nanos={nanos!r}, "
                f"derived_seconds={derived_seconds!r})"
            )
        return derived_seconds
    if positive_float(seconds):
        return float(seconds)
    if require_timing:
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: compiled BFS execution "
            "timing telemetry was missing or non-positive "
            f"(compiled_bfs_execution_seconds={seconds!r}, "
            f"compiled_bfs_execution_nanos={nanos!r})"
        )
    return None


def recomputed_llvm2_execution_median(spec, mode, require_timing):
    values = []
    for run in mode.get("runs") or []:
        if run.get("returncode", 0) != 0:
            continue
        execution_seconds = compiled_bfs_execution_seconds(
            spec, run, require_timing
        )
        if execution_seconds is not None:
            values.append(execution_seconds)
    median = median_or_none(values)
    advertised = mode.get("execution_median_seconds")
    if advertised is None:
        if median is not None or require_timing:
            errors.append(
                f"{spec}: llvm2 advertised execution_median_seconds was "
                f"{advertised!r}, expected recomputed execution median {median!r}"
            )
    elif (
        not isinstance(advertised, (int, float))
        or isinstance(advertised, bool)
        or not math.isfinite(advertised)
    ):
        errors.append(
            f"{spec}: llvm2 advertised execution_median_seconds was "
            f"{advertised!r}, expected a finite number or null"
        )
    elif median is None or not math.isclose(float(advertised), median, rel_tol=1e-9, abs_tol=1e-12):
        errors.append(
            f"{spec}: llvm2 advertised execution_median_seconds {advertised!r} "
            f"did not match recomputed execution median {median!r}"
        )
    return median


def require_advertised_speedup_match(spec, field, advertised, recomputed, required):
    if advertised is None:
        if recomputed is not None or required:
            errors.append(
                f"{spec}: advertised {field} was {advertised!r}, "
                f"expected recomputed speedup {recomputed!r}"
            )
    elif (
        not isinstance(advertised, (int, float))
        or isinstance(advertised, bool)
        or not math.isfinite(advertised)
    ):
        errors.append(
            f"{spec}: advertised {field} was {advertised!r}, "
            "expected a finite number or null"
        )
    elif recomputed is None or not math.isclose(float(advertised), recomputed, rel_tol=1e-9, abs_tol=1e-12):
        errors.append(
            f"{spec}: advertised {field} {advertised!r} did not match "
            f"recomputed speedup {recomputed!r}"
        )


def require_compilation_total_match(spec, run, telemetry, name):
    fields = {
        "actions": ("llvm2_actions_compiled", "llvm2_actions_total"),
        "invariants": ("llvm2_invariants_compiled", "llvm2_invariants_total"),
    }
    if name not in fields:
        errors.append(f"unknown LLVM2 compilation total policy check: {name!r}")
        return
    compiled_key, total_key = fields[name]
    compiled = telemetry.get(compiled_key)
    total = telemetry.get(total_key)
    if (
        not isinstance(total, int)
        or isinstance(total, bool)
        or total < 0
    ):
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: telemetry {total_key} "
            f"was {total!r}, expected a non-negative integer"
        )
        return
    if (
        not isinstance(compiled, int)
        or isinstance(compiled, bool)
        or compiled < 0
    ):
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: telemetry {compiled_key} "
            f"was {compiled!r}, expected {total_key} ({total!r})"
        )
        return
    if compiled != total:
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: telemetry {compiled_key} "
            f"was {compiled!r}, expected {total_key} ({total!r})"
        )


def require_llvm2_env_overrides(spec, run, required_env):
    if not required_env:
        return
    env_overrides = run.get("env_overrides")
    if not isinstance(env_overrides, dict):
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: env_overrides was "
            f"{env_overrides!r}, expected an object recording LLVM2 backend controls"
        )
        return
    for key, expected_value in sorted(required_env.items()):
        actual_value = env_overrides.get(key)
        if actual_value != expected_value:
            errors.append(
                f"{spec} llvm2 run {run.get('run_index')}: env_overrides[{key!r}] "
                f"was {actual_value!r}, expected {expected_value!r}"
            )


def artifact_dir_for(run):
    artifact_dir = run.get("artifact_dir")
    if not artifact_dir:
        return None
    path = Path(artifact_dir)
    if path.is_absolute():
        return path
    for candidate in (summary_path.parent / path, repo_root / path):
        if candidate.exists():
            return candidate
    return summary_path.parent / path


def read_run_artifact_text(spec, run):
    artifact_dir = artifact_dir_for(run)
    if artifact_dir is None:
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: missing artifact_dir "
            "for strict native callout selftest evidence"
        )
        return ""
    parts = []
    for name in ("stdout.txt", "stderr.txt"):
        path = artifact_dir / name
        if path.exists():
            parts.append(path.read_text(encoding="utf-8", errors="replace"))
    if not parts:
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: missing stdout.txt/stderr.txt "
            f"under artifact_dir {artifact_dir}"
        )
    return "\n".join(parts)


def latest_flat_primary_rebuild_segment(text):
    marker_index = text.rfind(FLAT_PRIMARY_REBUILD_MARKER)
    if marker_index == -1:
        return ""
    return text[marker_index:]


def parse_selftest_callout_result(line):
    if "[llvm2-selftest]" not in line or "status=" not in line or "value=" not in line:
        return None
    fields = {
        key: value.rstrip(",")
        for key, value in SELFTEST_KEY_VALUE_REGEX.findall(line)
    }
    kind = fields.get("kind")
    if kind is None:
        match = SELFTEST_LEADING_KIND_REGEX.search(line)
        if match:
            kind = match.group("kind")
    status = fields.get("status")
    raw_value = fields.get("value")
    if kind is None or status is None or raw_value is None:
        return None
    try:
        value = int(raw_value.replace(",", ""))
    except ValueError:
        return None
    return kind, status, value


def strict_selftest_false_result_failures(text):
    failures = []
    for line in text.splitlines():
        result = parse_selftest_callout_result(line)
        if result is None:
            continue
        kind, status, value = result
        if (
            kind in STRICT_SELFTEST_FALSE_RESULT_KINDS
            and status == "Ok"
            and value == 0
        ):
            failures.append(
                "native fused callout selftest reported false strict check: "
                f"kind={kind} status=Ok value=0 line={line!r}"
            )
    return failures


def require_strict_selftest_markers(spec, run, requirement):
    text = read_run_artifact_text(spec, run)
    evidence_text = latest_flat_primary_rebuild_segment(text)
    if not evidence_text:
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: missing post-rebuild "
            "flat-primary marker required for strict native callout selftest "
            f"evidence: {FLAT_PRIMARY_REBUILD_MARKER!r}"
        )
    actions = requirement["actions"]
    state_constraints = requirement["state_constraints"]
    invariants = requirement["invariants"]
    state_len = requirement.get("state_len")
    if state_len is not None and (
        not isinstance(state_len, int) or isinstance(state_len, bool) or state_len <= 0
    ):
        errors.append(
            f"{spec}: selftest state_len policy value was {state_len!r}, "
            "expected a positive integer"
        )
        state_len_pattern = r"\d+"
    else:
        state_len_pattern = str(state_len) if state_len is not None else r"\d+"
    patterns = (
        (
            "prepared native fused callout selftest",
            re.compile(
                r"\[llvm2-selftest\]\s+prepared native fused callout selftest:\s+"
                rf"actions={actions},\s+state_constraints={state_constraints},\s+"
                rf"invariants={invariants},\s+missing_expected=0,\s+"
                r"fail_closed=true\b"
            ),
        ),
        (
            "running native fused callout selftest on first real parent",
            re.compile(
                r"\[llvm2-selftest\]\s+running native fused callout selftest "
                rf"on first real parent:\s+state_len={state_len_pattern},\s+"
                rf"actions={actions},\s+state_constraints={state_constraints},\s+"
                rf"invariants={invariants},\s+fail_closed=true\b"
            ),
        ),
        (
            "native fused callout selftest complete",
            re.compile(r"\[llvm2-selftest\]\s+native fused callout selftest complete\b"),
        ),
    )
    for description, pattern in patterns:
        if not pattern.search(evidence_text):
            errors.append(
                f"{spec} llvm2 run {run.get('run_index')}: missing strict native "
                f"callout selftest marker: {description}"
            )
    for missing_expected in re.finditer(
        r"\[llvm2-selftest\]\s+prepared native fused callout selftest:.*?"
        r"missing_expected=(\d[\d,]*)\b",
        evidence_text,
    ):
        missing_expected_count = int(missing_expected.group(1).replace(",", ""))
        if missing_expected_count == 0:
            continue
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: strict native callout "
            "selftest reported missing expected callouts: "
            f"{missing_expected_count}"
        )
    for failure in strict_selftest_false_result_failures(evidence_text):
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: {failure}"
        )
    if re.search(
        r"\[llvm2-selftest\].*(native fused callout selftest failed|failing closed)",
        text,
    ):
        errors.append(
            f"{spec} llvm2 run {run.get('run_index')}: strict native callout "
            "selftest failure marker was present"
        )

modes = policy.get("gate_modes") or {}
if modes:
    mode = modes.get(gate_mode)
    if mode is None:
        errors.append(f"unknown policy gate mode: {gate_mode}")
        required_flags = []
        forbidden_flags = []
        required_llvm2_run_telemetry = {}
        required_llvm2_run_telemetry_by_spec = {}
        required_llvm2_selftest_by_spec = {}
        required_llvm2_env = {}
        require_generated_state_parity_by_run_index = False
        required_llvm2_compilation_total_matches = []
    else:
        required_flags = policy_string_list(
            mode.get("benchmark_flags", []),
            f"gate_modes.{gate_mode}.benchmark_flags",
        )
        forbidden_flags = policy_string_list(
            mode.get("forbidden_benchmark_flags", []),
            f"gate_modes.{gate_mode}.forbidden_benchmark_flags",
        )
        required_llvm2_run_telemetry = mode.get("required_llvm2_run_telemetry", {})
        required_llvm2_run_telemetry_by_spec = mode.get(
            "required_llvm2_run_telemetry_by_spec", {}
        )
        required_llvm2_selftest_by_spec = mode.get(
            "required_llvm2_selftest_by_spec", {}
        )
        required_llvm2_env = policy_string_map(
            mode.get("required_llvm2_env", {}),
            f"gate_modes.{gate_mode}.required_llvm2_env",
        )
        require_generated_state_parity_by_run_index = (
            mode.get("require_generated_state_parity_by_run_index") is True
        )
        required_llvm2_compilation_total_matches = policy_string_list(
            mode.get("required_llvm2_compilation_total_matches", []),
            f"gate_modes.{gate_mode}.required_llvm2_compilation_total_matches",
        )
else:
    required_flags = policy_string_list(
        policy.get("required_llvm2_gate_flags", []),
        "required_llvm2_gate_flags",
    )
    forbidden_flags = []
    required_llvm2_run_telemetry = {}
    required_llvm2_run_telemetry_by_spec = {}
    required_llvm2_selftest_by_spec = {}
    required_llvm2_env = {}
    require_generated_state_parity_by_run_index = False
    required_llvm2_compilation_total_matches = []

if not required_llvm2_compilation_total_matches:
    required_llvm2_compilation_total_matches = []
    if "require_llvm2_all_actions" in required_flags:
        required_llvm2_compilation_total_matches.append("actions")
    if "require_llvm2_compiled_invariants" in required_flags:
        required_llvm2_compilation_total_matches.append("invariants")

gate_flags = summary.get("gate_flags", {})
for flag in required_flags:
    if gate_flags.get(flag) is not True:
        errors.append(f"required benchmark flag was not enabled: {flag}")
for flag in forbidden_flags:
    forbidden_value = gate_flags.get(flag)
    if forbidden_value is not False:
        errors.append(f"forbidden benchmark flag was not disabled: {flag}")

for spec in policy["specs"]:
    row = rows.get(spec)
    if row is None:
        errors.append(f"{spec}: missing from summary")
        continue
    expected_states = expected_state_counts.get(spec)
    if expected_states is None:
        errors.append(f"{spec}: missing fixed expected state count in policy")
    elif (
        not isinstance(expected_states, int)
        or isinstance(expected_states, bool)
        or expected_states < 0
    ):
        errors.append(
            f"{spec}: invalid fixed expected state count in policy: {expected_states!r}"
        )

    if row["tlc"]["all_ok"] is not True:
        errors.append(f"{spec}: TLC run failed")
    if row["interp"]["all_ok"] is not True:
        errors.append(f"{spec}: interp run failed")
    if row["llvm2"]["all_ok"] is not True:
        errors.append(f"{spec}: llvm2 run failed")
    if row["parity_interp_vs_tlc"] is not True:
        errors.append(f"{spec}: interp parity drift vs TLC")
    if row["parity_llvm2_vs_tlc"] is not True:
        errors.append(f"{spec}: llvm2 parity drift vs TLC")
    for mode_name in ("tlc", "interp", "llvm2"):
        mode = row.get(mode_name, {})
        runs = mode.get("runs") or []
        if len(runs) != expected_run_count:
            errors.append(
                f"{spec}: {mode_name} had {len(runs)} runs in summary, "
                f"expected {expected_run_count}"
            )
        for run in runs:
            returncode = run.get("returncode")
            if returncode != 0 or isinstance(returncode, bool):
                errors.append(
                    f"{spec}: {mode_name} run {run.get('run_index')}: "
                    f"returncode was {returncode!r}, expected 0"
                )
            error = run.get("error")
            if error is not None:
                errors.append(
                    f"{spec}: {mode_name} run {run.get('run_index')}: "
                    f"error was {error!r}, expected null"
                )
            workers = run.get("workers")
            if workers != 1 or isinstance(workers, bool):
                errors.append(
                    f"{spec}: {mode_name} run {run.get('run_index')}: workers "
                    f"was {workers!r}, expected 1"
                )
        require_successful_run_indexes(spec, mode_name, mode)
    if require_generated_state_parity_by_run_index:
        require_expected_generated_state_counts(
            spec,
            row,
            expected_generated_state_counts.get(spec),
        )
    if expected_states is not None:
        for mode_name in ("tlc", "interp", "llvm2"):
            mode = row.get(mode_name, {})
            advertised_expected_states = mode.get("expected_states")
            if advertised_expected_states != expected_states:
                errors.append(
                    f"{spec}: {mode_name} advertised expected_states "
                    f"{advertised_expected_states!r}, expected fixed {expected_states}"
                )
            for run in mode.get("runs", []):
                actual_states = run.get("states_found")
                if actual_states != expected_states:
                    errors.append(
                        f"{spec}: {mode_name} run {run.get('run_index')}: "
                        f"states_found was {actual_states!r}, expected fixed "
                        f"{expected_states}"
                    )
    for failure in row.get("llvm2_gate_failures", []):
        errors.append(f"{spec}: {failure}")
    for run in row["llvm2"]["runs"]:
        telemetry = run.get("llvm2_telemetry") or {}
        require_llvm2_env_overrides(spec, run, required_llvm2_env)
        telemetry_requirements = dict(required_llvm2_run_telemetry)
        telemetry_requirements.update(
            required_llvm2_run_telemetry_by_spec.get(spec, {})
        )
        for key, expected in telemetry_requirements.items():
            if key == "transitions":
                actual = run.get("transitions")
            else:
                actual = telemetry.get(key)
            if expected == "all":
                expected_total = telemetry.get("llvm2_invariants_total")
                if (
                    isinstance(actual, int)
                    and not isinstance(actual, bool)
                    and isinstance(expected_total, int)
                    and not isinstance(expected_total, bool)
                    and expected_total >= 0
                    and actual == expected_total
                ):
                    continue
                errors.append(
                    f"{spec} llvm2 run {run['run_index']}: telemetry {key} "
                    f"was {actual!r}, expected all invariants ({expected_total!r})"
                )
                continue
            if expected == "positive":
                if isinstance(actual, int) and not isinstance(actual, bool) and actual > 0:
                    continue
                errors.append(
                    f"{spec} llvm2 run {run['run_index']}: telemetry {key} "
                    f"was {actual!r}, expected a positive integer"
                )
                continue
            if expected == "states_found":
                actual_states = run.get("states_found")
                if (
                    isinstance(actual, int)
                    and not isinstance(actual, bool)
                    and isinstance(actual_states, int)
                    and not isinstance(actual_states, bool)
                    and actual == actual_states
                ):
                    continue
                errors.append(
                    f"{spec} llvm2 run {run['run_index']}: telemetry {key} "
                    f"was {actual!r}, expected run states_found "
                    f"({actual_states!r})"
                )
                continue
            if expected == "transitions":
                actual_transitions = run.get("transitions")
                if (
                    isinstance(actual, int)
                    and not isinstance(actual, bool)
                    and isinstance(actual_transitions, int)
                    and not isinstance(actual_transitions, bool)
                    and actual == actual_transitions
                ):
                    continue
                errors.append(
                    f"{spec} llvm2 run {run['run_index']}: telemetry {key} "
                    f"was {actual!r}, expected run transitions "
                    f"({actual_transitions!r})"
                )
                continue
            if isinstance(expected, bool):
                if actual is expected:
                    continue
                errors.append(
                    f"{spec} llvm2 run {run['run_index']}: telemetry {key} "
                    f"was {actual!r}, expected {expected!r}"
                )
                continue
            if isinstance(expected, int):
                if (
                    isinstance(actual, int)
                    and not isinstance(actual, bool)
                    and not isinstance(expected, bool)
                    and actual == expected
                ):
                    continue
                errors.append(
                    f"{spec} llvm2 run {run['run_index']}: telemetry {key} "
                    f"was {actual!r}, expected {expected!r}"
                )
                continue
            if actual != expected:
                errors.append(
                    f"{spec} llvm2 run {run['run_index']}: telemetry {key} "
                    f"was {actual!r}, expected {expected!r}"
                )
        for total_match in required_llvm2_compilation_total_matches:
            require_compilation_total_match(spec, run, telemetry, total_match)
        selftest_requirement = required_llvm2_selftest_by_spec.get(spec)
        if selftest_requirement:
            require_strict_selftest_markers(spec, run, selftest_requirement)

    thresholds = policy["thresholds"][spec]
    tlc_median = recomputed_median(spec, "tlc", row["tlc"])
    interp_median = recomputed_median(spec, "interp", row["interp"])
    llvm2_median = recomputed_median(spec, "llvm2", row["llvm2"])
    require_llvm2_execution_faster = (
        "require_llvm2_execution_faster_than_tlc" in required_flags
    )
    llvm2_execution_median = recomputed_llvm2_execution_median(
        spec, row["llvm2"], require_llvm2_execution_faster
    )
    interp_speedup = speedup_from_medians(tlc_median, interp_median)
    llvm2_speedup = speedup_from_medians(tlc_median, llvm2_median)
    llvm2_execution_speedup = speedup_from_medians(
        tlc_median, llvm2_execution_median
    )
    require_advertised_speedup_match(
        spec,
        "speedup_llvm2_vs_tlc",
        row.get("speedup_llvm2_vs_tlc"),
        llvm2_speedup,
        "require_llvm2_faster_than_tlc" in required_flags,
    )
    require_advertised_speedup_match(
        spec,
        "speedup_llvm2_execution_vs_tlc",
        row.get("speedup_llvm2_execution_vs_tlc"),
        llvm2_execution_speedup,
        require_llvm2_execution_faster,
    )

    min_interp_speedup = thresholds.get("min_speedup_interp_vs_tlc")
    if min_interp_speedup is not None and (
        not isinstance(min_interp_speedup, (int, float))
        or isinstance(min_interp_speedup, bool)
        or not math.isfinite(min_interp_speedup)
        or min_interp_speedup <= 0
    ):
        errors.append(
            f"{spec}: min_speedup_interp_vs_tlc threshold was "
            f"{min_interp_speedup!r}, expected a positive finite number or null"
        )
        min_interp_speedup = None
    if (
        gate_mode != "full_native_fused"
        and min_interp_speedup is not None
        and (interp_speedup is None or interp_speedup <= min_interp_speedup)
    ):
        errors.append(
            f"{spec}: interp speedup {interp_speedup!r} at or below floor "
            f"{min_interp_speedup}"
        )
    min_llvm2_speedup = thresholds.get("min_speedup_llvm2_vs_tlc")
    if (
        not isinstance(min_llvm2_speedup, (int, float))
        or isinstance(min_llvm2_speedup, bool)
        or not math.isfinite(min_llvm2_speedup)
        or min_llvm2_speedup <= 0
    ):
        errors.append(
            f"{spec}: min_speedup_llvm2_vs_tlc threshold was "
            f"{min_llvm2_speedup!r}, expected a positive finite number"
        )
        min_llvm2_speedup = None
    elif llvm2_speedup is None or llvm2_speedup <= min_llvm2_speedup:
        errors.append(
            f"{spec}: llvm2 speedup {llvm2_speedup!r} at or below floor "
            f"{min_llvm2_speedup}"
        )
    if (
        require_llvm2_execution_faster
        and (llvm2_execution_speedup is None or llvm2_execution_speedup <= 1.0)
    ):
        errors.append(
            f"{spec}: llvm2 execution speedup {llvm2_execution_speedup!r} "
            "was not faster than TLC (requires > 1.0)"
        )

    min_ratio = thresholds.get("min_llvm2_vs_interp_ratio")
    if min_ratio is not None and (
        not isinstance(min_ratio, (int, float))
        or isinstance(min_ratio, bool)
        or not math.isfinite(min_ratio)
        or min_ratio <= 0
    ):
        errors.append(
            f"{spec}: min_llvm2_vs_interp_ratio threshold was "
            f"{min_ratio!r}, expected a positive finite number or null"
        )
        min_ratio = None
    if (
        gate_mode != "full_native_fused"
        and min_ratio is not None
        and interp_speedup not in (None, 0)
        and llvm2_speedup is not None
    ):
        ratio = llvm2_speedup / interp_speedup
        if ratio < min_ratio:
            errors.append(
                f"{spec}: llvm2/interp speedup ratio {ratio:.3f} below floor {min_ratio}"
            )


def write_policy_verdict(verdict, verdict_errors):
    payload = {
        "schema": "tla2.single_thread_supremacy.policy_verdict.v1",
        "verdict": verdict,
        "gate_mode": gate_mode,
        "expected_run_count": expected_run_count,
        "policy_file": str(policy_path),
        "summary_file": str(summary_path),
        "raw_benchmark_summary": {
            "schema": "benchmark_single_thread_backends_vs_tlc.summary.v1",
            "path": str(summary_path),
        },
        "policy_fields": {
            "state_counts": "expected_state_counts",
            "generated_state_counts": "expected_generated_state_counts",
            "llvm2_env": "gate_modes.*.required_llvm2_env",
        },
        "generated_state_count_sources": {
            "tlc": "runs[].states_generated",
            "interp": "runs[].transitions",
            "llvm2": "runs[].transitions",
        },
        "required_llvm2_env": dict(required_llvm2_env),
        "errors": list(verdict_errors),
    }
    (summary_path.parent / "policy_verdict.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


write_policy_verdict("fail" if errors else "pass", errors)

if errors:
    print("\n".join(errors), file=sys.stderr)
    raise SystemExit(1)
PY

if [[ $gate_exit -ne 0 ]]; then
    if [[ "$MODE" == "enforce" ]]; then
        echo "[single-thread-supremacy] FAIL: policy check failed." >&2
        exit 1
    fi
    echo "[single-thread-supremacy] WARNING: policy check failed." >&2
    exit 0
fi

echo "[single-thread-supremacy] PASS ($GATE_MODE)"
