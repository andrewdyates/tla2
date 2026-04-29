# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Policy checks for the single-thread supremacy gate wrapper."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from argparse import Namespace
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))

import benchmark_single_thread_backends_vs_tlc as bench


POLICY_PATH = (
    Path(__file__).parent
    / "tlc_comparison"
    / "single_thread_supremacy_gate.json"
)
WRAPPER_PATH = (
    Path(__file__).parent.parent
    / "scripts"
    / "check_single_thread_supremacy_gate.sh"
)


def _policy() -> dict:
    return json.loads(POLICY_PATH.read_text(encoding="utf-8"))


def _cli_benchmark_flags() -> set[str]:
    parser = bench.build_cli()
    return {
        action.dest
        for action in parser._actions
        if action.dest.startswith("require_")
        or action.dest == "allow_llvm2_invariant_rust_fallbacks"
    }


def test_single_thread_supremacy_full_policy_preserves_final_require_gates() -> None:
    cli_require_flags = {
        action.dest
        for action in bench.build_cli()._actions
        if action.dest.startswith("require_")
    }
    execution_speed_floor_flag = "require_llvm2_execution_faster_than_tlc"
    final_require_flags = cli_require_flags
    policy = _policy()
    full_mode = policy["gate_modes"][policy["final_gate_mode"]]

    assert execution_speed_floor_flag in cli_require_flags
    assert set(policy["required_llvm2_gate_flags"]) == final_require_flags
    assert set(full_mode["benchmark_flags"]) == final_require_flags
    assert "require_llvm2_faster_than_tlc" in full_mode["benchmark_flags"]
    assert execution_speed_floor_flag in full_mode["benchmark_flags"]
    assert (
        full_mode["required_llvm2_run_telemetry"]["compiled_bfs_execution_nanos"]
        == "positive"
    )


def test_single_thread_supremacy_gate_modes_reference_cli_flags() -> None:
    cli_flags = _cli_benchmark_flags()
    policy = _policy()

    for mode_name, mode in policy["gate_modes"].items():
        for flag in mode["benchmark_flags"]:
            assert flag in cli_flags, (mode_name, flag)
        for flag in mode.get("forbidden_benchmark_flags", []):
            assert flag in cli_flags, (mode_name, flag)


def test_single_thread_supremacy_wrapper_forwards_required_gate_flags() -> None:
    wrapper = WRAPPER_PATH.read_text(encoding="utf-8")

    assert "--gate-mode" in wrapper
    assert "gate_modes" in wrapper
    assert "benchmark_flags" in wrapper
    assert "forbidden_benchmark_flags" in wrapper
    assert "expected_state_counts" in wrapper
    assert "expected_generated_state_counts" in wrapper
    assert "states_found" in wrapper
    assert '"$GATE_MODE" "$RUNS"' in wrapper
    assert "expected_run_count" in wrapper
    assert "required_llvm2_run_telemetry" in wrapper
    assert "required_llvm2_run_telemetry_by_spec" in wrapper
    assert "required_llvm2_selftest_by_spec" in wrapper
    assert "required_llvm2_env" in wrapper, wrapper
    assert "require_llvm2_env_overrides" in wrapper, wrapper
    assert "required_llvm2_compilation_total_matches" in wrapper
    assert "require_generated_state_parity_by_run_index" in wrapper
    assert "require_successful_run_indexes" in wrapper
    assert "require_expected_generated_state_counts" in wrapper
    assert "require_compilation_total_match" in wrapper
    assert "policy_verdict.json" in wrapper
    assert "tla2.single_thread_supremacy.policy_verdict.v1" in wrapper
    assert "FLAT_PRIMARY_REBUILD_MARKER" in wrapper
    assert "latest_flat_primary_rebuild_segment" in wrapper
    assert "recomputed_median" in wrapper
    assert "recomputed_llvm2_execution_median" in wrapper
    assert "compiled_bfs_execution_seconds" in wrapper
    assert 'workers = run.get("workers")' in wrapper


def test_single_thread_supremacy_wrapper_defaults_to_three_run_final_claims() -> None:
    wrapper = WRAPPER_PATH.read_text(encoding="utf-8")

    assert 'RUNS="3"' in wrapper
    assert 'RUNS_SOURCE="default"' in wrapper
    assert 'RUNS_SOURCE="--runs"' in wrapper
    assert "Default run count (default: 3)" in wrapper
    assert '--runs "$RUNS"' in wrapper
    assert 'RUNS="$2"' in wrapper
    assert "must be at least 3 in enforce mode" in wrapper


def test_single_thread_supremacy_wrapper_can_reuse_built_binary() -> None:
    wrapper = WRAPPER_PATH.read_text(encoding="utf-8")

    assert 'TLA2_BIN="${TLA2_SINGLE_THREAD_SUPREMACY_TLA2_BIN:-}"' in wrapper
    assert "require_arg" in wrapper
    assert "--tla2-bin" in wrapper
    assert 'TLA2_BIN="$2"' in wrapper
    assert 'BENCHMARK_ARGS+=(--tla2-bin "$TLA2_BIN")' in wrapper


def test_single_thread_supremacy_wrapper_forwards_required_llvm2_env() -> None:
    wrapper = WRAPPER_PATH.read_text(encoding="utf-8")

    assert "--interp-env TLA2_LLVM2=0" in wrapper
    assert "--interp-env TLA2_LLVM2_BFS=0" in wrapper
    assert "--interp-env TLA2_BYTECODE_VM=1" in wrapper
    assert "--interp-env TLA2_AUTO_POR=0" in wrapper
    assert "--llvm2-env TLA2_LLVM2=1" in wrapper
    assert "--llvm2-env TLA2_LLVM2_BFS=1" in wrapper
    assert "--llvm2-env TLA2_LLVM2_EXISTS=1" in wrapper
    assert "--llvm2-env TLA2_COMPILED_BFS=1" in wrapper
    assert "--llvm2-env TLA2_FLAT_BFS=1" in wrapper
    assert "--llvm2-env TLA2_BYTECODE_VM=1" in wrapper
    assert "--llvm2-env TLA2_BYTECODE_VM_STATS=1" in wrapper
    assert "--llvm2-env TLA2_AUTO_POR=0" in wrapper
    assert "--llvm2-env TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST=strict" in wrapper
    assert "--llvm2-env TLA2_LLVM2_NATIVE_FUSED_STRICT=1" in wrapper
    assert "--llvm2-env TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL=O3" in wrapper
    assert (
        "--llvm2-env TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL=O3"
        in wrapper
    )
    assert "--llvm2-env TLA2_LLVM2_DISABLE_POST_RA_OPT=0" in wrapper
    assert "--llvm2-env TLA2_DISABLE_ARTIFACT_CACHE=1" in wrapper
    assert "--llvm2-env TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP=1" in wrapper
    assert 'TLA2_CACHE_DIR=$OUTPUT_DIR/llvm2-artifact-cache' in wrapper
    assert 'LLVM2_ENV_OVERRIDES=()' in wrapper, wrapper
    assert '--llvm2-env KEY=VALUE' in wrapper, wrapper
    assert 'LLVM2_ENV_OVERRIDES+=(--llvm2-env "$2")' in wrapper, wrapper
    assert '"${LLVM2_ENV_OVERRIDES[@]}"' in wrapper, wrapper


def test_final_policy_keeps_post_ra_optimization_enabled() -> None:
    policy = _policy()
    full_mode = policy["gate_modes"][policy["final_gate_mode"]]
    wrapper = WRAPPER_PATH.read_text(encoding="utf-8")
    benchmark = Path(bench.__file__).read_text(encoding="utf-8")

    assert full_mode["required_llvm2_env"]["TLA2_LLVM2_DISABLE_POST_RA_OPT"] == "0"
    assert full_mode["required_llvm2_env"]["TLA2_DISABLE_ARTIFACT_CACHE"] == "1"
    assert (
        full_mode["required_llvm2_env"][
            "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP"
        ]
        == "1"
    )
    assert (
        full_mode["required_llvm2_run_telemetry"][
            "llvm2_native_fused_local_dedup"
        ]
        is False
    )
    assert "--llvm2-env TLA2_LLVM2_DISABLE_POST_RA_OPT=0" in wrapper
    assert "--llvm2-env TLA2_DISABLE_ARTIFACT_CACHE=1" in wrapper
    assert "--llvm2-env TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP=1" in wrapper
    assert 'TLA2_LLVM2_DISABLE_POST_RA_OPT": "0"' in benchmark
    assert 'TLA2_DISABLE_ARTIFACT_CACHE": "1"' in benchmark
    assert 'TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP": "1"' in benchmark


def test_final_policy_requires_strict_native_fused_runtime() -> None:
    policy = _policy()
    full_mode = policy["gate_modes"][policy["final_gate_mode"]]
    wrapper = WRAPPER_PATH.read_text(encoding="utf-8")
    benchmark = Path(bench.__file__).read_text(encoding="utf-8")

    assert full_mode["required_llvm2_env"]["TLA2_LLVM2_NATIVE_FUSED_STRICT"] == "1"
    assert "--llvm2-env TLA2_LLVM2_NATIVE_FUSED_STRICT=1" in wrapper
    assert 'TLA2_LLVM2_NATIVE_FUSED_STRICT": "1"' in benchmark


def test_single_thread_supremacy_wrapper_forwards_extra_llvm2_env(
    tmp_path: Path,
) -> None:
    shim = tmp_path / "python3"
    args_log = tmp_path / "benchmark_args.json"
    output_dir = tmp_path / "out"
    parent_loop_opt = "TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL=O3"
    callout_opt = "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL=O1"

    shim.write_text(
        f"""#!{sys.executable}
import json
import os
import sys
from pathlib import Path

if len(sys.argv) > 1 and sys.argv[1].endswith("benchmark_single_thread_backends_vs_tlc.py"):
    Path({str(args_log)!r}).write_text(json.dumps(sys.argv[2:]), encoding="utf-8")
    raise SystemExit(1)

real_python = os.environ["REAL_PYTHON"]
os.execv(real_python, [real_python] + sys.argv[1:])
""",
        encoding="utf-8",
    )
    shim.chmod(0o755)

    env = os.environ.copy()
    env["PATH"] = f"{tmp_path}{os.pathsep}{env.get('PATH', '')}"
    env["REAL_PYTHON"] = sys.executable
    result = subprocess.run(
        [
            "bash",
            str(WRAPPER_PATH),
            "--mode",
            "warn",
            "--gate-mode",
            "interim_action_only_native_fused",
            "--runs",
            "0",
            "--output-dir",
            str(output_dir),
            "--llvm2-env",
            parent_loop_opt,
            "--llvm2-env",
            callout_opt,
        ],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode == 0, result.stderr
    assert "[single-thread-supremacy] WARNING: benchmark run failed." in result.stderr, (
        result.stderr
    )
    benchmark_args = json.loads(args_log.read_text(encoding="utf-8"))
    for env_override in (parent_loop_opt, callout_opt):
        position = benchmark_args.index(env_override)
        assert benchmark_args[position - 1] == "--llvm2-env", benchmark_args
    assert benchmark_args.index(parent_loop_opt) > benchmark_args.index(
        f"TLA2_CACHE_DIR={output_dir}/llvm2-artifact-cache"
    ), benchmark_args


def test_single_thread_supremacy_wrapper_sanitizes_behavioral_tla2_env() -> None:
    wrapper = WRAPPER_PATH.read_text(encoding="utf-8")

    assert "while IFS='=' read -r key _; do" in wrapper
    assert '[[ "$key" == TLA2_* ]]' in wrapper
    assert 'unset "$key"' in wrapper
    assert "done < <(env)" in wrapper


def test_single_thread_supremacy_wrapper_reports_missing_option_operands() -> None:
    for option in (
        "--mode",
        "--runs",
        "--gate-mode",
        "--output-dir",
        "--tla2-bin",
        "--llvm2-env",
    ):
        result = subprocess.run(
            ["bash", str(WRAPPER_PATH), option],
            check=False,
            capture_output=True,
            text=True,
        )
        assert result.returncode != 0
        assert f"Error: {option} requires an argument" in result.stderr
        assert "unbound variable" not in result.stderr


def test_single_thread_supremacy_wrapper_rejects_malformed_llvm2_env() -> None:
    result = subprocess.run(
        ["bash", str(WRAPPER_PATH), "--llvm2-env", "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL"],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode != 0, result.stderr
    assert "Error: --llvm2-env expects KEY=VALUE" in result.stderr, result.stderr
    assert "unbound variable" not in result.stderr, result.stderr


@pytest.mark.parametrize(
    "env_override",
    [
        "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL=O1",
        "TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL=O1",
    ],
)
def test_single_thread_supremacy_enforce_full_native_rejects_weaker_opt_override(
    tmp_path: Path,
    env_override: str,
) -> None:
    result = subprocess.run(
        [
            "bash",
            str(WRAPPER_PATH),
            "--mode",
            "enforce",
            "--output-dir",
            str(tmp_path / "out"),
            "--llvm2-env",
            env_override,
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    env_key = env_override.split("=", 1)[0]
    assert result.returncode != 0, result.stderr
    assert (
        f"Error: enforce/full_native_fused requires {env_key}=O3; "
        f"--llvm2-env supplied {env_override}"
    ) in result.stderr
    assert "[single-thread-supremacy] PASS" not in result.stdout


@pytest.mark.parametrize(
    "env_override",
    [
        "TLA2_LLVM2=0",
        "TLA2_LLVM2_BFS=0",
        "TLA2_LLVM2_EXISTS=0",
        "TLA2_COMPILED_BFS=0",
        "TLA2_FLAT_BFS=0",
        "TLA2_BYTECODE_VM=0",
        "TLA2_BYTECODE_VM_STATS=0",
        "TLA2_AUTO_POR=1",
        "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST=off",
        "TLA2_LLVM2_NATIVE_FUSED_STRICT=0",
        "TLA2_LLVM2_DISABLE_POST_RA_OPT=1",
    ],
)
def test_single_thread_supremacy_enforce_full_native_rejects_protected_env_override(
    tmp_path: Path,
    env_override: str,
) -> None:
    expected_values = {
        "TLA2_LLVM2": "1",
        "TLA2_LLVM2_BFS": "1",
        "TLA2_LLVM2_EXISTS": "1",
        "TLA2_COMPILED_BFS": "1",
        "TLA2_FLAT_BFS": "1",
        "TLA2_BYTECODE_VM": "1",
        "TLA2_BYTECODE_VM_STATS": "1",
        "TLA2_AUTO_POR": "0",
        "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST": "strict",
        "TLA2_LLVM2_NATIVE_FUSED_STRICT": "1",
        "TLA2_LLVM2_DISABLE_POST_RA_OPT": "0",
    }
    env_key = env_override.split("=", 1)[0]

    result = subprocess.run(
        [
            "bash",
            str(WRAPPER_PATH),
            "--mode",
            "enforce",
            "--output-dir",
            str(tmp_path / "out"),
            "--llvm2-env",
            env_override,
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode != 0, result.stderr
    assert (
        "Error: enforce/full_native_fused requires "
        f"{env_key}={expected_values[env_key]}; --llvm2-env supplied {env_override}"
    ) in result.stderr
    assert "[single-thread-supremacy] PASS" not in result.stdout


def test_single_thread_supremacy_enforce_full_native_allows_exact_opt_override(
    tmp_path: Path,
) -> None:
    shim = tmp_path / "python3"
    args_log = tmp_path / "benchmark_args.json"
    output_dir = tmp_path / "out"
    env_override = "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL=O3"

    shim.write_text(
        f"""#!{sys.executable}
import json
import os
import sys
from pathlib import Path

if len(sys.argv) > 1 and sys.argv[1].endswith("benchmark_single_thread_backends_vs_tlc.py"):
    Path({str(args_log)!r}).write_text(json.dumps(sys.argv[2:]), encoding="utf-8")
    raise SystemExit(1)

real_python = os.environ["REAL_PYTHON"]
os.execv(real_python, [real_python] + sys.argv[1:])
""",
        encoding="utf-8",
    )
    shim.chmod(0o755)

    env = os.environ.copy()
    env["PATH"] = f"{tmp_path}{os.pathsep}{env.get('PATH', '')}"
    env["REAL_PYTHON"] = sys.executable
    result = subprocess.run(
        [
            "bash",
            str(WRAPPER_PATH),
            "--mode",
            "enforce",
            "--runs",
            "3",
            "--output-dir",
            str(output_dir),
            "--llvm2-env",
            env_override,
        ],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode != 0, result.stderr
    assert "[single-thread-supremacy] FAIL: benchmark run failed." in result.stderr
    benchmark_args = json.loads(args_log.read_text(encoding="utf-8"))
    position = benchmark_args.index(env_override)
    assert benchmark_args[position - 1] == "--llvm2-env", benchmark_args


def test_single_thread_supremacy_enforce_default_is_final_mode() -> None:
    policy = _policy()
    assert policy["default_gate_mode"] == policy["final_gate_mode"]

    wrapper = WRAPPER_PATH.read_text(encoding="utf-8")
    assert 'run_mode == "enforce"' in wrapper
    assert 'policy.get("final_gate_mode")' in wrapper
    assert (
        'if run_mode == "enforce":\n'
        '        mode_name = policy.get("final_gate_mode")'
    ) in wrapper
    assert "Explicit policy gate mode outside enforce" in wrapper
    assert "--gate-mode is required outside --mode enforce" in wrapper


def test_single_thread_supremacy_enforce_ignores_weaker_requested_gate(
    tmp_path: Path,
) -> None:
    shim = tmp_path / "python3"
    args_log = tmp_path / "benchmark_args.json"
    fake_tla2 = tmp_path / "tla2"
    gate_flag_defaults = {flag: False for flag in _cli_benchmark_flags()}
    fake_tla2.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
    fake_tla2.chmod(0o755)

    shim.write_text(
        f"""#!{sys.executable}
import json
import os
import sys
from pathlib import Path

if len(sys.argv) > 1 and sys.argv[1].endswith("benchmark_single_thread_backends_vs_tlc.py"):
    args = sys.argv[2:]
    Path({str(args_log)!r}).write_text(json.dumps(args), encoding="utf-8")
    output_dir = Path(args[args.index("--output-dir") + 1])
    expected_run_count = int(args[args.index("--runs") + 1])
    gate_flags = json.loads({json.dumps(gate_flag_defaults)!r})
    specs = []
    i = 0
    while i < len(args):
        arg = args[i]
        if arg.startswith("--require-") or arg == "--allow-llvm2-invariant-rust-fallbacks":
            gate_flags[arg[2:].replace("-", "_")] = True
            i += 1
        elif arg == "--specs":
            i += 1
            while i < len(args) and not args[i].startswith("--"):
                specs.append(args[i])
                i += 1
        else:
            i += 2 if arg in {{"--runs", "--output-dir", "--target-dir", "--tla2-bin"}} else 1
    telemetry_by_spec = {{
        "CoffeeCan1000BeansSafety": {{
            "llvm2_actions_compiled": 4,
            "llvm2_actions_total": 4,
            "llvm2_invariants_compiled": 1,
            "llvm2_invariants_total": 1,
            "llvm2_native_fused_invariant_count": 1,
            "llvm2_native_fused_mode": "invariant_checking",
            "llvm2_native_fused_state_len": 2,
            "llvm2_native_fused_state_constraint_count": 0,
        }},
        "EWD998Small": {{
            "llvm2_actions_compiled": 15,
            "llvm2_actions_total": 15,
            "llvm2_invariants_compiled": 3,
            "llvm2_invariants_total": 3,
            "llvm2_native_fused_invariant_count": 3,
            "llvm2_native_fused_mode": "state_constraint_checking",
            "llvm2_native_fused_state_len": 15,
            "llvm2_native_fused_state_constraint_count": 1,
            "llvm2_state_constraints_compiled": 1,
            "llvm2_state_constraints_total": 1,
        }},
        "MCLamportMutex": {{
            "llvm2_actions_compiled": 27,
            "llvm2_actions_total": 27,
            "llvm2_invariants_compiled": 3,
            "llvm2_invariants_total": 3,
            "llvm2_native_fused_invariant_count": 3,
            "llvm2_native_fused_mode": "state_constraint_checking",
            "llvm2_native_fused_state_len": 89,
            "llvm2_native_fused_state_constraint_count": 1,
            "llvm2_state_constraints_compiled": 1,
            "llvm2_state_constraints_total": 1,
        }},
    }}
    expected_states_by_spec = {{
        "CoffeeCan1000BeansSafety": 501500,
        "EWD998Small": 1520618,
        "MCLamportMutex": 724274,
    }}
    expected_generated_states_by_spec = {{
        "CoffeeCan1000BeansSafety": 1498502,
        "EWD998Small": 9630813,
        "MCLamportMutex": 2496350,
    }}
    selftest_counts_by_spec = {{
        "CoffeeCan1000BeansSafety": {{"actions": 4, "state_constraints": 0, "invariants": 1, "state_len": 2}},
        "EWD998Small": {{"actions": 15, "state_constraints": 1, "invariants": 3, "state_len": 15}},
        "MCLamportMutex": {{"actions": 27, "state_constraints": 1, "invariants": 3, "state_len": 89}},
    }}
    def selftest_text(spec):
        counts = selftest_counts_by_spec[spec]
        return (
            {bench.FLAT_PRIMARY_REBUILD_MARKER!r} + "\\n"
            "[llvm2-selftest] prepared native fused callout selftest: "
            f"actions={{counts['actions']}}, state_constraints={{counts['state_constraints']}}, "
            f"invariants={{counts['invariants']}}, missing_expected=0, fail_closed=true\\n"
            "[llvm2-selftest] running native fused callout selftest on first real parent: "
            f"state_len={{counts['state_len']}}, actions={{counts['actions']}}, "
            f"state_constraints={{counts['state_constraints']}}, "
            f"invariants={{counts['invariants']}}, fail_closed=true\\n"
            "[llvm2-selftest] native fused callout selftest complete\\n"
        )
    base_telemetry = {{
        "compiled_bfs_level_loop_started": True,
        "compiled_bfs_level_loop_fused": True,
        "compiled_bfs_level_loop_initial_states": 1,
        "compiled_bfs_levels_completed": 1,
        "compiled_bfs_parents_processed": 1,
        "compiled_bfs_successors_new": 1,
        "compiled_bfs_execution_nanos": 1_000_000_000,
        "compiled_bfs_execution_seconds": 1.0,
        "compiled_bfs_total_states": 1,
        "llvm2_native_fused_level_built": True,
        "llvm2_native_fused_level_active": True,
        "llvm2_bfs_level_loop_kind": "native_fused_llvm2_parent_loop",
        "llvm2_native_fused_local_dedup": False,
        "llvm2_native_fused_regular_invariants_checked": True,
        "flat_state_primary": True,
        "flat_bfs_frontier_active": True,
        "flat_bfs_frontier_fallbacks": 0,
        "fallback_reasons": [],
    }}
    rows = []
    for spec in specs:
        states_found = expected_states_by_spec[spec]
        generated_states = expected_generated_states_by_spec[spec]
        telemetry = dict(base_telemetry)
        telemetry.update(telemetry_by_spec.get(spec, {{}}))
        telemetry["compiled_bfs_successors_generated"] = generated_states
        telemetry["compiled_bfs_successors_new"] = max(states_found - 1, 1)
        telemetry["compiled_bfs_total_states"] = states_found
        rows.append(
            {{
                "spec": spec,
                "tlc": {{
                    "all_ok": True,
                    "median_seconds": 3.0,
                    "expected_states": states_found,
                    "expected_states_match": True,
                    "runs": [
                        {{
                            "run_index": index,
                            "states_found": states_found,
                            "elapsed_seconds": 3.0,
                            "workers": 1,
                            "returncode": 0,
                            "states_generated": generated_states,
                        }}
                        for index in range(1, expected_run_count + 1)
                    ],
                }},
                "interp": {{
                    "all_ok": True,
                    "median_seconds": 2.0,
                    "expected_states": states_found,
                    "expected_states_match": True,
                    "runs": [
                        {{
                            "run_index": index,
                            "states_found": states_found,
                            "elapsed_seconds": 2.0,
                            "workers": 1,
                            "returncode": 0,
                            "transitions": generated_states,
                        }}
                        for index in range(1, expected_run_count + 1)
                    ],
                }},
                "llvm2": {{
                    "all_ok": True,
                    "median_seconds": 2.0,
                    "execution_median_seconds": 1.0,
                    "expected_states": states_found,
                    "expected_states_match": True,
                    "runs": [
                        {{
                            "run_index": index,
                            "states_found": states_found,
                            "elapsed_seconds": 2.0,
                            "workers": 1,
                            "returncode": 0,
                            "transitions": generated_states,
                            "artifact_dir": f"artifacts/{{spec}}/llvm2-{{index}}",
                            "llvm2_telemetry": telemetry,
                            "env_overrides": {{
                                "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST": "strict",
                                "TLA2_LLVM2_NATIVE_FUSED_STRICT": "1",
                                "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL": "O3",
                                "TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL": "O3",
                                "TLA2_LLVM2_DISABLE_POST_RA_OPT": "0",
                                "TLA2_DISABLE_ARTIFACT_CACHE": "1",
                                "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP": "1",
                            }},
                        }}
                        for index in range(1, expected_run_count + 1)
                    ],
                }},
                "parity_interp_vs_tlc": True,
                "parity_llvm2_vs_tlc": True,
                "llvm2_gate_failures": [],
                "speedup_interp_vs_tlc": 1.5,
                "speedup_llvm2_vs_tlc": 1.5,
                "speedup_llvm2_execution_vs_tlc": 3.0,
            }}
        )
    output_dir.mkdir(parents=True, exist_ok=True)
    for row in rows:
        for run in row["llvm2"]["runs"]:
            artifact_dir = output_dir / run["artifact_dir"]
            artifact_dir.mkdir(parents=True, exist_ok=True)
            (artifact_dir / "stdout.txt").write_text(
                selftest_text(row["spec"]),
                encoding="utf-8",
            )
            (artifact_dir / "stderr.txt").write_text("", encoding="utf-8")
    (output_dir / "summary.json").write_text(
        json.dumps({{"gate_flags": gate_flags, "rows": rows}}),
        encoding="utf-8",
    )
    raise SystemExit(0)

real_python = os.environ["REAL_PYTHON"]
os.execv(real_python, [real_python] + sys.argv[1:])
""",
        encoding="utf-8",
    )
    shim.chmod(0o755)

    env = os.environ.copy()
    env["PATH"] = f"{tmp_path}{os.pathsep}{env.get('PATH', '')}"
    env["REAL_PYTHON"] = sys.executable
    env["TLA2_SINGLE_THREAD_SUPREMACY_GATE_MODE"] = "interim_action_only_native_fused"
    result = subprocess.run(
        [
            "bash",
            str(WRAPPER_PATH),
            "--mode",
            "enforce",
            "--gate-mode",
            "interim_action_only_native_fused",
            "--runs",
            "3",
            "--output-dir",
            str(tmp_path / "out"),
            "--tla2-bin",
            str(fake_tla2),
        ],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode == 0, result.stderr
    assert "[single-thread-supremacy] PASS (full_native_fused)" in result.stdout
    benchmark_args = json.loads(args_log.read_text(encoding="utf-8"))
    assert "--require-llvm2-compiled-invariants" in benchmark_args
    assert "--allow-llvm2-invariant-rust-fallbacks" not in benchmark_args


def test_single_thread_supremacy_enforce_rejects_skip_env(tmp_path: Path) -> None:
    env = os.environ.copy()
    env["TLA2_SINGLE_THREAD_SUPREMACY_SKIP"] = "1"
    result = subprocess.run(
        ["bash", str(WRAPPER_PATH), "--mode", "enforce", "--output-dir", str(tmp_path / "out")],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode != 0
    assert (
        "TLA2_SINGLE_THREAD_SUPREMACY_SKIP is not allowed in enforce mode"
        in result.stderr
    )
    assert "[single-thread-supremacy] PASS" not in result.stdout


def test_single_thread_supremacy_warn_mode_still_allows_skip_env(tmp_path: Path) -> None:
    env = os.environ.copy()
    env["TLA2_SINGLE_THREAD_SUPREMACY_SKIP"] = "1"
    result = subprocess.run(
        [
            "bash",
            str(WRAPPER_PATH),
            "--mode",
            "warn",
            "--gate-mode",
            "interim_action_only_native_fused",
            "--output-dir",
            str(tmp_path / "out"),
        ],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode == 0


def test_single_thread_supremacy_enforce_rejects_policy_file_override(
    tmp_path: Path,
) -> None:
    fake_tla2 = tmp_path / "tla2"
    fake_tla2.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
    fake_tla2.chmod(0o755)
    policy_path = tmp_path / "single_thread_supremacy_gate.json"
    policy_path.write_text(json.dumps(_policy()), encoding="utf-8")
    env = os.environ.copy()
    env["TLA2_SINGLE_THREAD_SUPREMACY_POLICY_FILE"] = str(policy_path)

    result = subprocess.run(
        [
            "bash",
            str(WRAPPER_PATH),
            "--mode",
            "enforce",
            "--output-dir",
            str(tmp_path / "out"),
            "--tla2-bin",
            str(fake_tla2),
        ],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode != 0
    assert (
        "TLA2_SINGLE_THREAD_SUPREMACY_POLICY_FILE is not allowed in enforce mode"
        in result.stderr
    )
    assert result.stdout == ""


def test_single_thread_supremacy_enforce_rejects_sub_three_cli_runs(tmp_path: Path) -> None:
    result = subprocess.run(
        [
            "bash",
            str(WRAPPER_PATH),
            "--mode",
            "enforce",
            "--runs",
            "1",
            "--output-dir",
            str(tmp_path / "out"),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode != 0
    assert "Error: --runs must be at least 3 in enforce mode" in result.stderr


def test_single_thread_supremacy_enforce_rejects_sub_three_env_runs(tmp_path: Path) -> None:
    env = os.environ.copy()
    env["TLA2_SINGLE_THREAD_SUPREMACY_RUNS"] = "1"
    result = subprocess.run(
        ["bash", str(WRAPPER_PATH), "--mode", "enforce", "--output-dir", str(tmp_path / "out")],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode != 0
    assert (
        "Error: TLA2_SINGLE_THREAD_SUPREMACY_RUNS must be at least 3 in enforce mode"
        in result.stderr
    )


def test_single_thread_supremacy_interim_mode_is_action_only_explicit() -> None:
    policy = _policy()
    interim = policy["gate_modes"]["interim_action_only_native_fused"]
    full = policy["gate_modes"][policy["final_gate_mode"]]

    assert "require_llvm2_native_fused_level" in interim["benchmark_flags"]
    assert "allow_llvm2_invariant_rust_fallbacks" in interim["benchmark_flags"]
    assert "require_llvm2_compiled_invariants" not in interim["benchmark_flags"]
    assert "require_llvm2_successor_telemetry" not in interim["benchmark_flags"]
    assert "require_llvm2_compiled_invariants" in interim["forbidden_benchmark_flags"]

    assert "require_llvm2_compiled_invariants" in full["benchmark_flags"]
    assert "require_llvm2_successor_telemetry" in full["benchmark_flags"]
    assert "allow_llvm2_invariant_rust_fallbacks" in full["forbidden_benchmark_flags"]
    assert interim["required_llvm2_compilation_total_matches"] == ["actions"]
    assert full["required_llvm2_compilation_total_matches"] == [
        "actions",
        "invariants",
    ]
    assert full["required_llvm2_env"] == {
        "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST": "strict",
        "TLA2_LLVM2_NATIVE_FUSED_STRICT": "1",
        "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL": "O3",
        "TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL": "O3",
        "TLA2_LLVM2_DISABLE_POST_RA_OPT": "0",
        "TLA2_DISABLE_ARTIFACT_CACHE": "1",
        "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP": "1",
    }
    assert interim["require_generated_state_parity_by_run_index"] is True
    assert full["require_generated_state_parity_by_run_index"] is True
    assert interim["required_llvm2_run_telemetry"] == {
        "compiled_bfs_level_loop_started": True,
        "compiled_bfs_level_loop_fused": True,
        "compiled_bfs_level_loop_initial_states": "positive",
        "compiled_bfs_levels_completed": "positive",
        "compiled_bfs_parents_processed": "positive",
        "compiled_bfs_successors_generated": "transitions",
        "compiled_bfs_execution_nanos": "positive",
        "compiled_bfs_total_states": "positive",
        "llvm2_native_fused_level_built": True,
        "llvm2_native_fused_level_active": True,
        "llvm2_bfs_level_loop_kind": "native_fused_llvm2_parent_loop",
        "transitions": "positive",
        "flat_state_primary": True,
        "flat_bfs_frontier_active": True,
        "flat_bfs_frontier_fallbacks": 0,
    }
    assert full["required_llvm2_run_telemetry"] == {
        "compiled_bfs_level_loop_started": True,
        "compiled_bfs_level_loop_fused": True,
        "compiled_bfs_level_loop_initial_states": "positive",
        "compiled_bfs_levels_completed": "positive",
        "compiled_bfs_parents_processed": "positive",
        "compiled_bfs_successors_generated": "transitions",
        "compiled_bfs_successors_new": "positive",
        "compiled_bfs_execution_nanos": "positive",
        "compiled_bfs_total_states": "states_found",
        "llvm2_native_fused_level_built": True,
        "llvm2_native_fused_level_active": True,
        "llvm2_bfs_level_loop_kind": "native_fused_llvm2_parent_loop",
        "transitions": "positive",
        "llvm2_native_fused_regular_invariants_checked": True,
        "llvm2_native_fused_invariant_count": "all",
        "llvm2_native_fused_local_dedup": False,
        "flat_state_primary": True,
        "flat_bfs_frontier_active": True,
        "flat_bfs_frontier_fallbacks": 0,
    }
    assert full["required_llvm2_run_telemetry_by_spec"] == {
        "CoffeeCan1000BeansSafety": {
            "llvm2_native_fused_mode": "invariant_checking",
            "llvm2_native_fused_state_len": 2,
            "llvm2_native_fused_state_constraint_count": 0,
        },
        "EWD998Small": {
            "llvm2_native_fused_mode": "state_constraint_checking",
            "llvm2_native_fused_state_len": 15,
            "llvm2_native_fused_state_constraint_count": 1,
            "llvm2_state_constraints_compiled": 1,
            "llvm2_state_constraints_total": 1,
        },
        "MCLamportMutex": {
            "llvm2_native_fused_mode": "state_constraint_checking",
            "llvm2_native_fused_state_len": 89,
            "llvm2_native_fused_state_constraint_count": 1,
            "llvm2_state_constraints_compiled": 1,
            "llvm2_state_constraints_total": 1,
        },
    }
    assert full["required_llvm2_selftest_by_spec"] == {
        "CoffeeCan1000BeansSafety": {
            "actions": 4,
            "state_constraints": 0,
            "invariants": 1,
            "state_len": 2,
        },
        "EWD998Small": {
            "actions": 15,
            "state_constraints": 1,
            "invariants": 3,
            "state_len": 15,
        },
        "MCLamportMutex": {
            "actions": 27,
            "state_constraints": 1,
            "invariants": 3,
            "state_len": 89,
        },
    }


def test_single_thread_supremacy_policy_declares_fixed_final_state_counts() -> None:
    policy = _policy()

    assert policy["expected_state_counts"] == {
        "CoffeeCan1000BeansSafety": 501500,
        "EWD998Small": 1520618,
        "MCLamportMutex": 724274,
    }
    assert set(policy["expected_state_counts"]) == set(policy["specs"])


def test_single_thread_supremacy_policy_declares_fixed_final_generated_state_counts() -> None:
    policy = _policy()

    assert policy["expected_generated_state_counts"] == {
        "CoffeeCan1000BeansSafety": 1498502,
        "EWD998Small": 9630813,
        "MCLamportMutex": 2496350,
    }
    assert set(policy["expected_generated_state_counts"]) == set(policy["specs"])


def test_single_thread_supremacy_wrapper_writes_policy_verdict_schema(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()

    result = _run_policy_only_check(tmp_path, summary)

    verdict_path = tmp_path / "out" / "policy_verdict.json"
    assert result.returncode == 0, result.stderr
    verdict = json.loads(verdict_path.read_text(encoding="utf-8"))
    assert verdict["schema"] == "tla2.single_thread_supremacy.policy_verdict.v1"
    assert verdict["verdict"] == "pass"
    assert verdict["policy_fields"]["generated_state_counts"] == (
        "expected_generated_state_counts"
    )
    assert verdict["policy_fields"]["llvm2_env"] == "gate_modes.*.required_llvm2_env", verdict
    assert verdict["required_llvm2_env"] == _required_llvm2_env(), verdict
    assert verdict["generated_state_count_sources"] == {
        "tlc": "runs[].states_generated",
        "interp": "runs[].transitions",
        "llvm2": "runs[].transitions",
    }
    assert verdict["raw_benchmark_summary"]["path"].endswith("/summary.json")


def test_policy_rejects_wrong_raw_state_count_despite_summary_booleans(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
        states_found=501499,
    )
    row = summary["rows"][0]
    row["tlc"]["expected_states_match"] = True
    row["interp"]["expected_states_match"] = True
    row["llvm2"]["expected_states_match"] = True
    row["parity_interp_vs_tlc"] = True
    row["parity_llvm2_vs_tlc"] = True

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0, result.stderr
    assert (
        "CoffeeCan1000BeansSafety: tlc run 1: states_found was 501499, "
        "expected fixed 501500"
    ) in result.stderr
    assert (
        "CoffeeCan1000BeansSafety: llvm2 run 1: states_found was 501499, "
        "expected fixed 501500"
    ) in result.stderr


def test_policy_rejects_summaries_with_too_few_runs(tmp_path: Path) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
        run_count=1,
    )

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0, result.stderr
    assert (
        "CoffeeCan1000BeansSafety: tlc had 1 runs in summary, expected 3"
    ) in result.stderr
    assert (
        "CoffeeCan1000BeansSafety: llvm2 had 1 runs in summary, expected 3"
    ) in result.stderr


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_bool_successful_run_index(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0][mode_name]["runs"][0]["run_index"] = True

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} successful run at position 1: "
        "run_index was True, expected an integer"
    ) in result.stderr
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} successful run_index values "
        "were [2, 3], expected sequential [1, 2, 3]"
    ) in result.stderr


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_duplicate_successful_run_index(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0][mode_name]["runs"][1]["run_index"] = 1

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} successful run_index 1 "
        "was duplicated"
    ) in result.stderr
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} successful run_index values "
        "were [1, 3], expected sequential [1, 2, 3]"
    ) in result.stderr


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_non_sequential_successful_run_index(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0][mode_name]["runs"][0]["run_index"] = 0

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} successful run_index values "
        "were [0, 2, 3], expected sequential [1, 2, 3]"
    ) in result.stderr


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_generated_state_count_mismatch(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    field_name = "states_generated" if mode_name == "tlc" else "transitions"
    summary["rows"][0][mode_name]["runs"][1][field_name] = 7

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} run 2: generated-state count "
        f"({field_name}) was 7, "
        "expected fixed 1498502"
    ) in result.stderr


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_malformed_generated_state_count(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    field_name = "states_generated" if mode_name == "tlc" else "transitions"
    summary["rows"][0][mode_name]["runs"][0][field_name] = True

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} run 1: generated-state count "
        f"({field_name}) was True, "
        "expected an integer"
    ) in result.stderr
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} run 1: generated-state count "
        "was missing or invalid"
    ) in result.stderr


def test_policy_rejects_missing_tlc_generated_state_count(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    for row in summary["rows"]:
        for run in row["tlc"]["runs"]:
            run.pop("states_generated", None)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: tlc run 1: generated-state count "
        "was missing or invalid"
    ) in result.stderr


def test_policy_rejects_missing_expected_generated_state_count(
    tmp_path: Path,
) -> None:
    policy = _policy()
    del policy["expected_generated_state_counts"]["CoffeeCan1000BeansSafety"]
    summary = _full_valid_policy_summary()

    result = _run_policy_only_check(
        tmp_path,
        summary,
        policy=policy,
        mode="warn",
    )

    assert result.returncode == 0
    assert "[single-thread-supremacy] WARNING: policy check failed." in result.stderr
    assert (
        "CoffeeCan1000BeansSafety: invalid fixed expected generated-state count "
        "in policy: None"
    ) in result.stderr


def test_policy_rejects_malformed_expected_generated_state_count(
    tmp_path: Path,
) -> None:
    policy = _policy()
    policy["expected_generated_state_counts"]["CoffeeCan1000BeansSafety"] = True
    summary = _full_valid_policy_summary()

    result = _run_policy_only_check(
        tmp_path,
        summary,
        policy=policy,
        mode="warn",
    )

    assert result.returncode == 0
    assert "[single-thread-supremacy] WARNING: policy check failed." in result.stderr
    assert (
        "CoffeeCan1000BeansSafety: invalid fixed expected generated-state count "
        "in policy: True"
    ) in result.stderr


def test_policy_rejects_non_boolean_required_gate_flag(tmp_path: Path) -> None:
    summary = _full_valid_policy_summary()
    summary["gate_flags"]["require_llvm2_compiled_bfs"] = 1

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "required benchmark flag was not enabled: require_llvm2_compiled_bfs"
        in result.stderr
    )


def test_policy_rejects_truthy_forbidden_gate_flag(tmp_path: Path) -> None:
    summary = _full_valid_policy_summary()
    summary["gate_flags"]["allow_llvm2_invariant_rust_fallbacks"] = 1

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "forbidden benchmark flag was not disabled: allow_llvm2_invariant_rust_fallbacks"
        in result.stderr
    )


def test_policy_rejects_numeric_false_forbidden_gate_flag(tmp_path: Path) -> None:
    summary = _full_valid_policy_summary()
    summary["gate_flags"]["allow_llvm2_invariant_rust_fallbacks"] = 0

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "forbidden benchmark flag was not disabled: allow_llvm2_invariant_rust_fallbacks"
        in result.stderr
    )


def test_policy_rejects_missing_forbidden_gate_flag(tmp_path: Path) -> None:
    summary = _full_valid_policy_summary()
    del summary["gate_flags"]["allow_llvm2_invariant_rust_fallbacks"]

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "forbidden benchmark flag was not disabled: allow_llvm2_invariant_rust_fallbacks"
        in result.stderr
    )


def test_policy_rejects_tlc_summary_runs_that_are_not_single_threaded(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0]["tlc"]["runs"][0]["workers"] = 2

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "CoffeeCan1000BeansSafety: tlc run 1: workers was 2, expected 1" in (
        result.stderr
    )


def test_policy_rejects_bool_tlc_worker_count(tmp_path: Path) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0]["tlc"]["runs"][0]["workers"] = True

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: tlc run 1: workers was True, expected 1"
        in result.stderr
    )


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_non_single_thread_workers_for_all_modes(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0][mode_name]["runs"][0]["workers"] = 2

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} run 1: workers was 2, expected 1"
        in result.stderr
    )


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_malformed_all_ok_with_zero_returncode(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0][mode_name]["all_ok"] = 1

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    label = "TLC" if mode_name == "tlc" else mode_name
    assert f"CoffeeCan1000BeansSafety: {label} run failed" in result.stderr


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_nonzero_run_returncode_despite_malformed_all_ok(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    row = summary["rows"][0]
    row[mode_name]["all_ok"] = "malformed-truthy"
    row[mode_name]["runs"][0]["returncode"] = 7

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} run 1: "
        "returncode was 7, expected 0"
    ) in result.stderr


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_bool_run_returncode(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0][mode_name]["runs"][0]["returncode"] = False

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} run 1: "
        "returncode was False, expected 0"
    ) in result.stderr


@pytest.mark.parametrize("mode_name", ["tlc", "interp", "llvm2"])
def test_policy_rejects_non_null_run_error(
    tmp_path: Path,
    mode_name: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0][mode_name]["runs"][0]["error"] = "Invariant violated."

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        f"CoffeeCan1000BeansSafety: {mode_name} run 1: "
        "error was 'Invariant violated.', expected null"
    ) in result.stderr


@pytest.mark.parametrize(
    ("field", "message"),
    [
        ("parity_interp_vs_tlc", "interp parity drift vs TLC"),
        ("parity_llvm2_vs_tlc", "llvm2 parity drift vs TLC"),
    ],
)
def test_policy_rejects_malformed_parity_booleans(
    tmp_path: Path,
    field: str,
    message: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0][field] = 1

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert f"CoffeeCan1000BeansSafety: {message}" in result.stderr


def test_policy_rejects_summary_advertised_expected_state_drift(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "EWD998Small",
        _valid_policy_telemetry("EWD998Small"),
        transitions=1,
        advertised_expected_states=123,
    )

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "EWD998Small: llvm2 advertised expected_states 123, "
        "expected fixed 1520618"
    ) in result.stderr


def test_policy_rejects_summary_without_positive_native_fused_work(
    tmp_path: Path,
) -> None:
    telemetry = _valid_policy_telemetry("CoffeeCan1000BeansSafety")
    del telemetry["compiled_bfs_levels_completed"]
    summary = _policy_summary("CoffeeCan1000BeansSafety", telemetry, transitions=1)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "compiled_bfs_levels_completed" in result.stderr
    assert "expected a positive integer" in result.stderr

    telemetry["compiled_bfs_levels_completed"] = 1
    telemetry["compiled_bfs_parents_processed"] = 0
    summary = _policy_summary("CoffeeCan1000BeansSafety", telemetry, transitions=1)
    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "compiled_bfs_parents_processed" in result.stderr
    assert "expected a positive integer" in result.stderr


def test_full_gate_rejects_summary_without_admitted_successors(
    tmp_path: Path,
) -> None:
    telemetry = _valid_policy_telemetry("CoffeeCan1000BeansSafety")
    telemetry["compiled_bfs_successors_new"] = 0
    summary = _policy_summary("CoffeeCan1000BeansSafety", telemetry, transitions=1)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "compiled_bfs_successors_new" in result.stderr
    assert "expected a positive integer" in result.stderr


def test_full_gate_rejects_summary_without_execution_timing(
    tmp_path: Path,
) -> None:
    telemetry = _valid_policy_telemetry("CoffeeCan1000BeansSafety")
    del telemetry["compiled_bfs_execution_nanos"]
    summary = _policy_summary("CoffeeCan1000BeansSafety", telemetry, transitions=1)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "compiled_bfs_execution_nanos" in result.stderr
    assert "expected a positive integer" in result.stderr


def test_full_gate_rejects_summary_without_recorded_llvm2_backend_env(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    for row in summary["rows"]:
        for run in row["llvm2"]["runs"]:
            run.pop("env_overrides", None)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0, result.stderr
    missing_env_message = (
        "env_overrides was None, expected an object recording LLVM2 backend controls"
    )
    assert missing_env_message in result.stderr, result.stderr


@pytest.mark.parametrize(
    ("env_key", "bad_value"),
    [
        ("TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL", "O1"),
        ("TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL", "O1"),
        ("TLA2_LLVM2_NATIVE_FUSED_STRICT", "0"),
    ],
)
def test_full_gate_rejects_recorded_llvm2_backend_env_drift(
    tmp_path: Path,
    env_key: str,
    bad_value: str,
) -> None:
    summary = _full_valid_policy_summary()
    summary["rows"][0]["llvm2"]["runs"][0]["env_overrides"][env_key] = bad_value

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0, result.stderr
    expected_message = (
        f"CoffeeCan1000BeansSafety llvm2 run 1: env_overrides[{env_key!r}] "
        f"was {bad_value!r}, expected {_required_llvm2_env()[env_key]!r}"
    )
    assert expected_message in result.stderr, result.stderr


def test_benchmark_markdown_exposes_backend_controls() -> None:
    report = {
        "timestamp": "now",
        "git_commit": "abc123",
        "artifact_bundle": "reports/test",
        "invocation": "benchmark",
        "backend_controls": {"llvm2_env": _required_llvm2_env()},
        "rows": [],
    }

    markdown = bench.render_markdown(report)

    assert "## Backend Controls" in markdown, markdown
    assert "`TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL` | `O3`" in markdown, markdown
    parent_loop_control = "`TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL` | `O3`"
    assert parent_loop_control in markdown, markdown


def test_full_gate_rejects_bool_positive_telemetry(
    tmp_path: Path,
) -> None:
    telemetry = _valid_policy_telemetry("CoffeeCan1000BeansSafety")
    telemetry["compiled_bfs_execution_nanos"] = True
    summary = _policy_summary("CoffeeCan1000BeansSafety", telemetry, transitions=1)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "compiled_bfs_execution_nanos" in result.stderr
    assert "was True, expected a positive integer" in result.stderr


def test_full_gate_allows_same_index_llvm2_wall_sample_slower_than_tlc_when_median_wins(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    row = summary["rows"][0]
    row["tlc"]["runs"][1]["elapsed_seconds"] = 1.0
    row["llvm2"]["runs"][1]["elapsed_seconds"] = 2.0

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode == 0, result.stderr


def test_full_gate_allows_same_index_compiled_bfs_execution_sample_slower_than_tlc_when_median_wins(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    row = summary["rows"][0]
    row["tlc"]["runs"][1]["elapsed_seconds"] = 1.0
    row["llvm2"]["runs"][1]["llvm2_telemetry"][
        "compiled_bfs_execution_nanos"
    ] = 2_000_000_000
    row["llvm2"]["runs"][1]["llvm2_telemetry"][
        "compiled_bfs_execution_seconds"
    ] = 2.0

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode == 0, result.stderr


def test_full_gate_rejects_compiled_bfs_execution_seconds_nanos_mismatch(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    telemetry = summary["rows"][0]["llvm2"]["runs"][0]["llvm2_telemetry"]
    telemetry["compiled_bfs_execution_seconds"] = 0.25
    telemetry["compiled_bfs_execution_nanos"] = 2_000_000_000

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety llvm2 run 1: compiled BFS execution "
        "seconds/nanos mismatch"
    ) in result.stderr


def test_full_gate_rejects_integer_for_required_boolean_telemetry(
    tmp_path: Path,
) -> None:
    telemetry = _valid_policy_telemetry("CoffeeCan1000BeansSafety")
    telemetry["compiled_bfs_level_loop_started"] = 1
    summary = _policy_summary("CoffeeCan1000BeansSafety", telemetry, transitions=1)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "compiled_bfs_level_loop_started" in result.stderr
    assert "was 1, expected True" in result.stderr


def test_full_gate_rejects_compiled_bfs_total_state_drift(
    tmp_path: Path,
) -> None:
    telemetry = _valid_policy_telemetry("CoffeeCan1000BeansSafety")
    telemetry["compiled_bfs_total_states"] = 501499
    summary = _policy_summary("CoffeeCan1000BeansSafety", telemetry, transitions=1)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "compiled_bfs_total_states was 501499, "
        "expected run states_found (501500)"
    ) in result.stderr


def test_policy_rejects_summary_without_positive_llvm2_transitions(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=0,
    )

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "telemetry transitions was 0, expected a positive integer" in result.stderr


def test_policy_rejects_compiled_generated_below_llvm2_transitions(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )
    for run in summary["rows"][0]["llvm2"]["runs"]:
        run["llvm2_telemetry"]["compiled_bfs_successors_generated"] = 1

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "telemetry compiled_bfs_successors_generated was 1, "
        "expected run transitions (1498502)"
    ) in result.stderr


def test_full_gate_rejects_missing_strict_native_callout_selftest_markers(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )

    result = _run_policy_only_check(
        tmp_path,
        summary,
        write_selftest_artifacts=False,
    )

    assert result.returncode != 0
    assert "missing stdout.txt/stderr.txt under artifact_dir" in result.stderr
    assert (
        "missing strict native callout selftest marker: "
        "prepared native fused callout selftest"
    ) in result.stderr
    assert (
        "missing strict native callout selftest marker: "
        "running native fused callout selftest on first real parent"
    ) in result.stderr
    assert (
        "missing strict native callout selftest marker: "
        "native fused callout selftest complete"
    ) in result.stderr


def test_full_gate_rejects_selftest_markers_without_post_rebuild_marker(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )

    result = _run_policy_only_check(
        tmp_path,
        summary,
        selftest_artifact_mode="missing_marker",
    )

    assert result.returncode != 0
    assert "missing post-rebuild flat-primary marker" in result.stderr
    assert (
        "missing strict native callout selftest marker: "
        "prepared native fused callout selftest"
    ) in result.stderr


def test_full_gate_rejects_stale_pre_rebuild_selftest_markers(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )

    result = _run_policy_only_check(
        tmp_path,
        summary,
        selftest_artifact_mode="stale_pre_rebuild",
    )

    assert result.returncode != 0
    assert (
        "missing strict native callout selftest marker: "
        "prepared native fused callout selftest"
    ) in result.stderr
    assert (
        "missing strict native callout selftest marker: "
        "running native fused callout selftest on first real parent"
    ) in result.stderr
    assert (
        "missing strict native callout selftest marker: "
        "native fused callout selftest complete"
    ) in result.stderr


def test_full_gate_rejects_nonzero_missing_expected_selftest_marker(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )

    result = _run_policy_only_check(
        tmp_path,
        summary,
        selftest_missing_expected="1",
    )

    assert result.returncode != 0
    assert (
        "missing strict native callout selftest marker: "
        "prepared native fused callout selftest"
    ) in result.stderr
    assert "reported missing expected callouts: 1" in result.stderr


@pytest.mark.parametrize(
    ("spec_name", "wrong_state_len"),
    [
        ("CoffeeCan1000BeansSafety", 1),
        ("MCLamportMutex", 63),
    ],
)
def test_full_gate_rejects_wrong_selftest_state_len(
    tmp_path: Path,
    spec_name: str,
    wrong_state_len: int,
) -> None:
    summary = _full_valid_policy_summary()

    result = _run_policy_only_check(
        tmp_path,
        summary,
        selftest_state_len_by_spec={spec_name: wrong_state_len},
    )

    assert result.returncode != 0
    assert (
        f"{spec_name} llvm2 run 1: missing strict native callout selftest marker: "
        "running native fused callout selftest on first real parent"
    ) in result.stderr
    assert "[single-thread-supremacy] FAIL: policy check failed." in result.stderr


@pytest.mark.parametrize("kind", ["invariant", "state_constraint"])
@pytest.mark.parametrize(
    "line_template",
    [
        "[llvm2-selftest] {kind} callout index=0 symbol=sym name=Name status=Ok value=0",
        "[llvm2-selftest] callout kind={kind} index=0 symbol=sym name=Name status=Ok value=0",
    ],
)
def test_full_gate_rejects_false_standalone_strict_selftest_result(
    tmp_path: Path,
    kind: str,
    line_template: str,
) -> None:
    summary = _full_valid_policy_summary()

    result = _run_policy_only_check(
        tmp_path,
        summary,
        selftest_extra_lines=[line_template.format(kind=kind)],
    )

    assert result.returncode != 0
    assert f"kind={kind} status=Ok value=0" in result.stderr
    assert "reported false strict check" in result.stderr


@pytest.mark.parametrize(
    "line",
    [
        "[llvm2-selftest] action callout index=0 symbol=Action name=Action status=Ok value=0",
        "[llvm2-selftest] callout kind=action index=0 symbol=Action name=Action status=Ok value=0",
        "[llvm2-selftest] state_constraint_after_action callout index=0 symbol=SC name=SC status=Ok value=0",
        "[llvm2-selftest] callout kind=state_constraint_after_action index=0 symbol=SC name=SC status=Ok value=0",
    ],
)
def test_full_gate_allows_disabled_action_and_after_action_prune_selftest_lines(
    tmp_path: Path,
    line: str,
) -> None:
    summary = _full_valid_policy_summary()

    result = _run_policy_only_check(
        tmp_path,
        summary,
        selftest_extra_lines=[line],
    )

    assert result.returncode == 0, result.stderr


def test_policy_all_requirement_rejects_missing_actual_and_total(
    tmp_path: Path,
) -> None:
    telemetry = _valid_policy_telemetry("CoffeeCan1000BeansSafety")
    del telemetry["llvm2_native_fused_invariant_count"]
    del telemetry["llvm2_invariants_total"]
    summary = _policy_summary("CoffeeCan1000BeansSafety", telemetry, transitions=1)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert "llvm2_native_fused_invariant_count" in result.stderr
    assert "expected all invariants (None)" in result.stderr


@pytest.mark.parametrize(
    ("compiled_key", "total_key"),
    [
        ("llvm2_actions_compiled", "llvm2_actions_total"),
        ("llvm2_invariants_compiled", "llvm2_invariants_total"),
    ],
)
def test_full_gate_rejects_partial_llvm2_compilation_totals(
    tmp_path: Path,
    compiled_key: str,
    total_key: str,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )
    for run in summary["rows"][0]["llvm2"]["runs"]:
        run["llvm2_telemetry"][compiled_key] = (
            run["llvm2_telemetry"][total_key] - 1
        )

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert f"telemetry {compiled_key}" in result.stderr
    assert f"expected {total_key}" in result.stderr


def test_full_gate_rejects_native_fused_without_regular_invariant_telemetry() -> None:
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_actions_compiled=2,
                        llvm2_actions_total=2,
                        llvm2_invariants_compiled=1,
                        llvm2_invariants_total=1,
                        compiled_bfs_step_active=True,
                        compiled_bfs_level_active=True,
                        compiled_bfs_level_loop_started=True,
                        compiled_bfs_level_loop_initial_states=1,
                        compiled_bfs_level_loop_fused=True,
                        compiled_bfs_levels_completed=1,
                        compiled_bfs_parents_processed=1,
                        compiled_bfs_successors_generated=1,
                        compiled_bfs_total_states=1,
                        llvm2_native_fused_level_built=True,
                        llvm2_native_fused_level_active=True,
                        llvm2_bfs_level_loop_kind="native_fused_llvm2_parent_loop",
                        llvm2_native_fused_regular_invariants_checked=False,
                        flat_state_primary=True,
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=0,
                        fallback_reasons=[],
                    ).to_dict(),
                }
            ]
        },
    }
    args = _gate_args(
        require_llvm2_compiled_actions=True,
        require_llvm2_all_actions=True,
        require_llvm2_compiled_invariants=True,
        require_llvm2_compiled_bfs=True,
        require_llvm2_fused_level=True,
        require_llvm2_native_fused_level=True,
        require_flat_state_primary=True,
        require_flat_bfs_frontier=True,
        require_no_llvm2_fallbacks=True,
        require_llvm2_faster_than_tlc=True,
    )

    failures = bench.evaluate_llvm2_truth_gates(row, args)
    assert any(
        "llvm2_native_fused_regular_invariants_checked=False" in failure
        for failure in failures
    )

    telemetry = row["llvm2"]["runs"][0]["llvm2_telemetry"]
    telemetry["llvm2_native_fused_regular_invariants_checked"] = True
    failures = bench.evaluate_llvm2_truth_gates(row, args)
    assert any(
        "native fused invariant coverage did not include all regular invariants" in failure
        for failure in failures
    )

    telemetry["llvm2_native_fused_mode"] = "invariant_checking"
    telemetry["llvm2_native_fused_invariant_count"] = 1
    assert bench.evaluate_llvm2_truth_gates(row, args) == []


def test_interim_gate_still_allows_only_invariant_rust_fallback_after_native_flat_dedup() -> None:
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_actions_compiled=2,
                        llvm2_actions_total=2,
                        llvm2_invariants_compiled=0,
                        llvm2_invariants_total=1,
                        compiled_bfs_step_active=True,
                        compiled_bfs_level_active=True,
                        compiled_bfs_level_loop_started=True,
                        compiled_bfs_level_loop_initial_states=1,
                        compiled_bfs_level_loop_fused=True,
                        compiled_bfs_levels_completed=1,
                        compiled_bfs_parents_processed=1,
                        compiled_bfs_successors_generated=1,
                        compiled_bfs_total_states=1,
                        llvm2_native_fused_level_built=True,
                        llvm2_native_fused_level_active=True,
                        llvm2_native_fused_mode="action_only",
                        llvm2_bfs_level_loop_kind="native_fused_llvm2_parent_loop",
                        flat_state_primary=True,
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=0,
                        fallback_reasons=[
                            "[llvm2] failed to compile invariant 0: unsupported aggregate",
                            "[llvm2] native fused CompiledBfsLevel using action-only fallback: not all invariants have native entries",
                            "[llvm2] invariant-checking native fused CompiledBfsLevel unavailable, falling back to action-only native/prototype: unsupported aggregate",
                        ],
                    ).to_dict(),
                }
            ]
        },
    }
    args = _gate_args(
        require_llvm2_compiled_actions=True,
        require_llvm2_all_actions=True,
        require_llvm2_compiled_bfs=True,
        require_llvm2_fused_level=True,
        require_llvm2_native_fused_level=True,
        require_flat_state_primary=True,
        require_flat_bfs_frontier=True,
        require_no_llvm2_fallbacks=True,
        allow_llvm2_invariant_rust_fallbacks=True,
        require_llvm2_faster_than_tlc=True,
    )

    assert bench.evaluate_llvm2_truth_gates(row, args) == []

    telemetry = row["llvm2"]["runs"][0]["llvm2_telemetry"]
    telemetry["llvm2_native_fused_mode"] = None
    failures = bench.evaluate_llvm2_truth_gates(row, args)
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures)

    telemetry["llvm2_native_fused_mode"] = "action_only"
    telemetry["llvm2_bfs_level_loop_kind"] = (
        "prototype_rust_parent_loop_over_llvm2_action_invariant_pointers"
    )
    failures = bench.evaluate_llvm2_truth_gates(row, args)
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures)

    telemetry["llvm2_bfs_level_loop_kind"] = "native_fused_llvm2_parent_loop"
    telemetry["fallback_reasons"].append(
        "[llvm2] failed to compile action 'A': unsupported"
    )
    failures = bench.evaluate_llvm2_truth_gates(row, args)
    assert any("non-invariant LLVM2 fallback reasons" in failure for failure in failures)


def test_single_thread_supremacy_policy_rejects_sub_tlc_llvm2_speedups() -> None:
    policy = _policy()

    for spec_name in policy["specs"]:
        threshold = policy["thresholds"][spec_name]["min_speedup_llvm2_vs_tlc"]
        assert threshold >= 1.0, spec_name


@pytest.mark.parametrize(
    ("spec_name", "threshold_key", "threshold_value", "expected_type"),
    [
        (
            "CoffeeCan1000BeansSafety",
            "min_speedup_interp_vs_tlc",
            True,
            "a positive finite number or null",
        ),
        (
            "CoffeeCan1000BeansSafety",
            "min_speedup_llvm2_vs_tlc",
            False,
            "a positive finite number",
        ),
        (
            "CoffeeCan1000BeansSafety",
            "min_speedup_llvm2_vs_tlc",
            0,
            "a positive finite number",
        ),
        (
            "EWD998Small",
            "min_llvm2_vs_interp_ratio",
            -0.1,
            "a positive finite number or null",
        ),
    ],
)
def test_policy_rejects_malformed_speedup_thresholds(
    tmp_path: Path,
    spec_name: str,
    threshold_key: str,
    threshold_value: object,
    expected_type: str,
) -> None:
    policy = _policy()
    policy["thresholds"][spec_name][threshold_key] = threshold_value
    summary = _full_valid_policy_summary()

    result = _run_policy_only_check(tmp_path, summary, policy=policy, mode="warn")

    assert result.returncode == 0
    assert "[single-thread-supremacy] WARNING: policy check failed." in result.stderr
    assert (
        f"{spec_name}: {threshold_key} threshold was {threshold_value!r}, "
        f"expected {expected_type}"
    ) in result.stderr


def test_policy_rejects_malformed_forbidden_flag_list(
    tmp_path: Path,
) -> None:
    policy = _policy()
    policy["gate_modes"][policy["final_gate_mode"]][
        "forbidden_benchmark_flags"
    ] = "allow_llvm2_invariant_rust_fallbacks"
    summary = _full_valid_policy_summary()

    result = _run_policy_only_check(tmp_path, summary, policy=policy, mode="warn")

    assert result.returncode != 0
    assert (
        "policy gate_modes.full_native_fused.forbidden_benchmark_flags "
        "must be a list of non-empty strings"
    ) in result.stderr


def test_full_gate_allows_slow_interpreter_and_low_llvm2_interp_ratio(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    rows_by_spec = {row["spec"]: row for row in summary["rows"]}

    def set_mode_elapsed(row: dict, mode_name: str, elapsed_seconds: float) -> None:
        row[mode_name]["median_seconds"] = elapsed_seconds
        for run in row[mode_name]["runs"]:
            run["elapsed_seconds"] = elapsed_seconds

    coffee = rows_by_spec["CoffeeCan1000BeansSafety"]
    set_mode_elapsed(coffee, "interp", 10.0)
    coffee["speedup_interp_vs_tlc"] = 0.3

    ewd = rows_by_spec["EWD998Small"]
    set_mode_elapsed(ewd, "interp", 1.0)
    set_mode_elapsed(ewd, "llvm2", 2.5)
    ewd["speedup_interp_vs_tlc"] = 3.0
    ewd["speedup_llvm2_vs_tlc"] = 1.2

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode == 0, result.stderr


def test_policy_rejects_llvm2_speedup_equal_to_floor(tmp_path: Path) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
        speedup_llvm2_vs_tlc=1.0,
    )

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: llvm2 speedup 1.0 at or below floor 1.0"
        in result.stderr
    )


def test_policy_recomputes_speedup_from_run_medians(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
        speedup_llvm2_vs_tlc=1.5,
        tlc_elapsed_seconds=3.0,
        llvm2_elapsed_seconds=4.0,
    )

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: llvm2 speedup 0.75 at or below floor 1.0"
        in result.stderr
    )


def test_policy_rejects_advertised_llvm2_wall_speedup_drift(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
        speedup_llvm2_vs_tlc=99.0,
        llvm2_elapsed_seconds=2.0,
    )

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: advertised speedup_llvm2_vs_tlc 99.0 "
        "did not match recomputed speedup 1.5"
    ) in result.stderr
    assert "llvm2 speedup 1.5 at or below floor" not in result.stderr


def test_policy_rejects_advertised_llvm2_execution_median_drift(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )
    _set_llvm2_execution_telemetry(summary, seconds=0.5, nanos=500_000_000)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: llvm2 advertised execution_median_seconds 1.0 "
        "did not match recomputed execution median 0.5"
    ) in result.stderr
    assert (
        "CoffeeCan1000BeansSafety: advertised speedup_llvm2_execution_vs_tlc 3.0 "
        "did not match recomputed speedup 6.0"
    ) in result.stderr


def test_policy_rejects_missing_advertised_llvm2_execution_median_when_required(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )
    summary["rows"][0]["llvm2"]["execution_median_seconds"] = None

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: llvm2 advertised execution_median_seconds "
        "was None, expected recomputed execution median 1.0"
    ) in result.stderr


def test_policy_rejects_missing_advertised_llvm2_execution_speedup_when_required(
    tmp_path: Path,
) -> None:
    summary = _policy_summary(
        "CoffeeCan1000BeansSafety",
        _valid_policy_telemetry("CoffeeCan1000BeansSafety"),
        transitions=1,
    )
    summary["rows"][0]["speedup_llvm2_execution_vs_tlc"] = None

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: advertised speedup_llvm2_execution_vs_tlc "
        "was None, expected recomputed speedup 3.0"
    ) in result.stderr


def test_policy_rejects_slow_recomputed_llvm2_execution_speedup_even_with_wall_clock_win(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    for row in summary["rows"]:
        row["llvm2"]["execution_median_seconds"] = 4.0
        row["speedup_llvm2_execution_vs_tlc"] = 0.75
    _set_llvm2_execution_telemetry(summary, seconds=4.0, nanos=4_000_000_000)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode != 0
    assert (
        "CoffeeCan1000BeansSafety: llvm2 execution speedup 0.75 "
        "was not faster than TLC (requires > 1.0)"
    ) in result.stderr


def test_policy_recomputes_llvm2_execution_median_from_positive_nanos(
    tmp_path: Path,
) -> None:
    summary = _full_valid_policy_summary()
    _set_llvm2_execution_telemetry(summary, seconds=None, nanos=1_000_000_000)

    result = _run_policy_only_check(tmp_path, summary)

    assert result.returncode == 0, result.stderr


def _gate_args(**overrides: bool) -> Namespace:
    defaults = {
        "require_llvm2_compiled_actions": False,
        "require_llvm2_all_actions": False,
        "require_llvm2_compiled_invariants": False,
        "require_llvm2_compiled_bfs": False,
        "require_llvm2_fused_level": False,
        "require_llvm2_native_fused_level": False,
        "require_flat_state_primary": False,
        "require_flat_bfs_frontier": False,
        "require_no_llvm2_fallbacks": False,
        "allow_llvm2_invariant_rust_fallbacks": False,
        "require_llvm2_faster_than_tlc": False,
        "require_llvm2_execution_faster_than_tlc": False,
        "require_llvm2_successor_telemetry": False,
    }
    defaults.update(overrides)
    return Namespace(**defaults)


def _valid_policy_telemetry(spec_name: str) -> dict:
    expected_states = _policy()["expected_state_counts"][spec_name]
    expected_generated_states = _policy()["expected_generated_state_counts"][spec_name]
    actions_by_spec = {
        "CoffeeCan1000BeansSafety": 4,
        "EWD998Small": 15,
        "MCLamportMutex": 27,
    }
    invariants_by_spec = {
        "CoffeeCan1000BeansSafety": 1,
        "EWD998Small": 3,
        "MCLamportMutex": 3,
    }
    actions = actions_by_spec[spec_name]
    invariants = invariants_by_spec[spec_name]
    telemetry = {
        "llvm2_actions_compiled": actions,
        "llvm2_actions_total": actions,
        "llvm2_invariants_compiled": invariants,
        "llvm2_invariants_total": invariants,
        "compiled_bfs_level_loop_started": True,
        "compiled_bfs_level_loop_fused": True,
        "compiled_bfs_level_loop_initial_states": 1,
        "compiled_bfs_levels_completed": 1,
        "compiled_bfs_parents_processed": 1,
        "compiled_bfs_successors_generated": expected_generated_states,
        "compiled_bfs_successors_new": max(expected_states - 1, 1),
        "compiled_bfs_execution_nanos": 1_000_000_000,
        "compiled_bfs_execution_seconds": 1.0,
        "compiled_bfs_total_states": expected_states,
        "llvm2_native_fused_level_built": True,
        "llvm2_native_fused_level_active": True,
        "llvm2_bfs_level_loop_kind": "native_fused_llvm2_parent_loop",
        "llvm2_native_fused_local_dedup": False,
        "llvm2_native_fused_regular_invariants_checked": True,
        "flat_state_primary": True,
        "flat_bfs_frontier_active": True,
        "flat_bfs_frontier_fallbacks": 0,
        "fallback_reasons": [],
    }
    if spec_name == "CoffeeCan1000BeansSafety":
        telemetry.update(
            {
                "llvm2_native_fused_invariant_count": 1,
                "llvm2_native_fused_mode": "invariant_checking",
                "llvm2_native_fused_state_len": 2,
                "llvm2_native_fused_state_constraint_count": 0,
            }
        )
    else:
        telemetry.update(
            {
                "llvm2_native_fused_invariant_count": 3,
                "llvm2_native_fused_mode": "state_constraint_checking",
                "llvm2_native_fused_state_constraint_count": 1,
                "llvm2_state_constraints_compiled": 1,
                "llvm2_state_constraints_total": 1,
            }
        )
        state_len_by_spec = {
            "EWD998Small": 15,
            "MCLamportMutex": 89,
        }
        if spec_name in state_len_by_spec:
            telemetry["llvm2_native_fused_state_len"] = state_len_by_spec[spec_name]
    return telemetry


def _required_llvm2_env() -> dict[str, str]:
    policy = _policy()
    return dict(policy["gate_modes"][policy["final_gate_mode"]]["required_llvm2_env"])


def _policy_summary(
    spec_name: str,
    telemetry: dict,
    *,
    transitions: int,
    run_count: int = 3,
    speedup_interp_vs_tlc: float = 1.5,
    speedup_llvm2_vs_tlc: float = 1.5,
    speedup_llvm2_execution_vs_tlc: float = 3.0,
    tlc_elapsed_seconds: float = 3.0,
    interp_elapsed_seconds: float | None = None,
    llvm2_elapsed_seconds: float | None = None,
    llvm2_execution_elapsed_seconds: float | None = None,
    states_found: int | None = None,
    advertised_expected_states: int | None = None,
) -> dict:
    expected_states = _policy()["expected_state_counts"][spec_name]
    if states_found is None:
        states_found = expected_states
    if transitions == 1:
        transitions = _policy()["expected_generated_state_counts"][spec_name]
    if advertised_expected_states is None:
        advertised_expected_states = expected_states
    if interp_elapsed_seconds is None:
        interp_elapsed_seconds = tlc_elapsed_seconds / speedup_interp_vs_tlc
    if llvm2_elapsed_seconds is None:
        llvm2_elapsed_seconds = tlc_elapsed_seconds / speedup_llvm2_vs_tlc
    if llvm2_execution_elapsed_seconds is None:
        llvm2_execution_elapsed_seconds = (
            tlc_elapsed_seconds / speedup_llvm2_execution_vs_tlc
        )

    def plain_runs(mode_name: str, elapsed_seconds: float) -> list[dict]:
        runs = []
        for index in range(1, run_count + 1):
            run = {
                "run_index": index,
                "states_found": states_found,
                "elapsed_seconds": elapsed_seconds,
                "returncode": 0,
                "artifact_dir": f"artifacts/{spec_name}/{mode_name}-{index}",
            }
            if mode_name == "tlc":
                run["states_generated"] = transitions
            else:
                run["transitions"] = transitions
            run["workers"] = 1
            runs.append(run)
        return runs

    llvm2_runs = [
        {
            "run_index": index,
            "states_found": states_found,
            "elapsed_seconds": llvm2_elapsed_seconds,
            "returncode": 0,
            "workers": 1,
            "transitions": transitions,
            "artifact_dir": f"artifacts/{spec_name}/llvm2-{index}",
            "llvm2_telemetry": dict(telemetry),
            "env_overrides": _required_llvm2_env(),
        }
        for index in range(1, run_count + 1)
    ]
    return {
        "gate_flags": {
            **{flag: False for flag in _cli_benchmark_flags()},
            **{
                flag: True
                for flag in _policy()["gate_modes"][_policy()["final_gate_mode"]][
                    "benchmark_flags"
                ]
            },
        },
        "rows": [
            {
                "spec": spec_name,
                "tlc": {
                    "all_ok": True,
                    "median_seconds": tlc_elapsed_seconds,
                    "expected_states": advertised_expected_states,
                    "expected_states_match": True,
                    "runs": plain_runs("tlc", tlc_elapsed_seconds),
                },
                "interp": {
                    "all_ok": True,
                    "median_seconds": interp_elapsed_seconds,
                    "expected_states": advertised_expected_states,
                    "expected_states_match": True,
                    "runs": plain_runs("interp", interp_elapsed_seconds),
                },
                "llvm2": {
                    "all_ok": True,
                    "median_seconds": llvm2_elapsed_seconds,
                    "execution_median_seconds": llvm2_execution_elapsed_seconds,
                    "expected_states": advertised_expected_states,
                    "expected_states_match": True,
                    "runs": llvm2_runs,
                },
                "parity_interp_vs_tlc": True,
                "parity_llvm2_vs_tlc": True,
                "llvm2_gate_failures": [],
                "speedup_interp_vs_tlc": speedup_interp_vs_tlc,
                "speedup_llvm2_vs_tlc": speedup_llvm2_vs_tlc,
                "speedup_llvm2_execution_vs_tlc": (
                    speedup_llvm2_execution_vs_tlc
                ),
            }
        ],
    }


def _full_valid_policy_summary() -> dict:
    rows = []
    summary = None
    for spec_name in _policy()["specs"]:
        spec_summary = _policy_summary(
            spec_name,
            _valid_policy_telemetry(spec_name),
            transitions=1,
        )
        if summary is None:
            summary = spec_summary
        rows.extend(spec_summary["rows"])
    assert summary is not None
    summary["rows"] = rows
    return summary


def _set_llvm2_execution_telemetry(
    summary: dict,
    *,
    seconds: float | None,
    nanos: int | None,
) -> None:
    for row in summary["rows"]:
        for run in row["llvm2"]["runs"]:
            telemetry = run["llvm2_telemetry"]
            telemetry["compiled_bfs_execution_seconds"] = seconds
            telemetry["compiled_bfs_execution_nanos"] = nanos


def _run_policy_only_check(
    tmp_path: Path,
    summary: dict,
    *,
    policy: dict | None = None,
    mode: str = "enforce",
    write_selftest_artifacts: bool = True,
    selftest_missing_expected: str = "0",
    selftest_artifact_mode: str = "valid",
    selftest_extra_lines: list[str] | None = None,
    selftest_state_len_by_spec: dict[str, int] | None = None,
) -> subprocess.CompletedProcess[str]:
    shim = tmp_path / "python3"
    fake_tla2 = tmp_path / "tla2"
    summary_json = json.dumps(summary)
    write_selftest_artifacts_literal = repr(write_selftest_artifacts)
    selftest_missing_expected_literal = repr(selftest_missing_expected)
    selftest_artifact_mode_literal = repr(selftest_artifact_mode)
    selftest_extra_lines_json = json.dumps(selftest_extra_lines or [])
    selftest_state_len_by_spec_json = json.dumps(selftest_state_len_by_spec or {})
    flat_primary_rebuild_marker_literal = repr(bench.FLAT_PRIMARY_REBUILD_MARKER)
    fake_tla2.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
    fake_tla2.chmod(0o755)
    shim.write_text(
        f"""#!{sys.executable}
import json
import os
import sys
from pathlib import Path

if len(sys.argv) > 1 and sys.argv[1].endswith("benchmark_single_thread_backends_vs_tlc.py"):
    args = sys.argv[2:]
    output_dir = Path(args[args.index("--output-dir") + 1])
    output_dir.mkdir(parents=True, exist_ok=True)
    summary = json.loads({summary_json!r})
    selftest_extra_lines = json.loads({selftest_extra_lines_json!r})
    selftest_state_len_by_spec = {{
        "CoffeeCan1000BeansSafety": 2,
        "EWD998Small": 15,
        "MCLamportMutex": 89,
        **json.loads({selftest_state_len_by_spec_json!r}),
    }}
    selftest_counts_by_spec = {{
        "CoffeeCan1000BeansSafety": {{"actions": 4, "state_constraints": 0, "invariants": 1}},
        "EWD998Small": {{"actions": 15, "state_constraints": 1, "invariants": 3}},
        "MCLamportMutex": {{"actions": 27, "state_constraints": 1, "invariants": 3}},
    }}
    def selftest_text(spec):
        counts = selftest_counts_by_spec[spec]
        missing_expected = {selftest_missing_expected_literal}
        extra = "\\n".join(selftest_extra_lines)
        if extra:
            extra += "\\n"
        return (
            "[llvm2-selftest] prepared native fused callout selftest: "
            f"actions={{counts['actions']}}, state_constraints={{counts['state_constraints']}}, "
            f"invariants={{counts['invariants']}}, missing_expected={{missing_expected}}, fail_closed=true\\n"
            "[llvm2-selftest] running native fused callout selftest on first real parent: "
            f"state_len={{selftest_state_len_by_spec[spec]}}, actions={{counts['actions']}}, "
            f"state_constraints={{counts['state_constraints']}}, "
            f"invariants={{counts['invariants']}}, fail_closed=true\\n"
            "[llvm2-selftest] native fused callout selftest complete\\n"
            + extra
        )
    def artifact_text(spec):
        mode = {selftest_artifact_mode_literal}
        if mode == "valid":
            return "\\n".join(
                [
                    {flat_primary_rebuild_marker_literal},
                    selftest_text(spec).rstrip(),
                ]
            )
        if mode == "missing_marker":
            return selftest_text(spec)
        if mode == "stale_pre_rebuild":
            return "\\n".join(
                [
                    "[flat_state] flat_state_primary=true: selected promotion",
                    selftest_text(spec).rstrip(),
                    {flat_primary_rebuild_marker_literal},
                    "[llvm2] post-rebuild backend telemetry without selftest markers",
                ]
            )
        raise SystemExit(f"unknown selftest artifact mode: {{mode}}")
    if {write_selftest_artifacts_literal}:
        for row in summary.get("rows", []):
            for run in row.get("llvm2", {{}}).get("runs", []):
                artifact_dir = run.get("artifact_dir")
                if not artifact_dir:
                    continue
                artifact_path = output_dir / artifact_dir
                artifact_path.mkdir(parents=True, exist_ok=True)
                (artifact_path / "stdout.txt").write_text(
                    artifact_text(row["spec"]),
                    encoding="utf-8",
                )
                (artifact_path / "stderr.txt").write_text("", encoding="utf-8")
    (output_dir / "summary.json").write_text(json.dumps(summary), encoding="utf-8")
    raise SystemExit(0)

real_python = os.environ["REAL_PYTHON"]
os.execv(real_python, [real_python] + sys.argv[1:])
""",
        encoding="utf-8",
    )
    shim.chmod(0o755)
    env = os.environ.copy()
    env["PATH"] = f"{tmp_path}{os.pathsep}{env.get('PATH', '')}"
    env["REAL_PYTHON"] = sys.executable
    if policy is not None:
        policy_path = tmp_path / "single_thread_supremacy_gate.json"
        policy_path.write_text(json.dumps(policy), encoding="utf-8")
        env["TLA2_SINGLE_THREAD_SUPREMACY_POLICY_FILE"] = str(policy_path)
    command = [
        "bash",
        str(WRAPPER_PATH),
        "--mode",
        mode,
    ]
    if mode != "enforce":
        command.extend(["--gate-mode", _policy()["final_gate_mode"]])
    command.extend(
        [
            "--runs",
            "3",
            "--output-dir",
            str(tmp_path / "out"),
            "--tla2-bin",
            str(fake_tla2),
        ]
    )
    return subprocess.run(
        command,
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )
