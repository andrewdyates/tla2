# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Focused tests for LLVM2 truth gates in the single-thread benchmark script."""

from __future__ import annotations

import os
import sys
from argparse import Namespace
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))

import benchmark_single_thread_backends_vs_tlc as bench


def _native_fused_execution_fields(
    *,
    mode: str = "invariant_checking",
    invariant_count: int | None = None,
    regular_invariants_checked: bool | None = None,
) -> dict[str, object]:
    fields: dict[str, object] = {
        "compiled_bfs_level_active": True,
        "compiled_bfs_level_loop_started": True,
        "compiled_bfs_level_loop_initial_states": 1,
        "compiled_bfs_level_loop_fused": True,
        "compiled_bfs_levels_completed": 1,
        "compiled_bfs_parents_processed": 1,
        "compiled_bfs_successors_generated": 1,
        "compiled_bfs_total_states": 1,
        "llvm2_native_fused_level_built": True,
        "llvm2_native_fused_level_active": True,
        "llvm2_bfs_level_loop_kind": "native_fused_llvm2_parent_loop",
        "llvm2_native_fused_mode": mode,
    }
    if invariant_count is not None:
        fields["llvm2_native_fused_invariant_count"] = invariant_count
    if regular_invariants_checked is not None:
        fields["llvm2_native_fused_regular_invariants_checked"] = (
            regular_invariants_checked
        )
    return fields


def test_parse_llvm2_telemetry_extracts_compile_bfs_and_fallback_signals() -> None:
    stderr = """
    [llvm2] LLVM2 native compilation enabled (TLA2_LLVM2=1)
    [llvm2] compiling 3 actions (2 invariants, 1 binding specializations) with 4 state variables...
    [llvm2] compiled next-state for action 'A'
    [llvm2] failed to compile action 'B': UnsupportedInst: binding-frame instruction not yet supported in LLVM2 lowering (interpreter fallback permanent for this run)
    [llvm2] compiled invariant 0
    [llvm2] failed to compile invariant 1: LLVM2 IR emission failed: unsupported aggregate lowering
    [llvm2] compilation complete: 2/3 actions, 1/2 invariants compiled in 42ms
    [compiled-bfs] activating compiled BFS loop (TLA2_COMPILED_BFS=1)
    [compiled-bfs] starting compiled BFS level loop (5 initial states in arena, fused=true)
    [flat_state] flat_state_primary=true: all vars scalar, no VIEW, no SYMMETRY
    [flat-frontier] flat_bfs_frontier_active=true: 8 total pushed, 8 flat (100.0%), 0 fallback, 32 bytes/state
    """

    telemetry = bench.parse_llvm2_telemetry("", stderr).to_dict()

    assert telemetry["llvm2_actions_compiled"] == 2, telemetry
    assert telemetry["llvm2_actions_total"] == 3, telemetry
    assert telemetry["llvm2_invariants_compiled"] == 1, telemetry
    assert telemetry["llvm2_invariants_total"] == 2, telemetry
    assert telemetry["compiled_bfs_step_active"] is True, telemetry
    assert telemetry["compiled_bfs_level_active"] is True, telemetry
    assert telemetry["compiled_bfs_level_loop_started"] is True, telemetry
    assert telemetry["compiled_bfs_level_loop_initial_states"] == 5, telemetry
    assert telemetry["compiled_bfs_level_loop_fused"] is True, telemetry
    assert telemetry["llvm2_bfs_level_active"] is False, telemetry
    assert telemetry["llvm2_native_fused_level_active"] is False, telemetry
    assert telemetry["llvm2_native_fused_regular_invariants_checked"] is None, telemetry
    assert telemetry["llvm2_bfs_level_loop_kind"] is None, telemetry
    assert telemetry["flat_state_primary"] is True, telemetry
    assert telemetry["flat_bfs_frontier_active"] is True, telemetry
    assert telemetry["flat_bfs_frontier_fallbacks"] == 0, telemetry
    assert any(
        "failed to compile action 'B'" in item for item in telemetry["fallback_reasons"]
    ), telemetry


def test_parse_llvm2_telemetry_records_compiled_bfs_level_loop_start_from_stdout() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "[compiled-bfs] starting compiled BFS level loop (1,024 initial states in arena, fused=true)",
        "",
    ).to_dict()

    assert telemetry["compiled_bfs_step_active"] is True, telemetry
    assert telemetry["compiled_bfs_level_active"] is True, telemetry
    assert telemetry["compiled_bfs_level_loop_started"] is True, telemetry
    assert telemetry["compiled_bfs_level_loop_initial_states"] == 1024, telemetry
    assert telemetry["compiled_bfs_level_loop_fused"] is True, telemetry


def test_parse_llvm2_telemetry_does_not_infer_level_loop_start_from_active_kv() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "[llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop",
    ).to_dict()

    assert telemetry["compiled_bfs_level_active"] is True, telemetry
    assert telemetry["llvm2_native_fused_level_active"] is True, telemetry
    assert telemetry["llvm2_native_fused_level_built"] is False, telemetry
    assert telemetry["compiled_bfs_level_loop_started"] is False, telemetry
    assert telemetry["compiled_bfs_level_loop_initial_states"] is None, telemetry
    assert telemetry["compiled_bfs_level_loop_fused"] is None, telemetry


def test_parse_llvm2_telemetry_does_not_count_successful_tmir_attempt_as_fallback() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] action 'PickSameColorBlack' has opcodes outside the scalar+state-access set; attempting compile via tMIR anyway
        [llvm2] compiled next-state for action 'PickSameColorBlack'
        """,
    ).to_dict()

    assert telemetry["llvm2_actions_compiled"] == 1, telemetry
    assert telemetry["llvm2_actions_total"] == 1, telemetry
    assert telemetry["fallback_reasons"] == [], telemetry


def test_parse_llvm2_telemetry_records_specialized_wrapper_skip_as_fallback() -> None:
    skip_line = (
        "[llvm2] skipping action 'RecvMsg' as arity-positive wrapper 1; "
        "executable BindingSpec specializations are counted separately"
    )
    telemetry = bench.parse_llvm2_telemetry(
        "",
        f"""
        {skip_line}
        [llvm2] compilation complete: 15/15 actions, 1/3 invariants compiled in 791ms
        """,
    ).to_dict()

    assert telemetry["llvm2_actions_compiled"] == 15, telemetry
    assert telemetry["llvm2_actions_total"] == 15, telemetry
    assert telemetry["fallback_reasons"] == [skip_line], telemetry


def test_run_mode_sanitizes_behavioral_tla2_env(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    command_envs: list[dict[str, str]] = []

    def fake_build_tla2_check_command(
        spec: bench.perf_harness.SpecInfo,
        *,
        binary_path: Path,
        extra_flags: list[str],
        extra_env: dict[str, str],
        workers: int,
        profile_enum: bool,
        profile_eval: bool,
    ) -> bench.perf_harness.CommandSpec:
        assert workers == 1
        assert profile_enum is False
        assert profile_eval is False
        return bench.perf_harness.CommandSpec(
            argv=["/bin/echo", "fake"],
            cwd=tmp_path,
            env=extra_env,
        )

    def fake_run_command(
        command: bench.perf_harness.CommandSpec,
        timeout: int,
    ) -> bench.perf_harness.CommandResult:
        for key in (
            "TLA2_NO_COMPILED_BFS",
            "TLA2_CACHE_DIR",
            "TLA2_TIR_EVAL",
            "TLA2_COMPILED_BFS",
            "TLA2_FLAT_BFS",
            "TLA2_FORCE_Z4",
            "TLA2_USE_Z4",
            "TLA2_DISABLE_HANDLE_STATE",
        ):
            assert key not in os.environ
        command_envs.append(command.env or {})
        return bench.perf_harness.CommandResult(
            argv=command.argv,
            cwd=str(command.cwd),
            returncode=0,
            elapsed_seconds=0.01,
            stdout="States found: 1\nTransitions: 1\n",
            stderr="",
            env_overrides=dict(command.env or {}),
        )

    monkeypatch.setenv("TLA2_NO_COMPILED_BFS", "1")
    monkeypatch.setenv("TLA2_CACHE_DIR", "/ambient/cache")
    monkeypatch.setenv("TLA2_TIR_EVAL", "all")
    monkeypatch.setenv("TLA2_COMPILED_BFS", "1")
    monkeypatch.setenv("TLA2_FLAT_BFS", "1")
    monkeypatch.setenv("TLA2_FORCE_Z4", "1")
    monkeypatch.setenv("TLA2_USE_Z4", "1")
    monkeypatch.setenv("TLA2_DISABLE_HANDLE_STATE", "1")
    monkeypatch.setattr(bench.perf_harness, "build_tla2_check_command", fake_build_tla2_check_command)
    monkeypatch.setattr(bench.perf_harness, "run_command", fake_run_command)

    spec = bench.perf_harness.SpecInfo(
        name="Tiny",
        tla_path="Tiny.tla",
        cfg_path="Tiny.cfg",
        category="unit",
        expected_states=1,
    )
    bench.run_tla2_mode(
        spec,
        mode="interp",
        run_index=1,
        tla2_bin=Path("/tmp/tla2"),
        timeout=5,
        output_dir=tmp_path / "interp",
        common_flags=[],
        env_overrides=None,
    )
    bench.run_tla2_mode(
        spec,
        mode="llvm2",
        run_index=1,
        tla2_bin=Path("/tmp/tla2"),
        timeout=5,
        output_dir=tmp_path / "llvm2",
        common_flags=[],
        env_overrides={"TLA2_CACHE_DIR": "/explicit/cache"},
    )

    assert os.environ["TLA2_NO_COMPILED_BFS"] == "1"
    assert os.environ["TLA2_CACHE_DIR"] == "/ambient/cache"
    assert os.environ["TLA2_TIR_EVAL"] == "all"
    assert os.environ["TLA2_COMPILED_BFS"] == "1"
    assert os.environ["TLA2_FLAT_BFS"] == "1"
    assert os.environ["TLA2_FORCE_Z4"] == "1"
    assert os.environ["TLA2_USE_Z4"] == "1"
    assert os.environ["TLA2_DISABLE_HANDLE_STATE"] == "1"
    assert command_envs[0]["TLA2_AUTO_POR"] == "0"
    assert command_envs[0]["TLA2_BYTECODE_VM"] == "1"
    assert command_envs[1]["TLA2_AUTO_POR"] == "0"
    assert command_envs[1]["TLA2_BYTECODE_VM"] == "1"
    assert command_envs[1]["TLA2_CACHE_DIR"] == "/explicit/cache"


def test_run_mode_parses_llvm2_local_dedup_telemetry(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    def fake_build_tla2_check_command(
        spec: bench.perf_harness.SpecInfo,
        *,
        binary_path: Path,
        extra_flags: list[str],
        extra_env: dict[str, str],
        workers: int,
        profile_enum: bool,
        profile_eval: bool,
    ) -> bench.perf_harness.CommandSpec:
        return bench.perf_harness.CommandSpec(
            argv=["/bin/echo", spec.name],
            cwd=tmp_path,
            env=extra_env,
        )

    def fake_run_command(
        command: bench.perf_harness.CommandSpec,
        timeout: int,
    ) -> bench.perf_harness.CommandResult:
        assert command.env["TLA2_LLVM2"] == "1"
        assert command.env["TLA2_LLVM2_BFS"] == "1"
        assert command.env["TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP"] == "1"
        return bench.perf_harness.CommandResult(
            argv=command.argv,
            cwd=str(command.cwd),
            returncode=0,
            elapsed_seconds=0.01,
            stdout="States found: 10\nTransitions: 20\n",
            stderr=(
                "[llvm2-native-bfs] phase=complete symbol=llvm2_bfs_level "
                "local_dedup=false state_count=18 generated=40 parents_processed=8"
            ),
            env_overrides=dict(command.env or {}),
        )

    monkeypatch.setattr(
        bench.perf_harness,
        "build_tla2_check_command",
        fake_build_tla2_check_command,
    )
    monkeypatch.setattr(bench.perf_harness, "run_command", fake_run_command)
    spec = bench.perf_harness.SpecInfo(
        name="Tiny",
        tla_path="Tiny.tla",
        cfg_path="Tiny.cfg",
        category="unit",
        expected_states=10,
    )

    result = bench.run_tla2_mode(
        spec,
        mode="llvm2",
        run_index=1,
        tla2_bin=Path("/tmp/tla2"),
        timeout=5,
        output_dir=tmp_path / "llvm2",
        common_flags=[],
        env_overrides={"TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP": "1"},
    )

    assert result.llvm2_telemetry is not None
    telemetry = result.llvm2_telemetry.to_dict()
    assert telemetry["llvm2_native_fused_local_dedup"] is False, telemetry
    assert telemetry["llvm2_native_bfs_trace_generated"] == 40, telemetry
    assert telemetry["llvm2_native_bfs_trace_state_count"] == 18, telemetry


def test_stage_coffecan_safety_spec_writes_absolute_safety_only_wrapper(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    examples_dir = tmp_path / "examples"
    coffee_dir = examples_dir / "CoffeeCan"
    coffee_dir.mkdir(parents=True)
    source = coffee_dir / "CoffeeCan.tla"
    source.write_text(
        "---- MODULE CoffeeCan ----\nEXTENDS Naturals\n====\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(bench.perf_harness, "TLAPLUS_EXAMPLES_DIR", examples_dir)
    monkeypatch.chdir(tmp_path)

    spec = bench.stage_coffecan_safety_spec(Path("relative-output-dir"))

    tla_path = Path(spec.tla_path)
    cfg_path = Path(spec.cfg_path)
    assert spec.name == "CoffeeCan1000BeansSafety"
    assert spec.expected_states == 501500
    assert spec.timeout_seconds == 300
    assert tla_path.is_absolute()
    assert cfg_path.is_absolute()
    assert (tla_path.parent / "CoffeeCan.tla").read_text(encoding="utf-8") == (
        source.read_text(encoding="utf-8")
    )
    assert tla_path.read_text(encoding="utf-8") == (
        "---- MODULE CoffeeCanSafetyBench ----\n"
        "VARIABLE can\n\n"
        "INSTANCE CoffeeCan WITH MaxBeanCount <- 1000\n\n"
        "SafetyInit ==\n"
        "    can \\in {c \\in Can : c.black + c.white = 1000}\n\n"
        "====\n"
    )
    assert cfg_path.read_text(encoding="utf-8") == (
        "INIT\n"
        "    SafetyInit\n\n"
        "NEXT\n"
        "    Next\n\n"
        "INVARIANTS\n"
        "    TypeInvariant\n"
    )
    assert "exact-1000-bean initial frontier" in spec.notes
    assert "no temporal properties or fairness" in spec.notes.lower()


def test_resolve_spec_paths_preserves_absolute_specinfo_paths(tmp_path: Path) -> None:
    tla_path = tmp_path / "Generated.tla"
    cfg_path = tmp_path / "Generated.cfg"
    spec = bench.perf_harness.SpecInfo(
        name="Generated",
        tla_path=str(tla_path),
        cfg_path=str(cfg_path),
        category="unit",
        expected_states=1,
    )

    assert bench.perf_harness.resolve_spec_paths(spec) == (tla_path, cfg_path)


def test_resolve_final_specs_attaches_fixed_expected_state_counts(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    catalog = {
        "EWD998Small": bench.perf_harness.SpecInfo(
            name="EWD998Small",
            tla_path="EWD998.tla",
            cfg_path="EWD998Small.cfg",
            category="unit",
        ),
        "MCLamportMutex": bench.perf_harness.SpecInfo(
            name="MCLamportMutex",
            tla_path="MCLamportMutex.tla",
            cfg_path="MCLamportMutex.cfg",
            category="unit",
        ),
    }
    monkeypatch.setattr(bench.perf_harness, "require_spec", catalog.__getitem__)

    assert (
        bench.resolve_benchmark_spec("EWD998Small", tmp_path).expected_states
        == 1520618
    )
    assert (
        bench.resolve_benchmark_spec("MCLamportMutex", tmp_path).expected_states
        == 724274
    )


def test_resolve_final_spec_rejects_conflicting_catalog_expected_state_count(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    monkeypatch.setattr(
        bench.perf_harness,
        "require_spec",
        lambda _name: bench.perf_harness.SpecInfo(
            name="EWD998Small",
            tla_path="EWD998.tla",
            cfg_path="EWD998Small.cfg",
            category="unit",
            expected_states=123,
        ),
    )

    with pytest.raises(ValueError, match="catalog expected_states=123"):
        bench.resolve_benchmark_spec("EWD998Small", tmp_path)


def test_parse_llvm2_telemetry_distinguishes_prototype_and_native_fused_levels() -> None:
    prototype = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] CompiledBfsLevel built (prototype Rust parent loop over LLVM2 action/invariant pointers): 2 action instances, 1 invariants, state_len=3
        [compiled-bfs] starting compiled BFS level loop (5 initial states in arena, fused=true)
        """,
    ).to_dict()
    native = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] CompiledBfsLevel built (invariant-checking native fused LLVM2 parent loop): 2 action instances, 1 invariants, state_len=3
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=invariant_checking llvm2_native_fused_invariant_count=1 llvm2_native_fused_regular_invariants_checked=true
        [compiled-bfs] starting compiled BFS level loop (5 initial states in arena, fused=true)
        """,
    ).to_dict()
    action_only_native = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] CompiledBfsLevel built (action-only native fused LLVM2 parent loop): 2 action instances, 1 invariants, state_len=3
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=action_only llvm2_native_fused_invariant_count=0 llvm2_native_fused_regular_invariants_checked=false
        """,
    ).to_dict()
    generic = bench.parse_llvm2_telemetry(
        "",
        "[compiled-bfs] starting compiled BFS level loop (5 initial states in arena, fused=true)",
    ).to_dict()

    assert prototype["compiled_bfs_level_active"] is True, prototype
    assert prototype["llvm2_bfs_level_active"] is True, prototype
    assert prototype["llvm2_native_fused_level_active"] is False, prototype
    assert prototype["llvm2_native_fused_level_built"] is False, prototype
    assert prototype["llvm2_bfs_level_loop_kind"] == (
        "prototype_rust_parent_loop_over_llvm2_action_invariant_pointers"
    ), prototype

    assert native["compiled_bfs_level_active"] is True, native
    assert native["llvm2_bfs_level_active"] is True, native
    assert native["llvm2_native_fused_level_built"] is True, native
    assert native["llvm2_native_fused_level_active"] is True, native
    assert native["llvm2_native_fused_regular_invariants_checked"] is True, native
    assert native["llvm2_native_fused_mode"] == "invariant_checking", native
    assert native["llvm2_native_fused_invariant_count"] == 1, native
    assert native["llvm2_native_fused_state_len"] == 3, native
    assert native["llvm2_bfs_level_loop_kind"] == "native_fused_llvm2_parent_loop", native

    assert action_only_native["llvm2_native_fused_level_active"] is True, action_only_native
    assert action_only_native["llvm2_native_fused_level_built"] is True, action_only_native
    assert action_only_native["llvm2_native_fused_mode"] == "action_only", action_only_native
    assert action_only_native["llvm2_native_fused_invariant_count"] == 0, action_only_native
    assert action_only_native["llvm2_native_fused_regular_invariants_checked"] is False, (
        action_only_native
    )

    assert generic["compiled_bfs_level_active"] is True, generic
    assert generic["llvm2_bfs_level_active"] is False, generic
    assert generic["llvm2_native_fused_level_built"] is False, generic
    assert generic["llvm2_native_fused_level_active"] is False, generic
    assert generic["llvm2_native_fused_regular_invariants_checked"] is None, generic


def test_parse_llvm2_telemetry_keeps_explicit_native_fused_inactive_sticky() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] llvm2_native_fused_level_active=false
        [llvm2] CompiledBfsLevel built (invariant-checking native fused LLVM2 parent loop): 2 action instances, 1 invariants, state_len=3
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=invariant_checking
        """,
    ).to_dict()

    assert telemetry["llvm2_bfs_level_active"] is True, telemetry
    assert telemetry["llvm2_native_fused_level_built"] is True, telemetry
    assert telemetry["llvm2_bfs_level_loop_kind"] == "native_fused_llvm2_parent_loop", telemetry
    assert telemetry["llvm2_native_fused_level_active"] is False, telemetry


def test_parse_llvm2_telemetry_records_native_fused_state_constraint_count() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] compilation complete: 15/15 actions, 3/3 invariants, 1/1 state constraints compiled in 42ms
        [llvm2] CompiledBfsLevel built (state-constrained native fused LLVM2 parent loop): 15 action instances, 3 invariants, 1 state constraints, state_len=8
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=state_constraint_checking llvm2_native_fused_state_constraint_count=1 llvm2_native_fused_invariant_count=3 llvm2_native_fused_regular_invariants_checked=true
        """,
    ).to_dict()

    assert telemetry["llvm2_actions_compiled"] == 15, telemetry
    assert telemetry["llvm2_actions_total"] == 15, telemetry
    assert telemetry["llvm2_invariants_compiled"] == 3, telemetry
    assert telemetry["llvm2_invariants_total"] == 3, telemetry
    assert telemetry["llvm2_state_constraints_compiled"] == 1, telemetry
    assert telemetry["llvm2_state_constraints_total"] == 1, telemetry
    assert telemetry["llvm2_native_fused_level_built"] is True, telemetry
    assert telemetry["llvm2_native_fused_level_active"] is True, telemetry
    assert telemetry["llvm2_native_fused_mode"] == "state_constraint_checking", telemetry
    assert telemetry["llvm2_native_fused_state_constraint_count"] == 1, telemetry
    assert telemetry["llvm2_native_fused_state_len"] == 8, telemetry
    assert telemetry["llvm2_native_fused_invariant_count"] == 3, telemetry
    assert telemetry["llvm2_native_fused_regular_invariants_checked"] is True, telemetry


def test_parse_llvm2_telemetry_records_native_bfs_local_dedup_trace() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2-native-bfs] phase=complete symbol=llvm2_bfs_level returned_status=0 returned_status_kind=Success written_status=0 written_status_kind=Some(Success) state_len=15 parent_count=8 scratch_len=128 actions=15 state_constraints=1 invariants=3 local_dedup=false local_fp_set=false requested_successor_capacity=128 state_capacity=128 state_count=42 generated=99 parents_processed=8
        [llvm2-native-bfs] phase=complete symbol=llvm2_bfs_level returned_status=0 returned_status_kind=Success written_status=0 written_status_kind=Some(Success) state_len=15 parent_count=8 scratch_len=128 actions=15 state_constraints=1 invariants=3 local_dedup=false local_fp_set=false requested_successor_capacity=128 state_capacity=128 state_count=43 generated=100 parents_processed=8
        """,
    ).to_dict()

    assert telemetry["llvm2_native_fused_local_dedup"] is False, telemetry
    assert telemetry["llvm2_native_bfs_trace_generated"] == 100, telemetry
    assert telemetry["llvm2_native_bfs_trace_state_count"] == 43, telemetry
    assert telemetry["llvm2_native_bfs_trace_parents_processed"] == 8, telemetry


def test_parse_llvm2_telemetry_requires_explicit_zero_fallback_flat_frontier() -> None:
    inactive = bench.parse_llvm2_telemetry(
        "",
        "[flat-frontier] flat_bfs_frontier_active=false: 0 total pushed, 0 flat (0.0%), 0 fallback, 24 bytes/state",
    ).to_dict()
    active = bench.parse_llvm2_telemetry(
        "",
        "[flat-frontier] flat_bfs_frontier_active=true: 3 total pushed, 3 flat (100.0%), 0 fallback, 24 bytes/state",
    ).to_dict()
    ambiguous = bench.parse_llvm2_telemetry(
        "",
        "[flat-frontier] 3 total pushed, 3 flat (100.0%), 0 fallback, 24 bytes/state",
    ).to_dict()
    fallback = bench.parse_llvm2_telemetry(
        "",
        "[flat-frontier] flat_bfs_frontier_active=true: 3 total pushed, 2 flat (66.7%), 1 fallback, 24 bytes/state",
    ).to_dict()
    missing_fallback_count = bench.parse_llvm2_telemetry(
        "",
        "[flat-frontier] flat_bfs_frontier_active=true: active but count omitted",
    ).to_dict()

    assert inactive["flat_bfs_frontier_active"] is False, inactive
    assert inactive["flat_bfs_frontier_fallbacks"] == 0, inactive
    assert active["flat_bfs_frontier_active"] is True, active
    assert active["flat_bfs_frontier_fallbacks"] == 0, active
    assert ambiguous["flat_bfs_frontier_active"] is None, ambiguous
    assert ambiguous["flat_bfs_frontier_fallbacks"] == 0, ambiguous
    assert fallback["flat_bfs_frontier_active"] is False, fallback
    assert fallback["flat_bfs_frontier_fallbacks"] == 1, fallback
    assert fallback["fallback_reasons"] == [
        "[flat-frontier] flat_bfs_frontier_active=true: 3 total pushed, 2 flat (66.7%), 1 fallback, 24 bytes/state"
    ], fallback
    assert missing_fallback_count["flat_bfs_frontier_active"] is False, missing_fallback_count
    assert missing_fallback_count["flat_bfs_frontier_fallbacks"] is None, missing_fallback_count


def test_parse_llvm2_telemetry_does_not_infer_flat_primary_from_flat_bfs() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "[flat-bfs] active (auto-detected (all vars scalar)): 2 slots/state, 16 bytes/state, fully_flat=true",
    ).to_dict()

    assert telemetry["flat_state_primary"] is None, telemetry


def test_parse_llvm2_telemetry_keeps_flat_primary_false_sticky() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [flat_state] flat_state_primary=false: roundtrip_ok=true, fully_flat=true, flat_primary_safe=false
        [flat_state] flat_state_primary=true: roundtrip_ok=true, fully_flat=true, flat_primary_safe=true
        [flat-frontier] flat_bfs_frontier_active=false: 1 total pushed, 0 flat (0.0%), 1 fallback, 24 bytes/state
        [flat-frontier] flat_bfs_frontier_active=true: 1 total pushed, 1 flat (100.0%), 0 fallback, 24 bytes/state
        """,
    ).to_dict()

    assert telemetry["flat_state_primary"] is False, telemetry
    assert telemetry["flat_bfs_frontier_active"] is False, telemetry
    assert telemetry["flat_bfs_frontier_fallbacks"] == 1, telemetry


def test_parse_llvm2_telemetry_uses_latest_flat_primary_rebuild_segment() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                "[flat_state] flat_state_primary=true: stale promotion",
                "[llvm2] llvm2_native_fused_level_active=false",
                "[llvm2] failed to compile action 'Old': unsupported opcode",
                "[flat_state] flat_state_primary=true: selected promotion",
                (
                    f"{bench.FLAT_PRIMARY_REBUILD_MARKER}, flat_slots=15, logical_vars=5, "
                    "compiled_bfs_step=True, compiled_bfs_level=True, "
                    "llvm2_cache=True, llvm2_build_stats=True"
                ),
                "[llvm2] compilation complete: 2/2 actions, 1/1 invariants compiled in 42ms",
                (
                    "[llvm2] CompiledBfsLevel built "
                    "(invariant-checking native fused LLVM2 parent loop): "
                    "2 action instances, 1 invariants, state_len=3"
                ),
                (
                    "[llvm2] llvm2_bfs_level_active=true "
                    "llvm2_native_fused_level_active=true "
                    "llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop "
                    "llvm2_native_fused_mode=invariant_checking "
                    "llvm2_native_fused_invariant_count=1 "
                    "llvm2_native_fused_regular_invariants_checked=true"
                ),
                (
                    "[flat-frontier] flat_bfs_frontier_active=true: "
                    "8 total pushed, 8 flat (100.0%), 0 fallback, 32 bytes/state"
                ),
            ]
        ),
    ).to_dict()

    assert telemetry["flat_state_primary"] is True, telemetry
    assert telemetry["llvm2_actions_compiled"] == 2, telemetry
    assert telemetry["llvm2_actions_total"] == 2, telemetry
    assert telemetry["llvm2_native_fused_level_built"] is True, telemetry
    assert telemetry["llvm2_native_fused_level_active"] is True, telemetry
    assert telemetry["llvm2_bfs_level_loop_kind"] == "native_fused_llvm2_parent_loop", telemetry
    assert telemetry["llvm2_native_fused_mode"] == "invariant_checking", telemetry
    assert telemetry["llvm2_native_fused_invariant_count"] == 1, telemetry
    assert telemetry["llvm2_native_fused_regular_invariants_checked"] is True, telemetry
    assert telemetry["flat_bfs_frontier_active"] is True, telemetry
    assert telemetry["flat_bfs_frontier_fallbacks"] == 0, telemetry
    assert telemetry["fallback_reasons"] == [], telemetry


def test_parse_llvm2_telemetry_ignores_pre_rebuild_native_fused_success() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                "[flat_state] flat_state_primary=true: selected promotion",
                (
                    "[llvm2] compilation complete: 4/4 actions, 3/3 invariants, "
                    "1/1 state constraints compiled in 42ms"
                ),
                (
                    "[llvm2] CompiledBfsLevel built "
                    "(state-constrained native fused LLVM2 parent loop): "
                    "4 action instances, 3 invariants, state_len=4"
                ),
                (
                    "[llvm2] llvm2_bfs_level_active=true "
                    "llvm2_native_fused_level_active=true "
                    "llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop "
                    "llvm2_native_fused_mode=state_constraint_checking "
                    "llvm2_native_fused_invariant_count=3 "
                    "llvm2_native_fused_state_constraint_count=1 "
                    "llvm2_native_fused_regular_invariants_checked=true"
                ),
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                (
                    "[llvm2] compilation complete: 3/4 actions, 2/3 invariants, "
                    "0/1 state constraints compiled in 42ms"
                ),
                "[llvm2] llvm2_native_fused_level_active=false",
            ]
        ),
    ).to_dict()

    assert telemetry["flat_state_primary"] is True, telemetry
    assert telemetry["llvm2_actions_compiled"] == 3, telemetry
    assert telemetry["llvm2_actions_total"] == 4, telemetry
    assert telemetry["llvm2_invariants_compiled"] == 2, telemetry
    assert telemetry["llvm2_invariants_total"] == 3, telemetry
    assert telemetry["llvm2_state_constraints_compiled"] == 0, telemetry
    assert telemetry["llvm2_state_constraints_total"] == 1, telemetry
    assert telemetry["llvm2_native_fused_level_built"] is False, telemetry
    assert telemetry["llvm2_native_fused_level_active"] is False, telemetry
    assert telemetry["llvm2_bfs_level_loop_kind"] is None, telemetry
    assert telemetry["llvm2_native_fused_mode"] is None, telemetry
    assert telemetry["llvm2_native_fused_invariant_count"] is None, telemetry
    assert telemetry["llvm2_native_fused_state_constraint_count"] is None, telemetry
    assert telemetry["llvm2_native_fused_regular_invariants_checked"] is None, telemetry


def test_parse_llvm2_telemetry_keeps_post_marker_fallback_errors() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                "[flat_state] flat_state_primary=true: selected promotion",
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                "[llvm2] compilation complete: 2/2 actions, 1/1 invariants compiled in 42ms",
                "[compiled-bfs] fused level error: compiled BFS step runtime error -- falling back to per-parent step",
            ]
        ),
    ).to_dict()

    assert telemetry["flat_state_primary"] is True, telemetry
    assert telemetry["fallback_reasons"] == [
        "[compiled-bfs] fused level error: compiled BFS step runtime error -- falling back to per-parent step"
    ], telemetry


def test_parse_llvm2_telemetry_keeps_post_marker_llvm2_compile_failures() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                "[flat_state] flat_state_primary=true: selected promotion",
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                "[llvm2] failed to compile action 'New': unsupported opcode",
                "[llvm2] compilation complete: 1/2 actions, 1/1 invariants compiled in 42ms",
            ]
        ),
    ).to_dict()

    assert telemetry["flat_state_primary"] is True, telemetry
    assert telemetry["llvm2_actions_compiled"] == 1, telemetry
    assert telemetry["llvm2_actions_total"] == 2, telemetry
    assert telemetry["fallback_reasons"] == [
        "[llvm2] failed to compile action 'New': unsupported opcode"
    ], telemetry


def test_parse_llvm2_telemetry_keeps_flat_primary_false_after_rebuild_marker() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                "[flat_state] flat_state_primary=true: selected promotion",
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                "[flat_state] flat_state_primary=false: validation failed after rebuild",
                "[llvm2] compilation complete: 2/2 actions, 1/1 invariants compiled in 42ms",
            ]
        ),
    ).to_dict()

    assert telemetry["flat_state_primary"] is False, telemetry
    assert telemetry["llvm2_actions_compiled"] == 2, telemetry
    assert telemetry["llvm2_actions_total"] == 2, telemetry


def test_parse_llvm2_telemetry_uses_last_rebuild_marker_only() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                "[flat_state] flat_state_primary=true: stale promotion",
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                "[llvm2] failed to compile action 'Old': unsupported opcode",
                "[flat_state] flat_state_primary=true: final promotion",
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                "[llvm2] compilation complete: 4/4 actions, 2/2 invariants compiled in 42ms",
            ]
        ),
    ).to_dict()

    assert telemetry["flat_state_primary"] is True, telemetry
    assert telemetry["llvm2_actions_compiled"] == 4, telemetry
    assert telemetry["llvm2_actions_total"] == 4, telemetry
    assert telemetry["fallback_reasons"] == [], telemetry


def test_parse_llvm2_telemetry_does_not_infer_flat_primary_from_marker_only() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                "[llvm2] failed to compile action 'Old': unsupported opcode",
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                "[llvm2] compilation complete: 4/4 actions, 2/2 invariants compiled in 42ms",
            ]
        ),
    ).to_dict()

    assert telemetry["flat_state_primary"] is None, telemetry
    assert telemetry["llvm2_actions_compiled"] == 4, telemetry
    assert telemetry["llvm2_actions_total"] == 4, telemetry
    assert telemetry["fallback_reasons"] == [], telemetry


def test_parse_llvm2_telemetry_records_zero_action_skip() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "[llvm2] no safe action bytecodes available -- skipping LLVM2 compilation\n",
    ).to_dict()

    assert telemetry["llvm2_actions_compiled"] == 0, telemetry
    assert telemetry["llvm2_actions_total"] == 0, telemetry


def test_parse_llvm2_telemetry_ignores_zero_failed_summary_lines() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "[llvm2] invariant bytecode: 3/3 invariants compiled (0 failed)\n",
    ).to_dict()
    failed = bench.parse_llvm2_telemetry(
        "",
        "[llvm2] invariant bytecode: 2/3 invariants compiled (1 failed)\n",
    ).to_dict()

    assert telemetry["fallback_reasons"] == [], telemetry
    assert failed["fallback_reasons"] == [
        "[llvm2] invariant bytecode: 2/3 invariants compiled (1 failed)"
    ], failed


def test_parse_llvm2_telemetry_records_native_fused_invariant_fallback_lines() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "[llvm2] invariant-checking native fused CompiledBfsLevel unavailable, falling back to action-only native/prototype: linker reported missing invariant thunk\n",
    ).to_dict()

    assert telemetry["fallback_reasons"] == [
        "[llvm2] invariant-checking native fused CompiledBfsLevel unavailable, falling back to action-only native/prototype: linker reported missing invariant thunk"
    ], telemetry


def test_parse_llvm2_telemetry_records_compiled_bfs_runtime_fallback_errors() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [compiled-bfs] fused level error: compiled BFS step runtime error -- falling back to per-parent step
        [compiled-bfs] step error at depth 0, parent 0: compiled BFS step runtime error -- disabling
        [compiled-bfs] compiled BFS disabled: frontier contains non-flat fallback entries
        [compiled-bfs] compiled BFS step available but not enabled. TLA2_COMPILED_BFS=0
        [compiled-bfs] fused level skipped: state constraints require LLVM2 native fused constraint support (first state constraint: StateConstraint)
        """,
    ).to_dict()

    assert telemetry["fallback_reasons"] == [
        "[compiled-bfs] fused level error: compiled BFS step runtime error -- falling back to per-parent step",
        "[compiled-bfs] step error at depth 0, parent 0: compiled BFS step runtime error -- disabling",
        "[compiled-bfs] compiled BFS disabled: frontier contains non-flat fallback entries",
        "[compiled-bfs] compiled BFS step available but not enabled. TLA2_COMPILED_BFS=0",
        "[compiled-bfs] fused level skipped: state constraints require LLVM2 native fused constraint support (first state constraint: StateConstraint)",
    ], telemetry


def test_parse_llvm2_telemetry_records_state_constraint_step_skip_reason() -> None:
    line = (
        "[llvm2] CompiledBfsStep not eligible: "
        "state constraints require native fused constraint pruning "
        "(first state constraint: StateConstraint)"
    )

    telemetry = bench.parse_llvm2_telemetry("", line).to_dict()

    assert telemetry["fallback_reasons"] == [line], telemetry


def _state_constrained_native_fused_success_text(*extra_lines: str) -> str:
    return "\n".join(
        [
            (
                "[llvm2] compilation complete: 4/4 actions, 3/3 invariants, "
                "1/1 state constraints compiled in 42ms"
            ),
            (
                "[llvm2] CompiledBfsLevel built "
                "(state-constrained native fused LLVM2 parent loop): "
                "4 action instances, 3 invariants, 1 state constraints, state_len=15"
            ),
            (
                "[llvm2] llvm2_bfs_level_active=true "
                "llvm2_native_fused_level_active=true "
                "llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop "
                "llvm2_native_fused_mode=state_constraint_checking "
                "llvm2_native_fused_invariant_count=3 "
                "llvm2_native_fused_state_constraint_count=1 "
                "llvm2_native_fused_regular_invariants_checked=true"
            ),
            "[flat_state] flat_state_primary=true: all vars scalar, no VIEW, no SYMMETRY",
            (
                "[flat-frontier] flat_bfs_frontier_active=true: "
                "2 total pushed, 2 flat (100.0%), 0 fallback, 32 bytes/state"
            ),
            "[compiled-bfs] starting compiled BFS level loop (1 initial states in arena, fused=true)",
            "[compiled-bfs] completed: 1 levels, 1 parents, 1 generated, 0 new, 2 total states",
            *extra_lines,
        ]
    )


def test_parse_llvm2_telemetry_keeps_state_constraint_native_fused_skip_diagnostics() -> None:
    step_skip = (
        "[llvm2] CompiledBfsStep not eligible: "
        "state constraints require native fused constraint pruning "
        "(first state constraint: StateConstraint)"
    )
    fused_skip = (
        "[compiled-bfs] fused level skipped: state constraints require LLVM2 "
        "native fused constraint support (first state constraint: StateConstraint)"
    )
    stale_failure = "[llvm2] failed to compile action 'Old': unsupported opcode"

    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                stale_failure,
                "[flat_state] flat_state_primary=true: selected promotion",
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                _state_constrained_native_fused_success_text(
                    fused_skip,
                    step_skip,
                    (
                        "[llvm2-selftest] prepared native fused callout selftest: "
                        "actions=4, state_constraints=1, invariants=3, "
                        "missing_expected=0, fail_closed=true"
                    ),
                    (
                        "[llvm2-selftest] running native fused callout selftest on first "
                        "real parent: state_len=15, actions=4, state_constraints=1, "
                        "invariants=3, fail_closed=true"
                    ),
                    "[llvm2-selftest] native fused callout selftest complete",
                ),
            ]
        ),
    ).to_dict()

    assert telemetry["llvm2_native_fused_mode"] == "state_constraint_checking", telemetry
    assert telemetry["llvm2_native_fused_state_constraint_count"] == 1, telemetry
    assert telemetry["llvm2_state_constraints_compiled"] == 1, telemetry
    assert telemetry["llvm2_state_constraints_total"] == 1, telemetry
    assert telemetry["fallback_reasons"] == [fused_skip, step_skip], telemetry
    assert stale_failure not in telemetry["fallback_reasons"], telemetry

    row = {
        "spec": "EWD998Small",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_compiled_invariants=True,
            require_llvm2_native_fused_level=True,
            require_no_llvm2_fallbacks=True,
        ),
    )

    assert failures == [], failures


def test_parse_llvm2_telemetry_keeps_true_runtime_markers_after_benign_state_constraint_diagnostics() -> None:
    step_skip = (
        "[llvm2] CompiledBfsStep not eligible: "
        "state constraints require native fused constraint pruning "
        "(first state constraint: StateConstraint)"
    )
    selftest_failure = (
        "[llvm2-selftest] native fused callout selftest failed: "
        "state_constraint callout runtime_error index=0 symbol=sc name=StateConstraint"
    )
    compiled_bfs_error = (
        "[compiled-bfs] fused level error: compiled BFS step runtime error -- "
        "falling back to per-parent step"
    )
    telemetry = bench.parse_llvm2_telemetry(
        "",
        _state_constrained_native_fused_success_text(
            step_skip,
            selftest_failure,
            compiled_bfs_error,
        ),
    ).to_dict()

    assert telemetry["fallback_reasons"] == [
        step_skip,
        selftest_failure,
        compiled_bfs_error,
    ], telemetry

    row = {
        "spec": "EWD998Small",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )

    assert any(
        "compiled BFS runtime fallback/error reasons observed" in failure
        for failure in failures
    ), failures
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures


def test_parse_llvm2_telemetry_marks_truncated_fallback_reasons() -> None:
    lines = "\n".join(
        f"[llvm2] failed to compile action 'A{i}': unsupported opcode {i}"
        for i in range(bench.MAX_FALLBACK_REASONS + 1)
    )

    telemetry = bench.parse_llvm2_telemetry("", lines).to_dict()

    assert len(telemetry["fallback_reasons"]) == bench.MAX_FALLBACK_REASONS, telemetry
    assert telemetry["fallback_reasons"][-1] == bench.TRUNCATED_FALLBACK_REASON, telemetry


def test_parse_llvm2_telemetry_records_compiled_bfs_completion_work_counts() -> None:
    zero = bench.parse_llvm2_telemetry(
        "",
        "[compiled-bfs] completed: 0 levels, 0 parents, 0 generated, 0 new, 192 total states",
    ).to_dict()
    nonzero = bench.parse_llvm2_telemetry(
        "",
        "[compiled-bfs] completed: 3 levels, 14 parents, 42 generated, 17 new, 209 total states",
    ).to_dict()

    assert zero["compiled_bfs_step_active"] is True, zero
    assert zero["compiled_bfs_levels_completed"] == 0, zero
    assert zero["compiled_bfs_parents_processed"] == 0, zero
    assert zero["compiled_bfs_successors_generated"] == 0, zero
    assert zero["compiled_bfs_successors_new"] == 0, zero
    assert zero["compiled_bfs_total_states"] == 192, zero
    assert zero["compiled_bfs_zero_work"] is True, zero
    assert zero["fallback_reasons"] == [], zero

    assert nonzero["compiled_bfs_step_active"] is True, nonzero
    assert nonzero["compiled_bfs_levels_completed"] == 3, nonzero
    assert nonzero["compiled_bfs_parents_processed"] == 14, nonzero
    assert nonzero["compiled_bfs_successors_generated"] == 42, nonzero
    assert nonzero["compiled_bfs_successors_new"] == 17, nonzero
    assert nonzero["compiled_bfs_total_states"] == 209, nonzero
    assert nonzero["compiled_bfs_zero_work"] is False, nonzero
    assert nonzero["fallback_reasons"] == [], nonzero


def test_parse_llvm2_telemetry_records_compiled_bfs_execution_time() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        (
            "[compiled-bfs] completed: 3 levels, 14 parents, 42 generated, "
            "17 new, 209 total states, execution_time_ns=123456789, "
            "execution_time_seconds=0.123457"
        ),
    ).to_dict()

    assert telemetry["compiled_bfs_execution_nanos"] == 123456789, telemetry
    assert telemetry["compiled_bfs_execution_seconds"] == pytest.approx(
        0.123457
    ), telemetry


def test_parse_llvm2_telemetry_derives_execution_seconds_from_nanos() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        (
            "[compiled-bfs] completed: 1 levels, 1 parents, 1 generated, "
            "1 new, 2 total states, execution_time_ns=250000000, "
            "execution_time_seconds=0.000000"
        ),
    ).to_dict()

    assert telemetry["compiled_bfs_execution_nanos"] == 250000000, telemetry
    assert telemetry["compiled_bfs_execution_seconds"] == pytest.approx(0.25), telemetry


def test_parse_llvm2_telemetry_ignores_stray_execution_time_after_rebuild() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        "\n".join(
            [
                "[flat_state] flat_state_primary=true: roundtrip_ok=true",
                bench.FLAT_PRIMARY_REBUILD_MARKER,
                (
                    "[compiled-bfs] completed: 1 levels, 1 parents, 1 generated, "
                    "1 new, 2 total states"
                ),
                "unrelated execution_time_ns=123456789 execution_time_seconds=0.123457",
            ]
        ),
    ).to_dict()

    assert telemetry["compiled_bfs_execution_nanos"] is None, telemetry
    assert telemetry["compiled_bfs_execution_seconds"] is None, telemetry


def test_aggregate_llvm2_telemetry_uses_worst_observed_coverage() -> None:
    runs = [
        _run(
            1,
            bench.Llvm2Telemetry(
                llvm2_actions_compiled=2,
                llvm2_actions_total=2,
                llvm2_invariants_compiled=1,
                llvm2_invariants_total=1,
                compiled_bfs_step_active=True,
                compiled_bfs_level_active=False,
                compiled_bfs_level_loop_started=True,
                compiled_bfs_level_loop_initial_states=1,
                compiled_bfs_level_loop_fused=True,
                compiled_bfs_execution_nanos=20_000_000,
                compiled_bfs_execution_seconds=0.02,
                flat_state_primary=True,
                flat_bfs_frontier_active=True,
                fallback_reasons=[],
            ),
        ),
        _run(
            2,
            bench.Llvm2Telemetry(
                llvm2_actions_compiled=1,
                llvm2_actions_total=2,
                llvm2_invariants_compiled=0,
                llvm2_invariants_total=1,
                compiled_bfs_step_active=False,
                compiled_bfs_level_active=False,
                compiled_bfs_execution_nanos=10_000_000,
                compiled_bfs_execution_seconds=0.01,
                flat_state_primary=False,
                flat_bfs_frontier_active=True,
                fallback_reasons=["[llvm2] failed to compile action 'B': unsupported"],
            ),
        ),
    ]

    summary = bench.aggregate_mode(runs)
    telemetry = summary["telemetry"]

    assert summary["execution_median_seconds"] == pytest.approx(0.015), summary
    assert telemetry["llvm2_actions_compiled"] == 1, telemetry
    assert telemetry["llvm2_actions_total"] == 2, telemetry
    assert telemetry["llvm2_invariants_compiled"] == 0, telemetry
    assert telemetry["compiled_bfs_step_active"] is False, telemetry
    assert telemetry["runs_with_compiled_bfs_step_active"] == 1, telemetry
    assert telemetry["compiled_bfs_level_loop_started"] is False, telemetry
    assert telemetry["runs_with_compiled_bfs_level_loop_started"] == 1, telemetry
    assert telemetry["flat_state_primary"] is False, telemetry
    assert telemetry["llvm2_native_fused_level_active"] is False, telemetry
    assert telemetry["runs_with_llvm2_native_fused_level_active"] == 0, telemetry
    assert telemetry["llvm2_native_fused_regular_invariants_checked"] is False, telemetry
    assert telemetry["runs_with_llvm2_native_fused_regular_invariants_checked"] == 0, telemetry
    assert telemetry["compiled_bfs_execution_nanos"] == 20_000_000, telemetry
    assert telemetry["compiled_bfs_execution_seconds"] == pytest.approx(0.02), telemetry
    assert telemetry["runs_with_compiled_bfs_execution_timing"] == 2, telemetry
    assert telemetry["fallback_reasons"] == [
        "[llvm2] failed to compile action 'B': unsupported"
    ], telemetry


def test_aggregate_llvm2_telemetry_rejects_bool_execution_timing() -> None:
    telemetry = bench.aggregate_llvm2_telemetry(
        [
            _run(
                1,
                bench.Llvm2Telemetry(
                    compiled_bfs_execution_nanos=True,
                    compiled_bfs_execution_seconds=True,
                ),
            )
        ]
    )

    assert telemetry is not None
    assert telemetry["compiled_bfs_execution_nanos"] is None, telemetry
    assert telemetry["compiled_bfs_execution_seconds"] is None, telemetry
    assert telemetry["runs_with_compiled_bfs_execution_timing"] == 0, telemetry


def test_aggregate_llvm2_telemetry_requires_mode_on_every_native_run() -> None:
    runs = [
        _run(
            1,
            bench.Llvm2Telemetry(
                llvm2_native_fused_level_active=True,
                llvm2_native_fused_mode="action_only",
                llvm2_native_fused_invariant_count=0,
                fallback_reasons=[],
            ),
        ),
        _run(
            2,
            bench.Llvm2Telemetry(
                llvm2_native_fused_level_active=True,
                fallback_reasons=[],
            ),
        ),
    ]

    telemetry = bench.aggregate_mode(runs)["telemetry"]

    assert telemetry["llvm2_native_fused_mode"] is None, telemetry
    assert telemetry["llvm2_native_fused_invariant_count"] is None, telemetry


def test_aggregate_llvm2_telemetry_preserves_state_constraint_counts() -> None:
    runs = [
        _run(
            1,
            bench.Llvm2Telemetry(
                llvm2_state_constraints_compiled=1,
                llvm2_state_constraints_total=1,
                llvm2_native_fused_level_active=True,
                llvm2_native_fused_mode="state_constraint_checking",
                llvm2_native_fused_state_constraint_count=1,
                fallback_reasons=[],
            ),
        ),
        _run(
            2,
            bench.Llvm2Telemetry(
                llvm2_state_constraints_compiled=1,
                llvm2_state_constraints_total=1,
                llvm2_native_fused_level_active=True,
                llvm2_native_fused_mode="state_constraint_checking",
                llvm2_native_fused_state_constraint_count=1,
                fallback_reasons=[],
            ),
        ),
    ]

    telemetry = bench.aggregate_mode(runs)["telemetry"]

    assert telemetry["llvm2_state_constraints_compiled"] == 1, telemetry
    assert telemetry["llvm2_state_constraints_total"] == 1, telemetry
    assert telemetry["llvm2_native_fused_state_constraint_count"] == 1, telemetry
    assert telemetry["runs_with_llvm2_native_fused_state_constraints"] == 2, telemetry


def test_aggregate_llvm2_telemetry_preserves_unknown_flat_layout_evidence() -> None:
    runs = [
        _run(
            1,
            bench.Llvm2Telemetry(
                flat_state_primary=True,
                flat_bfs_frontier_active=True,
                flat_bfs_frontier_fallbacks=0,
                fallback_reasons=[],
            ),
        ),
        _run(2, bench.Llvm2Telemetry(fallback_reasons=[])),
    ]

    telemetry = bench.aggregate_mode(runs)["telemetry"]

    assert telemetry["flat_state_primary"] is None, telemetry
    assert telemetry["flat_bfs_frontier_active"] is None, telemetry
    assert telemetry["flat_bfs_frontier_fallbacks"] == 0, telemetry

    runs[0].llvm2_telemetry.flat_state_primary = None
    runs[0].llvm2_telemetry.flat_bfs_frontier_active = None
    telemetry = bench.aggregate_mode(runs)["telemetry"]

    assert telemetry["flat_state_primary"] is None, telemetry
    assert telemetry["flat_bfs_frontier_active"] is None, telemetry

    runs[0].llvm2_telemetry.flat_state_primary = True
    runs[0].llvm2_telemetry.flat_bfs_frontier_active = True
    runs[1].llvm2_telemetry.flat_state_primary = False
    runs[1].llvm2_telemetry.flat_bfs_frontier_active = False
    telemetry = bench.aggregate_mode(runs)["telemetry"]

    assert telemetry["flat_state_primary"] is False, telemetry
    assert telemetry["flat_bfs_frontier_active"] is False, telemetry

    runs[0].llvm2_telemetry.flat_state_primary = None
    runs[0].llvm2_telemetry.flat_bfs_frontier_active = None
    telemetry = bench.aggregate_mode(runs)["telemetry"]

    assert telemetry["flat_state_primary"] is False, telemetry
    assert telemetry["flat_bfs_frontier_active"] is False, telemetry

    for run in runs:
        run.llvm2_telemetry.flat_state_primary = True
        run.llvm2_telemetry.flat_bfs_frontier_active = True
    telemetry = bench.aggregate_mode(runs)["telemetry"]

    assert telemetry["flat_state_primary"] is True, telemetry
    assert telemetry["flat_bfs_frontier_active"] is True, telemetry


def test_summarize_spec_requires_fixed_expected_states_not_just_tlc_parity() -> None:
    spec = bench.perf_harness.SpecInfo(
        name="TinySpec",
        tla_path="Tiny.tla",
        cfg_path="Tiny.cfg",
        category="unit",
        expected_states=10,
    )
    tlc_runs = [_tlc_run(states_found=9)]
    interp_runs = [_mode_run("interp", states_found=9)]
    llvm2_runs = [
        _mode_run(
            "llvm2",
            states_found=9,
            telemetry=bench.Llvm2Telemetry(fallback_reasons=[]),
        )
    ]

    row = bench.summarize_spec(spec, interp_runs, llvm2_runs, tlc_runs)

    assert row["tlc"]["state_values"] == [9], row
    assert row["interp"]["state_values"] == [9], row
    assert row["llvm2"]["state_values"] == [9], row
    assert row["tlc"]["expected_states"] == 10, row
    assert row["tlc"]["expected_states_match"] is False, row
    assert row["interp"]["expected_states_match"] is False, row
    assert row["llvm2"]["expected_states_match"] is False, row
    assert row["parity_interp_vs_tlc"] is False, row
    assert row["parity_llvm2_vs_tlc"] is False, row

    tlc_runs[0].states_found = 10
    interp_runs[0].states_found = 10
    llvm2_runs[0].states_found = 10
    row = bench.summarize_spec(spec, interp_runs, llvm2_runs, tlc_runs)

    assert row["tlc"]["expected_states_match"] is True, row
    assert row["interp"]["expected_states_match"] is True, row
    assert row["llvm2"]["expected_states_match"] is True, row
    assert row["parity_interp_vs_tlc"] is True, row
    assert row["parity_llvm2_vs_tlc"] is True, row


def test_summarize_spec_reports_llvm2_execution_speedup_separately() -> None:
    spec = bench.perf_harness.SpecInfo(
        name="TinySpec",
        tla_path="Tiny.tla",
        cfg_path="Tiny.cfg",
        category="unit",
        expected_states=10,
    )
    tlc_runs = [_tlc_run(states_found=10, elapsed_seconds=3.0)]
    interp_runs = [_mode_run("interp", states_found=10, elapsed_seconds=2.0)]
    llvm2_runs = [
        _mode_run(
            "llvm2",
            states_found=10,
            elapsed_seconds=4.0,
            telemetry=bench.Llvm2Telemetry(
                compiled_bfs_execution_nanos=1_500_000_000,
                fallback_reasons=[],
            ),
        )
    ]

    row = bench.summarize_spec(spec, interp_runs, llvm2_runs, tlc_runs)

    assert row["llvm2"]["median_seconds"] == pytest.approx(4.0), row
    assert row["llvm2"]["execution_median_seconds"] == pytest.approx(1.5), row
    assert row["speedup_llvm2_vs_tlc"] == pytest.approx(0.75), row
    assert row["speedup_llvm2_execution_vs_tlc"] == pytest.approx(2.0), row


def test_local_dedup_isolation_cli_flag_is_removed() -> None:
    parser = bench.build_cli()

    with pytest.raises(SystemExit):
        parser.parse_args(["--local-dedup-isolation"])


def test_summarize_spec_serializes_tlc_generated_state_counts() -> None:
    spec = bench.perf_harness.SpecInfo(
        name="TinySpec",
        tla_path="Tiny.tla",
        cfg_path="Tiny.cfg",
        category="unit",
        expected_states=10,
    )
    tlc_runs = [
        _tlc_run(states_found=10, states_generated=27),
        _tlc_run(states_found=10, states_generated=28),
    ]
    interp_runs = [_mode_run("interp", states_found=10)]
    llvm2_runs = [
        _mode_run(
            "llvm2",
            states_found=10,
            telemetry=bench.Llvm2Telemetry(fallback_reasons=[]),
        )
    ]

    row = bench.summarize_spec(spec, interp_runs, llvm2_runs, tlc_runs)

    assert [run["states_generated"] for run in row["tlc"]["runs"]] == [27, 28], row
    assert [run["transitions"] for run in row["tlc"]["runs"]] == [None, None], row
    assert row["tlc"]["generated_state_values"] == [27, 28], row
    assert row["tlc"]["consistent_generated_states"] is False, row


def test_summarize_spec_excludes_bool_tlc_returncode_from_median() -> None:
    spec = bench.perf_harness.SpecInfo(
        name="TinySpec",
        tla_path="Tiny.tla",
        cfg_path="Tiny.cfg",
        category="unit",
        expected_states=10,
    )
    tlc_runs = [
        _tlc_run(states_found=10, elapsed_seconds=3.0, returncode=0),
        _tlc_run(states_found=10, elapsed_seconds=99.0, returncode=False),
    ]
    interp_runs = [_mode_run("interp", states_found=10, elapsed_seconds=2.0)]
    llvm2_runs = [
        _mode_run(
            "llvm2",
            states_found=10,
            elapsed_seconds=1.0,
            telemetry=bench.Llvm2Telemetry(fallback_reasons=[]),
        )
    ]

    row = bench.summarize_spec(spec, interp_runs, llvm2_runs, tlc_runs)

    assert row["tlc"]["median_seconds"] == pytest.approx(3.0), row
    assert row["speedup_llvm2_vs_tlc"] == pytest.approx(3.0), row


def test_aggregate_mode_rejects_non_null_error_with_zero_returncode() -> None:
    runs = [
        _mode_run(
            "llvm2",
            states_found=10,
            elapsed_seconds=1.0,
            error="Invariant violated.",
        )
    ]

    summary = bench.aggregate_mode(runs)

    assert summary["all_ok"] is False, summary
    assert summary["median_seconds"] is None, summary


def test_validate_cli_rejects_native_fused_o1_override() -> None:
    parser = bench.build_cli()
    args = parser.parse_args(
        [
            "--require-llvm2-native-fused-level",
            "--llvm2-env",
            "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL=O1",
        ]
    )

    with pytest.raises(SystemExit):
        bench.validate_cli(args, parser)


@pytest.mark.parametrize(
    ("env_override", "required_value"),
    [
        ("TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST=off", "strict"),
        ("TLA2_LLVM2_NATIVE_FUSED_STRICT=0", "1"),
        ("TLA2_LLVM2_DISABLE_POST_RA_OPT=1", "0"),
        ("TLA2_DISABLE_ARTIFACT_CACHE=0", "1"),
        ("TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP=0", "1"),
    ],
)
def test_validate_cli_rejects_native_fused_smoke_policy_env_override(
    capsys: pytest.CaptureFixture[str],
    env_override: str,
    required_value: str,
) -> None:
    parser = bench.build_cli()
    args = parser.parse_args(
        [
            "--require-llvm2-native-fused-level",
            "--llvm2-env",
            env_override,
        ]
    )

    with pytest.raises(SystemExit):
        bench.validate_cli(args, parser)

    env_key = env_override.split("=", 1)[0]
    assert f"requires {env_key}={required_value}" in capsys.readouterr().err


@pytest.mark.parametrize(
    "env_override",
    [
        "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST=strict",
        "TLA2_LLVM2_NATIVE_FUSED_STRICT=1",
        "TLA2_LLVM2_DISABLE_POST_RA_OPT=0",
        "TLA2_DISABLE_ARTIFACT_CACHE=1",
        "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP=1",
    ],
)
def test_validate_cli_allows_exact_native_fused_smoke_policy_env_override(
    env_override: str,
) -> None:
    parser = bench.build_cli()
    args = parser.parse_args(
        [
            "--require-llvm2-native-fused-level",
            "--llvm2-env",
            env_override,
        ]
    )

    bench.validate_cli(args, parser)


def test_validate_cli_rejects_invariant_fallback_compilation_conflict() -> None:
    parser = bench.build_cli()
    args = parser.parse_args(
        [
            "--allow-llvm2-invariant-rust-fallbacks",
            "--require-no-llvm2-fallbacks",
            "--require-llvm2-fused-level",
            "--require-llvm2-native-fused-level",
            "--require-flat-state-primary",
            "--require-flat-bfs-frontier",
            "--require-llvm2-compiled-invariants",
        ]
    )

    with pytest.raises(SystemExit):
        bench.validate_cli(args, parser)


def test_classify_llvm2_evidence_reports_path_and_winner() -> None:
    row = _summary_row(
        speedup_llvm2_vs_tlc=0.75,
        telemetry={
            "llvm2_actions_compiled": 2,
            "llvm2_actions_total": 2,
            "llvm2_invariants_compiled": 0,
            "llvm2_invariants_total": 1,
            **_native_fused_execution_fields(mode="action_only"),
            "flat_state_primary": True,
            "flat_bfs_frontier_active": True,
            "flat_bfs_frontier_fallbacks": 0,
        },
    )

    evidence = bench.classify_llvm2_evidence(row)

    assert evidence == {
        "native_fused": True,
        "native_fused_regular_invariants_checked": None,
        "action_only": True,
        "flat_layout": True,
        "tlc_wins": True,
        "winner": "TLC",
    }, evidence

    row["speedup_llvm2_vs_tlc"] = 1.25
    row["llvm2"]["telemetry"]["llvm2_invariants_compiled"] = 1
    row["llvm2"]["telemetry"]["llvm2_native_fused_mode"] = "invariant_checking"
    evidence = bench.classify_llvm2_evidence(row)
    assert evidence["action_only"] is False, evidence
    assert evidence["tlc_wins"] is False, evidence
    assert evidence["winner"] == "LLVM2", evidence

    row["llvm2"]["telemetry"]["flat_state_primary"] = None
    row["llvm2"]["telemetry"]["flat_bfs_frontier_active"] = True
    row["llvm2"]["telemetry"]["flat_bfs_frontier_fallbacks"] = 0
    evidence = bench.classify_llvm2_evidence(row)
    assert evidence["flat_layout"] is None, evidence

    row["llvm2"]["telemetry"]["flat_state_primary"] = True
    row["llvm2"]["telemetry"]["flat_bfs_frontier_active"] = None
    evidence = bench.classify_llvm2_evidence(row)
    assert evidence["flat_layout"] is None, evidence

    row["llvm2"]["telemetry"]["flat_state_primary"] = True
    row["llvm2"]["telemetry"]["flat_bfs_frontier_active"] = True
    row["llvm2"]["telemetry"]["flat_bfs_frontier_fallbacks"] = 1
    evidence = bench.classify_llvm2_evidence(row)
    assert evidence["flat_layout"] is False, evidence

    row["llvm2"]["telemetry"]["flat_bfs_frontier_fallbacks"] = False
    evidence = bench.classify_llvm2_evidence(row)
    assert evidence["flat_layout"] is None, evidence


def test_classify_llvm2_evidence_uses_native_fused_mode_over_compile_fraction() -> None:
    row = _summary_row(
        speedup_llvm2_vs_tlc=1.25,
        telemetry={
            "llvm2_actions_compiled": 2,
            "llvm2_actions_total": 2,
            "llvm2_invariants_compiled": 1,
            "llvm2_invariants_total": 1,
            "llvm2_native_fused_level_active": True,
            "llvm2_native_fused_mode": "action_only",
            "llvm2_native_fused_regular_invariants_checked": False,
            "flat_state_primary": True,
            "flat_bfs_frontier_active": True,
            "flat_bfs_frontier_fallbacks": 0,
        },
    )

    evidence = bench.classify_llvm2_evidence(row)

    assert evidence["action_only"] is True, evidence
    assert evidence["native_fused_regular_invariants_checked"] is False, evidence


def test_classify_llvm2_evidence_rejects_spoofed_native_fused_evidence() -> None:
    key_value_only = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=invariant_checking llvm2_native_fused_invariant_count=1 llvm2_native_fused_regular_invariants_checked=true
        [compiled-bfs] starting compiled BFS level loop (1 initial states in arena, fused=true)
        [compiled-bfs] completed: 1 levels, 1 parents, 1 generated, 0 new, 2 total states
        """,
    ).to_dict()
    row = _summary_row(speedup_llvm2_vs_tlc=1.25, telemetry=key_value_only)

    evidence = bench.classify_llvm2_evidence(row)

    assert key_value_only["llvm2_native_fused_level_active"] is True, key_value_only
    assert key_value_only["llvm2_native_fused_level_built"] is False, key_value_only
    assert evidence["native_fused"] is False, evidence


def test_classify_llvm2_evidence_requires_positive_native_fused_completion() -> None:
    missing_completion = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] CompiledBfsLevel built (invariant-checking native fused LLVM2 parent loop): 1 action instances, 1 invariants, state_len=1
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=invariant_checking llvm2_native_fused_invariant_count=1 llvm2_native_fused_regular_invariants_checked=true
        [compiled-bfs] starting compiled BFS level loop (1 initial states in arena, fused=true)
        """,
    ).to_dict()
    zero_completion = dict(missing_completion)
    zero_completion.update(
        {
            "compiled_bfs_levels_completed": 1,
            "compiled_bfs_parents_processed": 1,
            "compiled_bfs_successors_generated": 0,
            "compiled_bfs_total_states": 2,
        }
    )
    positive_completion = dict(missing_completion)
    positive_completion.update(
        {
            "compiled_bfs_levels_completed": 1,
            "compiled_bfs_parents_processed": 1,
            "compiled_bfs_successors_generated": 1,
            "compiled_bfs_total_states": 2,
        }
    )

    assert (
        bench.classify_llvm2_evidence(
            _summary_row(speedup_llvm2_vs_tlc=1.25, telemetry=missing_completion)
        )["native_fused"]
        is False
    )
    assert (
        bench.classify_llvm2_evidence(
            _summary_row(speedup_llvm2_vs_tlc=1.25, telemetry=zero_completion)
        )["native_fused"]
        is False
    )
    assert (
        bench.classify_llvm2_evidence(
            _summary_row(speedup_llvm2_vs_tlc=1.25, telemetry=positive_completion)
        )["native_fused"]
        is True
    )


def test_classify_llvm2_evidence_surfaces_missing_native_invariant_proof() -> None:
    row = _summary_row(
        speedup_llvm2_vs_tlc=1.25,
        telemetry={
            "llvm2_actions_compiled": 2,
            "llvm2_actions_total": 2,
            "llvm2_invariants_compiled": 1,
            "llvm2_invariants_total": 1,
            "compiled_bfs_step_active": True,
            **_native_fused_execution_fields(),
            "flat_state_primary": True,
            "flat_bfs_frontier_active": True,
            "flat_bfs_frontier_fallbacks": 0,
            "fallback_reasons": [],
        },
    )

    evidence = bench.classify_llvm2_evidence(row)

    assert evidence["native_fused"] is True, evidence
    assert evidence["native_fused_regular_invariants_checked"] is None, evidence
    assert evidence["action_only"] is False, evidence
    assert evidence["flat_layout"] is True, evidence


def test_render_markdown_includes_explicit_path_columns() -> None:
    row = _summary_row(
        speedup_llvm2_vs_tlc=0.75,
        telemetry={
            "llvm2_actions_compiled": 2,
            "llvm2_actions_total": 2,
            "llvm2_invariants_compiled": 1,
            "llvm2_invariants_total": 1,
            "compiled_bfs_step_active": True,
            **_native_fused_execution_fields(regular_invariants_checked=True),
            "flat_state_primary": True,
            "flat_bfs_frontier_active": True,
            "flat_bfs_frontier_fallbacks": 0,
            "fallback_reasons": [],
        },
    )
    row["llvm2_evidence"] = bench.classify_llvm2_evidence(row)
    markdown = bench.render_markdown(
        {
            "timestamp": "2026-04-24T000000Z",
            "git_commit": "test",
            "artifact_bundle": "reports/test",
            "invocation": "benchmark_single_thread_backends_vs_tlc.py --fake",
            "rows": [row],
        }
    )

    assert (
        "Winner | Parity | Native fused | Native invariant checks | Action-only | Flat layout"
        in markdown
    ), markdown
    assert (
        "| TinySpec | 3.000 | 2.000 | 4.000 | 1.500 | "
        "1.50x | 0.75x | 2.00x | TLC | PASS | yes | yes | no | yes |"
        in markdown
    ), markdown


def test_render_markdown_marks_missing_native_invariant_proof_as_unknown() -> None:
    row = _summary_row(
        speedup_llvm2_vs_tlc=1.25,
        telemetry={
            "llvm2_actions_compiled": 2,
            "llvm2_actions_total": 2,
            "llvm2_invariants_compiled": 1,
            "llvm2_invariants_total": 1,
            "compiled_bfs_step_active": True,
            **_native_fused_execution_fields(),
            "flat_state_primary": True,
            "flat_bfs_frontier_active": True,
            "flat_bfs_frontier_fallbacks": 0,
            "fallback_reasons": [],
        },
    )
    row["llvm2_evidence"] = bench.classify_llvm2_evidence(row)
    markdown = bench.render_markdown(
        {
            "timestamp": "2026-04-24T000000Z",
            "git_commit": "test",
            "artifact_bundle": "reports/test",
            "invocation": "benchmark_single_thread_backends_vs_tlc.py --fake",
            "rows": [row],
        }
    )

    assert (
        "| TinySpec | 3.000 | 2.000 | 4.000 | 1.500 | "
        "1.50x | 1.25x | 2.00x | LLVM2 | PASS | yes | n/a | no | yes |"
        in markdown
    ), markdown


def test_evaluate_llvm2_truth_gates_reports_requested_failures_only() -> None:
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 0.95,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_actions_compiled=0,
                        llvm2_actions_total=2,
                        compiled_bfs_step_active=False,
                    ).to_dict(),
                }
            ]
        },
    }

    no_gates = Namespace(
        require_llvm2_compiled_actions=False,
        require_llvm2_all_actions=False,
        require_llvm2_compiled_invariants=False,
        require_llvm2_compiled_bfs=False,
        require_llvm2_fused_level=False,
        require_llvm2_native_fused_level=False,
        require_flat_state_primary=False,
        require_flat_bfs_frontier=False,
        require_no_llvm2_fallbacks=False,
        require_llvm2_faster_than_tlc=False,
    )
    strict = Namespace(
        require_llvm2_compiled_actions=True,
        require_llvm2_all_actions=False,
        require_llvm2_compiled_invariants=False,
        require_llvm2_compiled_bfs=True,
        require_llvm2_fused_level=False,
        require_llvm2_native_fused_level=False,
        require_flat_state_primary=False,
        require_flat_bfs_frontier=False,
        require_no_llvm2_fallbacks=False,
        require_llvm2_faster_than_tlc=True,
    )

    assert bench.evaluate_llvm2_truth_gates(row, no_gates) == [], (
        "gates should remain compatibility-noop when flags are absent"
    )
    failures = bench.evaluate_llvm2_truth_gates(row, strict)
    assert len(failures) == 3, failures
    assert any("compiled actions gate failed" in failure for failure in failures), failures
    assert any("compiled BFS step was not active" in failure for failure in failures), failures
    assert any("not faster than TLC" in failure for failure in failures), failures


def test_evaluate_llvm2_execution_speed_gate_uses_execution_timing() -> None:
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 0.75,
        "speedup_llvm2_execution_vs_tlc": 2.0,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        compiled_bfs_execution_nanos=1_500_000_000,
                        fallback_reasons=[],
                    ).to_dict(),
                }
            ]
        },
    }

    args = _gate_args(require_llvm2_execution_faster_than_tlc=True)

    assert bench.evaluate_llvm2_truth_gates(row, args) == []

    row["llvm2"]["runs"][0]["llvm2_telemetry"]["compiled_bfs_execution_nanos"] = None
    failures = bench.evaluate_llvm2_truth_gates(row, args)
    assert any(
        "compiled BFS execution timing telemetry was missing or non-positive" in failure
        for failure in failures
    ), failures

    row["llvm2"]["runs"][0]["llvm2_telemetry"][
        "compiled_bfs_execution_nanos"
    ] = 4_000_000_000
    row["speedup_llvm2_execution_vs_tlc"] = 0.75
    failures = bench.evaluate_llvm2_truth_gates(row, args)
    assert any(
        "llvm2 execution median was not faster than TLC" in failure
        for failure in failures
    ), failures


def test_evaluate_llvm2_execution_speed_gate_rejects_seconds_nanos_mismatch() -> None:
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 2.0,
        "speedup_llvm2_execution_vs_tlc": 2.0,
        "tlc": {
            "runs": [
                {"run_index": 1, "elapsed_seconds": 1.0, "returncode": 0},
            ],
        },
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "returncode": 0,
                    "llvm2_telemetry": {
                        "compiled_bfs_execution_seconds": 0.25,
                        "compiled_bfs_execution_nanos": 2_000_000_000,
                    },
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_execution_faster_than_tlc=True),
    )

    assert any(
        "compiled BFS execution seconds/nanos mismatch" in failure
        for failure in failures
    ), failures


def test_evaluate_llvm2_wall_speed_gate_allows_same_index_slow_sample_when_median_wins() -> None:
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 1.5,
        "tlc": {
            "runs": [
                {"run_index": 1, "elapsed_seconds": 3.0, "returncode": 0},
                {"run_index": 2, "elapsed_seconds": 1.0, "returncode": 0},
                {"run_index": 3, "elapsed_seconds": 3.0, "returncode": 0},
            ],
        },
        "llvm2": {
            "runs": [
                {"run_index": 1, "elapsed_seconds": 2.0, "returncode": 0},
                {"run_index": 2, "elapsed_seconds": 2.0, "returncode": 0},
                {"run_index": 3, "elapsed_seconds": 2.0, "returncode": 0},
            ],
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_faster_than_tlc=True),
    )

    assert failures == []


def test_evaluate_llvm2_execution_speed_gate_allows_same_index_slow_sample_when_median_wins() -> None:
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 1.5,
        "speedup_llvm2_execution_vs_tlc": 3.0,
        "tlc": {
            "runs": [
                {"run_index": 1, "elapsed_seconds": 3.0, "returncode": 0},
                {"run_index": 2, "elapsed_seconds": 1.0, "returncode": 0},
                {"run_index": 3, "elapsed_seconds": 3.0, "returncode": 0},
            ],
        },
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "returncode": 0,
                    "llvm2_telemetry": {"compiled_bfs_execution_nanos": 1_000_000_000},
                },
                {
                    "run_index": 2,
                    "returncode": 0,
                    "llvm2_telemetry": {"compiled_bfs_execution_nanos": 2_000_000_000},
                },
                {
                    "run_index": 3,
                    "returncode": 0,
                    "llvm2_telemetry": {"compiled_bfs_execution_nanos": 1_000_000_000},
                },
            ],
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_execution_faster_than_tlc=True),
    )

    assert failures == []


def test_evaluate_llvm2_execution_speed_gate_rejects_bool_timing() -> None:
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 2.0,
        "speedup_llvm2_execution_vs_tlc": 2.0,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        compiled_bfs_execution_nanos=True,
                        compiled_bfs_execution_seconds=True,
                        fallback_reasons=[],
                    ).to_dict(),
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_execution_faster_than_tlc=True),
    )

    assert any(
        "compiled BFS execution timing telemetry was missing or non-positive"
        in failure
        for failure in failures
    ), failures


def test_flat_frontier_gate_rejects_bool_zero_fallback_count() -> None:
    telemetry = bench.Llvm2Telemetry(
        flat_state_primary=True,
        flat_bfs_frontier_active=True,
        flat_bfs_frontier_fallbacks=False,
        fallback_reasons=[],
    ).to_dict()
    row = {
        "spec": "TinySpec",
        "speedup_llvm2_vs_tlc": 2.0,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_flat_bfs_frontier=True),
    )

    assert any(
        "flat BFS frontier did not report explicit active=true with 0 fallback"
        in failure
        for failure in failures
    ), failures


def test_evaluate_llvm2_evidence_gates_require_full_native_path() -> None:
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_actions_compiled=1,
                        llvm2_actions_total=2,
                        llvm2_invariants_compiled=0,
                        llvm2_invariants_total=1,
                        compiled_bfs_step_active=True,
                        compiled_bfs_level_active=False,
                        flat_state_primary=False,
                        flat_bfs_frontier_active=False,
                        fallback_reasons=["[llvm2] skipping action 'B': unsupported"],
                    ).to_dict(),
                }
            ]
        },
    }

    gates = Namespace(
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

    failures = bench.evaluate_llvm2_truth_gates(row, gates)

    assert any("all-actions gate failed" in failure for failure in failures), failures
    assert any("compiled invariants gate failed" in failure for failure in failures), failures
    assert any("fused BFS level was not active" in failure for failure in failures), failures
    assert any("native LLVM2 fused BFS level" in failure for failure in failures), failures
    assert any("flat_state_primary was not true" in failure for failure in failures), failures
    assert any("flat BFS frontier did not report explicit active=true" in failure for failure in failures), failures
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures
    assert not any("compiled actions gate failed" in failure for failure in failures), failures
    assert not any("compiled BFS step was not active" in failure for failure in failures), failures
    assert not any("not faster than TLC" in failure for failure in failures), failures


def test_allow_invariant_rust_fallbacks_rejects_truncated_fallback_sentinel() -> None:
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
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
                        llvm2_native_fused_mode="action_only",
                        flat_state_primary=True,
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=0,
                        fallback_reasons=[
                            "[llvm2] invariant-checking native fused CompiledBfsLevel unavailable, falling back to action-only native/prototype: missing invariant thunk",
                            bench.TRUNCATED_FALLBACK_REASON,
                        ],
                    ).to_dict(),
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_no_llvm2_fallbacks=True,
            allow_llvm2_invariant_rust_fallbacks=True,
        ),
    )

    assert len(failures) == 1, failures
    assert "non-invariant LLVM2 fallback reasons observed" in failures[0], failures
    assert "1 disallowed of 2 total" in failures[0], failures


def test_allow_invariant_rust_fallbacks_allows_action_only_native_build_with_work() -> None:
    fallback_reason = (
        "[llvm2] invariant-checking native fused CompiledBfsLevel unavailable, "
        "falling back to action-only native/prototype: missing invariant thunk"
    )
    telemetry = {
        **_native_fused_execution_fields(mode="action_only"),
        "flat_state_primary": True,
        "flat_bfs_frontier_active": True,
        "flat_bfs_frontier_fallbacks": 0,
        "fallback_reasons": [fallback_reason],
    }
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    assert (
        bench.evaluate_llvm2_truth_gates(
            row,
            _gate_args(
                require_no_llvm2_fallbacks=True,
                allow_llvm2_invariant_rust_fallbacks=True,
            ),
        )
        == []
    )


def test_allow_invariant_rust_fallbacks_rejects_action_only_kv_without_build_line() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=action_only llvm2_native_fused_invariant_count=0 llvm2_native_fused_regular_invariants_checked=false
        [flat_state] flat_state_primary=true: all vars scalar, no VIEW, no SYMMETRY
        [flat-frontier] flat_bfs_frontier_active=true: 1 total pushed, 1 flat (100.0%), 0 fallback, 24 bytes/state
        [compiled-bfs] starting compiled BFS level loop (1 initial states in arena, fused=true)
        [compiled-bfs] completed: 1 levels, 1 parents, 1 generated, 0 new, 2 total states
        [llvm2] invariant-checking native fused CompiledBfsLevel unavailable, falling back to action-only native/prototype: missing invariant thunk
        """,
    ).to_dict()
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_no_llvm2_fallbacks=True,
            allow_llvm2_invariant_rust_fallbacks=True,
        ),
    )

    assert telemetry["llvm2_native_fused_level_built"] is False, telemetry
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures


def test_compiled_bfs_requirements_reject_runtime_fallback_errors() -> None:
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        compiled_bfs_step_active=True,
                        compiled_bfs_level_active=True,
                        fallback_reasons=[
                            "[compiled-bfs] fused level error: compiled BFS step runtime error -- falling back to per-parent step"
                        ],
                    ).to_dict(),
                }
            ]
        },
    }
    compiled_args = _gate_args(require_llvm2_compiled_bfs=True)
    fused_args = _gate_args(require_llvm2_fused_level=True)

    compiled_failures = bench.evaluate_llvm2_truth_gates(row, compiled_args)
    fused_failures = bench.evaluate_llvm2_truth_gates(row, fused_args)

    assert any(
        "compiled BFS runtime fallback/error reasons observed" in failure
        for failure in compiled_failures
    ), compiled_failures
    assert any(
        "compiled BFS runtime fallback/error reasons observed" in failure
        for failure in fused_failures
    ), fused_failures


def test_native_fused_requirement_implies_flat_frontier_and_no_fallbacks() -> None:
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
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
                        flat_state_primary=False,
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=1,
                        fallback_reasons=[
                            "[llvm2] failed to compile action 'A': unsupported",
                        ],
                    ).to_dict(),
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )

    assert any("flat_state_primary was not true" in failure for failure in failures), failures
    assert any(
        "flat BFS frontier did not report explicit active=true with 0 fallback" in failure
        for failure in failures
    ), failures
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures


def test_native_fused_requirement_rejects_zero_work_compiled_bfs_completion() -> None:
    failures = _native_fused_completion_failures(
        "[compiled-bfs] completed: 0 levels, 0 parents, 0 generated, 0 new, 192 total states"
    )

    assert any(
        "compiled BFS loop completed without processing work" in failure
        for failure in failures
    ), failures
    assert any("levels=0" in failure for failure in failures), failures


def test_native_fused_requirement_rejects_missing_compiled_bfs_completion() -> None:
    failures = _native_fused_completion_failures("")

    assert any(
        "compiled BFS loop did not report positive native-fused work" in failure
        and "levels=None" in failure
        for failure in failures
    ), failures


def test_native_fused_requirement_rejects_active_kv_without_build_line() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=invariant_checking llvm2_native_fused_invariant_count=1 llvm2_native_fused_regular_invariants_checked=true
        [flat_state] flat_state_primary=true: all vars scalar, no VIEW, no SYMMETRY
        [flat-frontier] flat_bfs_frontier_active=true: 192 total pushed, 192 flat (100.0%), 0 fallback, 24 bytes/state
        [compiled-bfs] starting compiled BFS level loop (192 initial states in arena, fused=true)
        [compiled-bfs] completed: 1 levels, 1 parents, 1 generated, 0 new, 192 total states
        """,
    ).to_dict()
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )

    assert telemetry["llvm2_native_fused_level_active"] is True, telemetry
    assert telemetry["llvm2_native_fused_level_built"] is False, telemetry
    assert any(
        "llvm2_native_fused_level_built=False" in failure for failure in failures
    ), failures


@pytest.mark.parametrize(
    ("completion", "expected_detail"),
    [
        (
            "[compiled-bfs] completed: 1 levels, 0 parents, 0 generated, 0 new, 192 total states",
            "parents=0",
        ),
        (
            "[compiled-bfs] completed: 1 levels, 1 parents, 0 generated, 0 new, 192 total states",
            "generated=0",
        ),
    ],
)
def test_native_fused_requirement_rejects_partial_zero_compiled_bfs_completion(
    completion: str,
    expected_detail: str,
) -> None:
    failures = _native_fused_completion_failures(completion)

    assert any(
        "compiled BFS loop did not report positive native-fused work" in failure
        and expected_detail in failure
        for failure in failures
    ), failures


def test_native_fused_requirement_requires_positive_compiled_bfs_work_counts() -> None:
    failures = _native_fused_completion_failures(
        "[compiled-bfs] completed: 1 levels, 1 parents, 1 generated, 0 new, 192 total states"
    )

    assert failures == [], failures


def test_successor_telemetry_gate_requires_new_successors_and_total_state_match() -> None:
    def telemetry(*, successors_new: int | None, total_states: int | None) -> dict:
        return bench.Llvm2Telemetry(
            compiled_bfs_successors_new=successors_new,
            compiled_bfs_total_states=total_states,
        ).to_dict()

    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "states_found": 10,
                    "llvm2_telemetry": telemetry(successors_new=0, total_states=10),
                },
                {
                    "run_index": 2,
                    "states_found": 10,
                    "llvm2_telemetry": telemetry(successors_new=2, total_states=9),
                },
                {
                    "run_index": 3,
                    "states_found": 10,
                    "llvm2_telemetry": telemetry(successors_new=2, total_states=10),
                },
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_successor_telemetry=True),
    )

    assert len(failures) == 2, failures
    assert any(
        "run 1" in failure and "compiled_bfs_successors_new=0" in failure
        for failure in failures
    ), failures
    assert any(
        "run 2" in failure
        and "compiled_bfs_total_states=9" in failure
        and "states_found=10" in failure
        for failure in failures
    ), failures
    assert not any("run 3" in failure for failure in failures), failures


@pytest.mark.parametrize(
    ("start_line", "expected_detail"),
    [
        (
            "[compiled-bfs] starting compiled BFS level loop (1 initial states in arena, fused=false)",
            "compiled_bfs_level_loop_fused=False",
        ),
        (
            "[compiled-bfs] starting compiled BFS level loop (0 initial states in arena, fused=true)",
            "compiled_bfs_level_loop_initial_states=0",
        ),
        (
            "[compiled-bfs] activating compiled BFS loop (auto-detected)",
            "compiled_bfs_level_loop_initial_states=None",
        ),
    ],
)
def test_native_fused_requirement_rejects_unproven_fused_loop_start(
    start_line: str, expected_detail: str
) -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        f"""
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=invariant_checking llvm2_native_fused_invariant_count=1 llvm2_native_fused_regular_invariants_checked=true
        [flat_state] flat_state_primary=true: all vars scalar, no VIEW, no SYMMETRY
        [flat-frontier] flat_bfs_frontier_active=true: 1 total pushed, 1 flat (100.0%), 0 fallback, 24 bytes/state
        {start_line}
        """,
    ).to_dict()
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {"runs": [{"run_index": 1, "transitions": 1, "llvm2_telemetry": telemetry}]},
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )

    assert any(expected_detail in failure for failure in failures), failures


def test_native_fused_requirement_rejects_zero_transition_runs() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] CompiledBfsLevel built (invariant-checking native fused LLVM2 parent loop): 1 action instances, 1 invariants, state_len=1
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=invariant_checking llvm2_native_fused_invariant_count=1 llvm2_native_fused_regular_invariants_checked=true
        [flat_state] flat_state_primary=true: all vars scalar, no VIEW, no SYMMETRY
        [flat-frontier] flat_bfs_frontier_active=true: 1 total pushed, 1 flat (100.0%), 0 fallback, 24 bytes/state
        [compiled-bfs] starting compiled BFS level loop (1 initial states in arena, fused=true)
        [compiled-bfs] completed: 1 levels, 1 parents, 1 generated, 1 new, 2 total states
        """,
    ).to_dict()
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 0,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )

    assert len(failures) == 1, failures
    assert "transition work was not observed (transitions=0)" in failures[0], failures


def test_native_fused_requirement_requires_state_constraints_for_constrained_specs() -> None:
    telemetry = bench.Llvm2Telemetry(
        llvm2_invariants_compiled=3,
        llvm2_invariants_total=3,
        llvm2_state_constraints_compiled=1,
        llvm2_state_constraints_total=1,
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
        llvm2_native_fused_mode="invariant_checking",
        llvm2_native_fused_invariant_count=3,
        llvm2_native_fused_state_len=15,
        llvm2_native_fused_regular_invariants_checked=True,
        flat_state_primary=True,
        flat_bfs_frontier_active=True,
        flat_bfs_frontier_fallbacks=0,
        fallback_reasons=[],
    ).to_dict()
    row = {
        "spec": "EWD998Small",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )
    assert len(failures) == 1, failures
    assert "native fused state constraints were not checked by the backend" in failures[0], failures
    assert "llvm2_native_fused_state_constraint_count=None" in failures[0], failures
    assert "expected=1" in failures[0], failures

    telemetry["llvm2_native_fused_state_constraint_count"] = 0
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )
    assert len(failures) == 1, failures
    assert "llvm2_native_fused_state_constraint_count=0" in failures[0], failures

    telemetry["llvm2_native_fused_state_constraint_count"] = 1
    telemetry["llvm2_native_fused_mode"] = "state_constraint_checking"
    telemetry["compiled_bfs_step_active"] = False
    assert bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_compiled_invariants=True,
            require_llvm2_native_fused_level=True,
        ),
    ) == []

    telemetry["llvm2_state_constraints_compiled"] = None
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )
    assert any(
        "native fused state constraints were not checked by the backend" in failure
        and "llvm2_state_constraints_compiled=None" in failure
        and "llvm2_state_constraints_total=1" in failure
        for failure in failures
    ), failures
    telemetry["llvm2_state_constraints_compiled"] = 1


@pytest.mark.parametrize(
    ("spec_name", "expected_state_len"),
    [("EWD998Small", 15), ("MCLamportMutex", 89)],
)
def test_native_fused_requirement_rejects_wrong_state_constrained_state_len(
    spec_name: str,
    expected_state_len: int,
) -> None:
    telemetry = bench.Llvm2Telemetry(
        llvm2_invariants_compiled=3,
        llvm2_invariants_total=3,
        llvm2_state_constraints_compiled=1,
        llvm2_state_constraints_total=1,
        compiled_bfs_step_active=False,
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
        llvm2_native_fused_mode="state_constraint_checking",
        llvm2_native_fused_invariant_count=3,
        llvm2_native_fused_regular_invariants_checked=True,
        llvm2_native_fused_state_constraint_count=1,
        llvm2_native_fused_state_len=63,
        flat_state_primary=True,
        flat_bfs_frontier_active=True,
        flat_bfs_frontier_fallbacks=0,
        fallback_reasons=[],
    ).to_dict()
    row = {
        "spec": spec_name,
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )

    assert any(
        "native fused state length did not match the real spec layout" in failure
        and "llvm2_native_fused_state_len=63" in failure
        and f"expected={expected_state_len}" in failure
        for failure in failures
    ), failures


def test_native_fused_requirement_rejects_wrong_coffee_state_len() -> None:
    telemetry = bench.Llvm2Telemetry(
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
        llvm2_native_fused_mode="invariant_checking",
        llvm2_native_fused_invariant_count=1,
        llvm2_native_fused_regular_invariants_checked=True,
        llvm2_native_fused_state_constraint_count=0,
        llvm2_native_fused_state_len=1,
        flat_state_primary=True,
        flat_bfs_frontier_active=True,
        flat_bfs_frontier_fallbacks=0,
        fallback_reasons=[],
    ).to_dict()
    row = {
        "spec": "CoffeeCan1000BeansSafety",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )

    assert any(
        "native fused state length did not match the real spec layout" in failure
        and "llvm2_native_fused_state_len=1" in failure
        and "expected=2" in failure
        for failure in failures
    ), failures


def test_no_fallback_gate_allows_benign_state_constraint_step_skip_in_full_native() -> None:
    skip_reason = (
        "[llvm2] CompiledBfsStep not eligible: "
        "state constraints require native fused constraint pruning "
        "(first state constraint: StateConstraint)"
    )
    telemetry = bench.Llvm2Telemetry(
        llvm2_invariants_compiled=3,
        llvm2_invariants_total=3,
        llvm2_state_constraints_compiled=1,
        llvm2_state_constraints_total=1,
        compiled_bfs_step_active=False,
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
        llvm2_native_fused_mode="state_constraint_checking",
        llvm2_native_fused_invariant_count=3,
        llvm2_native_fused_regular_invariants_checked=True,
        llvm2_native_fused_state_constraint_count=1,
        llvm2_native_fused_state_len=15,
        flat_state_primary=True,
        flat_bfs_frontier_active=True,
        flat_bfs_frontier_fallbacks=0,
        fallback_reasons=[skip_reason],
    ).to_dict()
    row = {
        "spec": "EWD998Small",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }

    assert bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_compiled_invariants=True,
            require_llvm2_native_fused_level=True,
            require_no_llvm2_fallbacks=True,
        ),
    ) == []

    row["spec"] = "CoffeeCan1000BeansSafety"
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_native_fused_level=True,
            require_no_llvm2_fallbacks=True,
        ),
    )
    assert any("compiled BFS step was not active" in failure for failure in failures), failures

    row["spec"] = "EWD998Small"
    telemetry["llvm2_native_fused_state_constraint_count"] = 0
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_native_fused_level=True,
            require_no_llvm2_fallbacks=True,
        ),
    )
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures

    telemetry["llvm2_native_fused_state_constraint_count"] = 1
    telemetry["llvm2_state_constraints_compiled"] = 0
    telemetry["fallback_reasons"] = [
        skip_reason,
    ]
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_native_fused_level=True,
            require_no_llvm2_fallbacks=True,
        ),
    )
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures

    telemetry["llvm2_state_constraints_compiled"] = 1
    telemetry["llvm2_state_constraints_total"] = None
    telemetry["fallback_reasons"] = [
        skip_reason,
    ]
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_native_fused_level=True,
            require_no_llvm2_fallbacks=True,
        ),
    )
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures

    telemetry["llvm2_state_constraints_total"] = 1
    telemetry["fallback_reasons"] = [
        (
            "[llvm2] CompiledBfsStep not eligible: "
            "state constraints require native fused constraint pruning "
            "but action lowering also failed"
        )
    ]
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_native_fused_level=True,
            require_no_llvm2_fallbacks=True,
        ),
    )
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures

    telemetry["fallback_reasons"] = [
        "[llvm2] CompiledBfsStep not eligible: unsupported lowering for action Foo"
    ]
    failures = bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(
            require_llvm2_native_fused_level=True,
            require_no_llvm2_fallbacks=True,
        ),
    )
    assert any("LLVM2 fallback reasons observed" in failure for failure in failures), failures


def test_native_fused_requirement_allows_missing_state_constraint_count_for_coffee() -> None:
    row = {
        "spec": "CoffeeCan1000BeansSafety",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
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
                        llvm2_native_fused_mode="invariant_checking",
                        llvm2_native_fused_invariant_count=1,
                        llvm2_native_fused_state_len=2,
                        llvm2_native_fused_regular_invariants_checked=True,
                        flat_state_primary=True,
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=0,
                        fallback_reasons=[],
                    ).to_dict(),
                }
            ]
        },
    }

    assert bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    ) == []


def test_require_compiled_invariants_rejects_zero_configured_zero_compiled() -> None:
    gates = Namespace(
        require_llvm2_compiled_actions=False,
        require_llvm2_all_actions=False,
        require_llvm2_compiled_invariants=True,
        require_llvm2_compiled_bfs=False,
        require_llvm2_fused_level=False,
        require_llvm2_native_fused_level=False,
        require_flat_state_primary=False,
        require_flat_bfs_frontier=False,
        require_no_llvm2_fallbacks=False,
        require_llvm2_faster_than_tlc=False,
    )
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_invariants_compiled=0,
                        llvm2_invariants_total=0,
                    ).to_dict(),
                },
                {
                    "run_index": 2,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_invariants_compiled=1,
                        llvm2_invariants_total=1,
                    ).to_dict(),
                },
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(row, gates)

    assert len(failures) == 1, failures
    assert "run 1" in failures[0], failures
    assert "compiled invariants gate failed (0/0)" in failures[0], failures


def test_require_compiled_invariants_rejects_native_action_only_fused_level() -> None:
    gates = Namespace(
        require_llvm2_compiled_actions=False,
        require_llvm2_all_actions=False,
        require_llvm2_compiled_invariants=True,
        require_llvm2_compiled_bfs=False,
        require_llvm2_fused_level=False,
        require_llvm2_native_fused_level=False,
        require_flat_state_primary=False,
        require_flat_bfs_frontier=False,
        require_no_llvm2_fallbacks=False,
        require_llvm2_faster_than_tlc=False,
    )
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_invariants_compiled=1,
                        llvm2_invariants_total=1,
                        llvm2_native_fused_level_active=True,
                        llvm2_native_fused_regular_invariants_checked=False,
                    ).to_dict(),
                },
                {
                    "run_index": 2,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_invariants_compiled=1,
                        llvm2_invariants_total=1,
                        llvm2_native_fused_level_active=True,
                        llvm2_native_fused_mode="invariant_checking",
                        llvm2_native_fused_invariant_count=1,
                        llvm2_native_fused_regular_invariants_checked=True,
                    ).to_dict(),
                },
                {
                    "run_index": 3,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        llvm2_invariants_compiled=1,
                        llvm2_invariants_total=1,
                        llvm2_native_fused_level_active=True,
                        llvm2_native_fused_mode="action_only",
                        llvm2_native_fused_invariant_count=0,
                        llvm2_native_fused_regular_invariants_checked=True,
                    ).to_dict(),
                },
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(row, gates)

    assert len(failures) == 2, failures
    assert "run 1" in failures[0], failures
    assert "native fused regular invariants were not checked by the backend" in failures[0], failures
    assert any(
        "run 3" in failure
        and "native fused invariant coverage did not include all regular invariants" in failure
        for failure in failures
    ), failures


def test_require_flat_bfs_frontier_gate_rejects_missing_zero_fallback_evidence() -> None:
    gates = Namespace(
        require_llvm2_compiled_actions=False,
        require_llvm2_all_actions=False,
        require_llvm2_compiled_invariants=False,
        require_llvm2_compiled_bfs=False,
        require_llvm2_fused_level=False,
        require_llvm2_native_fused_level=False,
        require_flat_state_primary=False,
        require_flat_bfs_frontier=True,
        require_no_llvm2_fallbacks=False,
        require_llvm2_faster_than_tlc=False,
    )
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        flat_bfs_frontier_active=True,
                        fallback_reasons=[],
                    ).to_dict(),
                },
                {
                    "run_index": 2,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=1,
                        fallback_reasons=[],
                    ).to_dict(),
                },
                {
                    "run_index": 3,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=0,
                        fallback_reasons=[],
                    ).to_dict(),
                },
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(row, gates)

    assert len(failures) == 2, failures
    assert any(
        "run 1" in failure and "fallbacks=None" in failure for failure in failures
    ), failures
    assert any("run 2" in failure and "fallbacks=1" in failure for failure in failures), failures
    assert not any("run 3" in failure for failure in failures), failures


def test_require_native_fused_level_requires_loop_kind_evidence() -> None:
    gates = Namespace(
        require_llvm2_compiled_actions=False,
        require_llvm2_all_actions=False,
        require_llvm2_compiled_invariants=False,
        require_llvm2_compiled_bfs=False,
        require_llvm2_fused_level=False,
        require_llvm2_native_fused_level=True,
        require_flat_state_primary=False,
        require_flat_bfs_frontier=False,
        require_no_llvm2_fallbacks=False,
        require_llvm2_faster_than_tlc=False,
    )
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
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
                        flat_state_primary=True,
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=0,
                        fallback_reasons=[],
                    ).to_dict(),
                },
                {
                    "run_index": 2,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
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
                        llvm2_bfs_level_loop_kind="prototype_rust_parent_loop_over_llvm2_action_invariant_pointers",
                        flat_state_primary=True,
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=0,
                        fallback_reasons=[],
                    ).to_dict(),
                },
                {
                    "run_index": 3,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
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
                        llvm2_native_fused_regular_invariants_checked=True,
                        flat_state_primary=True,
                        flat_bfs_frontier_active=True,
                        flat_bfs_frontier_fallbacks=0,
                        fallback_reasons=[],
                    ).to_dict(),
                },
                {
                    "run_index": 4,
                    "llvm2_telemetry": bench.Llvm2Telemetry(
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
                },
            ]
        },
    }

    failures = bench.evaluate_llvm2_truth_gates(row, gates)

    assert len(failures) == 2, failures
    assert any("run 1" in failure and "loop_kind=None" in failure for failure in failures), failures
    assert any(
        "run 2" in failure and "prototype_rust_parent_loop" in failure for failure in failures
    ), failures
    assert not any("run 3" in failure for failure in failures), failures
    assert not any("run 4" in failure for failure in failures), failures


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


def _native_fused_completion_failures(completion_line: str) -> list[str]:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        f"""
        [llvm2] CompiledBfsLevel built (invariant-checking native fused LLVM2 parent loop): 1 action instances, 1 invariants, state_len=1
        [llvm2] llvm2_bfs_level_active=true llvm2_native_fused_level_active=true llvm2_bfs_level_loop_kind=native_fused_llvm2_parent_loop llvm2_native_fused_mode=invariant_checking llvm2_native_fused_invariant_count=1 llvm2_native_fused_regular_invariants_checked=true
        [flat_state] flat_state_primary=true: all vars scalar, no VIEW, no SYMMETRY
        [flat-frontier] flat_bfs_frontier_active=true: 192 total pushed, 192 flat (100.0%), 0 fallback, 24 bytes/state
        [compiled-bfs] starting compiled BFS level loop (192 initial states in arena, fused=true)
        {completion_line}
        """,
    ).to_dict()
    row = {
        "spec": "TargetSpec",
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": 1,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }
    assert telemetry["fallback_reasons"] == [], telemetry
    return bench.evaluate_llvm2_truth_gates(
        row,
        _gate_args(require_llvm2_native_fused_level=True),
    )


def _mode_run(
    mode: str,
    *,
    states_found: int | None,
    elapsed_seconds: float = 1.0,
    telemetry: bench.Llvm2Telemetry | None = None,
    error: str | None = None,
) -> bench.ModeRunResult:
    return bench.ModeRunResult(
        tool="tla2",
        mode=mode,
        spec_name="TinySpec",
        run_index=1,
        elapsed_seconds=elapsed_seconds,
        states_found=states_found,
        transitions=1,
        returncode=0,
        error=error,
        artifact_dir=None,
        llvm2_telemetry=telemetry,
    )


def _tlc_run(
    *,
    states_found: int | None,
    elapsed_seconds: float = 1.0,
    returncode: int | bool = 0,
    states_generated: int | None = None,
) -> bench.scaling.ScalingRunResult:
    return bench.scaling.ScalingRunResult(
        tool="tlc",
        spec_name="TinySpec",
        workers=1,
        elapsed_seconds=elapsed_seconds,
        states_found=states_found,
        distinct_states=states_found,
        returncode=returncode,
        error=None,
        artifact_dir=None,
        states_generated=states_generated,
    )


def _run(run_index: int, telemetry: bench.Llvm2Telemetry) -> bench.ModeRunResult:
    return bench.ModeRunResult(
        tool="tla2",
        mode="llvm2",
        spec_name="TinySpec",
        run_index=run_index,
        elapsed_seconds=float(run_index),
        states_found=1,
        transitions=1,
        returncode=0,
        error=None,
        artifact_dir=None,
        llvm2_telemetry=telemetry,
    )


def _summary_row(
    *,
    speedup_llvm2_vs_tlc: float,
    telemetry: dict,
    speedup_llvm2_execution_vs_tlc: float | None = 2.0,
    llvm2_execution_median_seconds: float | None = 1.5,
) -> dict:
    return {
        "spec": "TinySpec",
        "tlc": {"median_seconds": 3.0},
        "interp": {"median_seconds": 2.0},
        "llvm2": {
            "median_seconds": 4.0,
            "execution_median_seconds": llvm2_execution_median_seconds,
            "telemetry": telemetry,
            "runs": [],
        },
        "parity_interp_vs_tlc": True,
        "parity_llvm2_vs_tlc": True,
        "speedup_interp_vs_tlc": 1.5,
        "speedup_llvm2_vs_tlc": speedup_llvm2_vs_tlc,
        "speedup_llvm2_execution_vs_tlc": speedup_llvm2_execution_vs_tlc,
        "llvm2_gate_failures": [],
    }
