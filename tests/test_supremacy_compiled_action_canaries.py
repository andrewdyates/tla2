# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Focused compiled-action canaries for the pinned supremacy specs."""

from __future__ import annotations

import sys
from argparse import Namespace
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

import benchmark_single_thread_backends_vs_tlc as bench


EXPECTED_ACTIONS = {
    "CoffeeCan1000Beans": 4,
    "EWD998Small": 15,
    "MCLamportMutex": 27,
}


EXPECTED_INVARIANTS = {
    "CoffeeCan1000Beans": 1,
    "EWD998Small": 3,
    "MCLamportMutex": 3,
}


def test_mclamport_gate_rejects_zero_of_27_action_lowering_gap() -> None:
    telemetry = bench.parse_llvm2_telemetry(
        "",
        """
        [llvm2] executable action coverage: llvm2_actions_compiled=0 llvm2_actions_total=27
        [llvm2] compilation complete: 0/27 actions, 3/3 invariants compiled
        [llvm2] failed to compile action 'enter': unsupported opcode for tMIR backend: StoreVar
        [llvm2] failed to compile action 'try': unsupported opcode for tMIR backend: SetUnion
        [llvm2] failed to compile action 'exit': unsupported opcode for tMIR backend: SetDiff
        """,
    ).to_dict()

    assert telemetry["llvm2_actions_compiled"] == 0, telemetry
    assert telemetry["llvm2_actions_total"] == 27, telemetry
    for opcode in ("StoreVar", "SetUnion", "SetDiff"):
        assert any(opcode in reason for reason in telemetry["fallback_reasons"]), (
            telemetry
        )

    failures = bench.evaluate_llvm2_truth_gates(
        _row("MCLamportMutex", telemetry, transitions=3),
        _full_native_gate_args(),
    )

    assert any("compiled actions gate failed (0/27)" in failure for failure in failures), (
        failures
    )
    assert any("all-actions gate failed (0/27)" in failure for failure in failures), failures
    assert any("native LLVM2 fused BFS level was not active" in failure for failure in failures), (
        failures
    )
    assert any("LLVM2 fallback reasons observed (3)" in failure for failure in failures), (
        failures
    )


@pytest.mark.parametrize("spec_name", ["CoffeeCan1000Beans", "EWD998Small"])
def test_full_native_gate_rejects_zero_actions_and_non_native_path(
    spec_name: str,
) -> None:
    telemetry = bench.Llvm2Telemetry(
        llvm2_actions_compiled=0,
        llvm2_actions_total=EXPECTED_ACTIONS[spec_name],
        llvm2_invariants_compiled=EXPECTED_INVARIANTS[spec_name],
        llvm2_invariants_total=EXPECTED_INVARIANTS[spec_name],
        compiled_bfs_step_active=True,
        compiled_bfs_level_active=True,
        llvm2_native_fused_level_active=False,
        llvm2_bfs_level_loop_kind=(
            "prototype_rust_parent_loop_over_llvm2_action_invariant_pointers"
        ),
        llvm2_native_fused_mode="invariant_checking",
        llvm2_native_fused_invariant_count=EXPECTED_INVARIANTS[spec_name],
        llvm2_native_fused_regular_invariants_checked=True,
        flat_state_primary=True,
        flat_bfs_frontier_active=True,
        flat_bfs_frontier_fallbacks=0,
        fallback_reasons=[],
    ).to_dict()

    failures = bench.evaluate_llvm2_truth_gates(
        _row(spec_name, telemetry, transitions=1),
        _full_native_gate_args(),
    )

    assert any("compiled actions gate failed (0/" in failure for failure in failures), (
        failures
    )
    assert any("all-actions gate failed (0/" in failure for failure in failures), failures
    assert any("native LLVM2 fused BFS level was not active" in failure for failure in failures), (
        failures
    )


@pytest.mark.parametrize("spec_name", ["CoffeeCan1000Beans", "EWD998Small"])
def test_full_native_gate_rejects_native_fused_false_even_with_all_actions(
    spec_name: str,
) -> None:
    telemetry = bench.Llvm2Telemetry(
        llvm2_actions_compiled=EXPECTED_ACTIONS[spec_name],
        llvm2_actions_total=EXPECTED_ACTIONS[spec_name],
        llvm2_invariants_compiled=EXPECTED_INVARIANTS[spec_name],
        llvm2_invariants_total=EXPECTED_INVARIANTS[spec_name],
        compiled_bfs_step_active=True,
        compiled_bfs_level_active=True,
        llvm2_native_fused_level_active=False,
        llvm2_bfs_level_loop_kind=(
            "prototype_rust_parent_loop_over_llvm2_action_invariant_pointers"
        ),
        llvm2_native_fused_mode="invariant_checking",
        llvm2_native_fused_invariant_count=EXPECTED_INVARIANTS[spec_name],
        llvm2_native_fused_regular_invariants_checked=True,
        flat_state_primary=True,
        flat_bfs_frontier_active=True,
        flat_bfs_frontier_fallbacks=0,
        fallback_reasons=[],
    ).to_dict()

    failures = bench.evaluate_llvm2_truth_gates(
        _row(spec_name, telemetry, transitions=1),
        _full_native_gate_args(),
    )

    assert any("native LLVM2 fused BFS level was not active" in failure for failure in failures), (
        failures
    )
    assert not any("compiled actions gate failed" in failure for failure in failures), (
        failures
    )


def test_supremacy_canary_action_totals_stay_positive() -> None:
    assert EXPECTED_ACTIONS == {
        "CoffeeCan1000Beans": 4,
        "EWD998Small": 15,
        "MCLamportMutex": 27,
    }
    assert EXPECTED_INVARIANTS == {
        "CoffeeCan1000Beans": 1,
        "EWD998Small": 3,
        "MCLamportMutex": 3,
    }


def _row(spec_name: str, telemetry: dict, *, transitions: int) -> dict:
    return {
        "spec": spec_name,
        "speedup_llvm2_vs_tlc": 1.25,
        "llvm2": {
            "runs": [
                {
                    "run_index": 1,
                    "transitions": transitions,
                    "llvm2_telemetry": telemetry,
                }
            ]
        },
    }


def _full_native_gate_args() -> Namespace:
    return Namespace(
        require_llvm2_compiled_actions=True,
        require_llvm2_all_actions=True,
        require_llvm2_compiled_invariants=True,
        require_llvm2_compiled_bfs=True,
        require_llvm2_fused_level=True,
        require_llvm2_native_fused_level=True,
        require_flat_state_primary=True,
        require_flat_bfs_frontier=True,
        require_no_llvm2_fallbacks=True,
        allow_llvm2_invariant_rust_fallbacks=False,
        require_llvm2_faster_than_tlc=True,
    )
