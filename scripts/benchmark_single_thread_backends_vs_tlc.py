#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Run repeated single-thread TLC vs TLA2 interpreter/LLVM2 comparisons."""

from __future__ import annotations

import argparse
import contextlib
import json
import logging
import math
import os
import re
import shutil
import shlex
import statistics
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import perf_harness
import perf_harness_scaling as scaling

log = logging.getLogger(__name__)

DEFAULT_SPECS = (
    "CoffeeCan1000BeansSafety",
    "EWD998Small",
    "MCLamportMutex",
)
COFFEECAN_SAFETY_SPEC_NAME = "CoffeeCan1000BeansSafety"
COFFEECAN_SAFETY_BEANS = 1000
FLAT_PRIMARY_REBUILD_MARKER = (
    "[compiled-bfs] clearing layout-sensitive compiled artifacts before rebuild: "
    "reason=flat_state_primary layout promotion"
)
NATIVE_FUSED_STATE_CONSTRAINT_COUNTS = {
    "EWD998Small": 1,
    "MCLamportMutex": 1,
}
NATIVE_FUSED_STATE_LENGTHS = {
    COFFEECAN_SAFETY_SPEC_NAME: 2,
    "EWD998Small": 15,
    "MCLamportMutex": 89,
}
REQUIRED_NATIVE_FUSED_ENV = {
    "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST": "strict",
    "TLA2_LLVM2_NATIVE_FUSED_STRICT": "1",
    "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL": "O3",
    "TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL": "O3",
    "TLA2_LLVM2_DISABLE_POST_RA_OPT": "0",
    "TLA2_DISABLE_ARTIFACT_CACHE": "1",
    "TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP": "1",
}
FINAL_SPEC_EXPECTED_STATE_COUNTS = {
    COFFEECAN_SAFETY_SPEC_NAME: 501500,
    "EWD998Small": 1520618,
    "MCLamportMutex": 724274,
}
COMPILED_BFS_EXECUTION_SECONDS_REL_TOL = 1e-6
COMPILED_BFS_EXECUTION_SECONDS_ABS_TOL = 1e-6

MAX_FALLBACK_REASONS = 12
MAX_REASON_CHARS = 240
TRUNCATED_FALLBACK_REASON = (
    "[benchmark] LLVM2 fallback reasons truncated; hidden reasons exist"
)
STATE_CONSTRAINT_STEP_SKIP_REASON = (
    "[llvm2] CompiledBfsStep not eligible: "
    "state constraints require native fused constraint pruning"
)
SANITIZED_TLA2_ENV_PREFIX = "TLA2_"
COMPILED_BFS_EXECUTION_NANOS_REGEX = re.compile(
    r"\b(?:compiled_bfs_execution_nanos|execution_time_ns|execution_time_nanos)"
    r"\s*[:=]\s*(\d[\d,]*)\b",
    re.IGNORECASE,
)
COMPILED_BFS_EXECUTION_SECONDS_REGEX = re.compile(
    r"\b(?:compiled_bfs_execution_seconds|execution_time_seconds)"
    r"\s*[:=]\s*(\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)\b",
    re.IGNORECASE,
)
COMPILED_BFS_LEVEL_BUILT_REGEX = re.compile(
    r"\[llvm2\]\s+CompiledBfsLevel built \((?P<label>[^)]+)\):"
    r".*?\binvariants"
    r"(?:,\s+\d[\d,]*\s+state constraints)?"
    r"(?:,\s+state_len=(?P<state_len>\d[\d,]*))?\b",
    re.IGNORECASE,
)


@dataclass
class Llvm2Telemetry:
    """LLVM2 native-path truth signals parsed from a TLA2 run artifact."""

    llvm2_actions_compiled: int | None = None
    llvm2_actions_total: int | None = None
    llvm2_invariants_compiled: int | None = None
    llvm2_invariants_total: int | None = None
    llvm2_state_constraints_compiled: int | None = None
    llvm2_state_constraints_total: int | None = None
    compiled_bfs_step_active: bool = False
    compiled_bfs_level_active: bool = False
    compiled_bfs_level_loop_started: bool = False
    compiled_bfs_level_loop_initial_states: int | None = None
    compiled_bfs_level_loop_fused: bool | None = None
    compiled_bfs_levels_completed: int | None = None
    compiled_bfs_parents_processed: int | None = None
    compiled_bfs_successors_generated: int | None = None
    compiled_bfs_successors_new: int | None = None
    compiled_bfs_total_states: int | None = None
    compiled_bfs_zero_work: bool = False
    compiled_bfs_execution_nanos: int | None = None
    compiled_bfs_execution_seconds: float | None = None
    llvm2_bfs_level_active: bool = False
    llvm2_native_fused_level_built: bool = False
    llvm2_native_fused_level_active: bool = False
    llvm2_native_fused_regular_invariants_checked: bool | None = None
    llvm2_native_fused_mode: str | None = None
    llvm2_native_fused_invariant_count: int | None = None
    llvm2_native_fused_state_constraint_count: int | None = None
    llvm2_native_fused_state_len: int | None = None
    llvm2_native_fused_local_dedup: bool | None = None
    llvm2_native_bfs_trace_generated: int | None = None
    llvm2_native_bfs_trace_state_count: int | None = None
    llvm2_native_bfs_trace_parents_processed: int | None = None
    llvm2_bfs_level_loop_kind: str | None = None
    flat_state_primary: bool | None = None
    flat_bfs_frontier_active: bool | None = None
    flat_bfs_frontier_fallbacks: int | None = None
    fallback_reasons: list[str] | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "llvm2_actions_compiled": self.llvm2_actions_compiled,
            "llvm2_actions_total": self.llvm2_actions_total,
            "llvm2_invariants_compiled": self.llvm2_invariants_compiled,
            "llvm2_invariants_total": self.llvm2_invariants_total,
            "llvm2_state_constraints_compiled": self.llvm2_state_constraints_compiled,
            "llvm2_state_constraints_total": self.llvm2_state_constraints_total,
            "compiled_bfs_step_active": self.compiled_bfs_step_active,
            "compiled_bfs_level_active": self.compiled_bfs_level_active,
            "compiled_bfs_level_loop_started": self.compiled_bfs_level_loop_started,
            "compiled_bfs_level_loop_initial_states": (
                self.compiled_bfs_level_loop_initial_states
            ),
            "compiled_bfs_level_loop_fused": self.compiled_bfs_level_loop_fused,
            "compiled_bfs_levels_completed": self.compiled_bfs_levels_completed,
            "compiled_bfs_parents_processed": self.compiled_bfs_parents_processed,
            "compiled_bfs_successors_generated": self.compiled_bfs_successors_generated,
            "compiled_bfs_successors_new": self.compiled_bfs_successors_new,
            "compiled_bfs_total_states": self.compiled_bfs_total_states,
            "compiled_bfs_zero_work": self.compiled_bfs_zero_work,
            "compiled_bfs_execution_nanos": self.compiled_bfs_execution_nanos,
            "compiled_bfs_execution_seconds": self.compiled_bfs_execution_seconds,
            "llvm2_bfs_level_active": self.llvm2_bfs_level_active,
            "llvm2_native_fused_level_built": self.llvm2_native_fused_level_built,
            "llvm2_native_fused_level_active": self.llvm2_native_fused_level_active,
            "llvm2_native_fused_regular_invariants_checked": (
                self.llvm2_native_fused_regular_invariants_checked
            ),
            "llvm2_native_fused_mode": self.llvm2_native_fused_mode,
            "llvm2_native_fused_invariant_count": (
                self.llvm2_native_fused_invariant_count
            ),
            "llvm2_native_fused_state_constraint_count": (
                self.llvm2_native_fused_state_constraint_count
            ),
            "llvm2_native_fused_state_len": self.llvm2_native_fused_state_len,
            "llvm2_native_fused_local_dedup": self.llvm2_native_fused_local_dedup,
            "llvm2_native_bfs_trace_generated": self.llvm2_native_bfs_trace_generated,
            "llvm2_native_bfs_trace_state_count": self.llvm2_native_bfs_trace_state_count,
            "llvm2_native_bfs_trace_parents_processed": (
                self.llvm2_native_bfs_trace_parents_processed
            ),
            "llvm2_bfs_level_loop_kind": self.llvm2_bfs_level_loop_kind,
            "flat_state_primary": self.flat_state_primary,
            "flat_bfs_frontier_active": self.flat_bfs_frontier_active,
            "flat_bfs_frontier_fallbacks": self.flat_bfs_frontier_fallbacks,
            "fallback_reasons": list(self.fallback_reasons or []),
        }


@dataclass
class ModeRunResult:
    """Normalized result for one run of TLC or one TLA2 backend."""

    tool: str
    mode: str
    spec_name: str
    run_index: int
    elapsed_seconds: float
    states_found: int | None
    transitions: int | None
    returncode: int
    error: str | None
    artifact_dir: str | None
    workers: int = 1
    env_overrides: dict[str, str] | None = None
    llvm2_telemetry: Llvm2Telemetry | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "tool": self.tool,
            "mode": self.mode,
            "spec_name": self.spec_name,
            "run_index": self.run_index,
            "elapsed_seconds": self.elapsed_seconds,
            "states_found": self.states_found,
            "transitions": self.transitions,
            "returncode": self.returncode,
            "error": self.error,
            "artifact_dir": self.artifact_dir,
            "workers": self.workers,
            "env_overrides": self.env_overrides,
            "llvm2_telemetry": (
                self.llvm2_telemetry.to_dict() if self.llvm2_telemetry is not None else None
            ),
        }


def parse_env_overrides(items: list[str]) -> dict[str, str]:
    """Parse repeated KEY=VALUE CLI arguments."""
    overrides: dict[str, str] = {}
    for item in items:
        key, sep, value = item.partition("=")
        if not sep or not key:
            raise ValueError(f"expected KEY=VALUE, got {item!r}")
        overrides[key] = value
    return overrides


def resolve_benchmark_spec(spec_name: str, output_dir: Path) -> perf_harness.SpecInfo:
    """Resolve catalog specs plus benchmark-local generated specs."""
    if spec_name == COFFEECAN_SAFETY_SPEC_NAME:
        return stage_coffecan_safety_spec(output_dir)
    spec = perf_harness.require_spec(spec_name)
    final_expected_states = FINAL_SPEC_EXPECTED_STATE_COUNTS.get(spec_name)
    if final_expected_states is None:
        return spec
    if spec.expected_states is not None and spec.expected_states != final_expected_states:
        raise ValueError(
            f"{spec_name}: catalog expected_states={spec.expected_states} does not "
            f"match final benchmark expected_states={final_expected_states}"
        )
    if spec.expected_states == final_expected_states:
        return spec
    return spec._replace(expected_states=final_expected_states)


def stage_coffecan_safety_spec(output_dir: Path) -> perf_harness.SpecInfo:
    """Stage a fair CoffeeCan safety-only model for TLC and TLA2."""
    spec_dir = (output_dir / "generated-specs" / "CoffeeCanSafety1000").resolve()
    spec_dir.mkdir(parents=True, exist_ok=True)
    source = perf_harness.TLAPLUS_EXAMPLES_DIR / "CoffeeCan" / "CoffeeCan.tla"
    staged_source = spec_dir / "CoffeeCan.tla"
    wrapper_tla = spec_dir / "CoffeeCanSafetyBench.tla"
    wrapper_cfg = spec_dir / "CoffeeCanSafetyBench.cfg"
    if not source.exists():
        raise FileNotFoundError(f"CoffeeCan source not found: {source}")
    shutil.copy2(source, staged_source)
    wrapper_tla.write_text(
        (
            "---- MODULE CoffeeCanSafetyBench ----\n"
            "VARIABLE can\n\n"
            f"INSTANCE CoffeeCan WITH MaxBeanCount <- {COFFEECAN_SAFETY_BEANS}\n\n"
            "SafetyInit ==\n"
            "    can \\in {c \\in Can : "
            f"c.black + c.white = {COFFEECAN_SAFETY_BEANS}}}\n\n"
            "====\n"
        ),
        encoding="utf-8",
    )
    wrapper_cfg.write_text(
        (
            "INIT\n"
            "    SafetyInit\n\n"
            "NEXT\n"
            "    Next\n\n"
            "INVARIANTS\n"
            "    TypeInvariant\n"
        ),
        encoding="utf-8",
    )
    return perf_harness.SpecInfo(
        COFFEECAN_SAFETY_SPEC_NAME,
        str(wrapper_tla),
        str(wrapper_cfg),
        "CoffeeCan",
        expected_states=501500,
        timeout_seconds=300,
        notes=(
            "Generated safety-only CoffeeCan1000 model: exact-1000-bean initial "
            "frontier, Next, TypeInvariant, no temporal properties or fairness."
        ),
    )


@contextlib.contextmanager
def sanitized_tla2_env() -> Any:
    """Temporarily remove behavior-changing TLA2_* ambient env from benchmark runs."""
    missing = object()
    keys = [key for key in os.environ if key.startswith(SANITIZED_TLA2_ENV_PREFIX)]
    previous: dict[str, object] = {
        key: os.environ.get(key, missing) for key in keys
    }
    try:
        for key in keys:
            os.environ.pop(key, None)
        yield
    finally:
        for key, value in previous.items():
            if value is missing:
                os.environ.pop(key, None)
            else:
                os.environ[key] = str(value)


def parse_llvm2_telemetry(stdout: str, stderr: str) -> Llvm2Telemetry:
    """Extract LLVM2 coverage and activation signals from run output."""
    telemetry = Llvm2Telemetry(fallback_reasons=[])
    action_compiled_lines = 0
    action_failed_lines = 0
    invariant_compiled_lines = 0
    invariant_failed_lines = 0
    state_constraint_compiled_lines = 0
    state_constraint_failed_lines = 0
    saw_no_safe_actions = False
    explicit_native_fused_level_active: bool | None = None
    combined = latest_flat_primary_backend_segment("\n".join((stdout, stderr)))

    for raw_line in combined.splitlines():
        line = " ".join(raw_line.strip().split())
        if not line:
            continue
        lower = line.lower()

        for key, value in re.findall(
            r"\b("
            r"llvm2_actions_compiled|llvm2_actions_total|"
            r"llvm2_invariants_compiled|llvm2_invariants_total|"
            r"llvm2_state_constraints_compiled|llvm2_state_constraints_total|"
            r"llvm2_native_fused_invariant_count|"
            r"llvm2_native_fused_state_constraint_count"
            r")\s*[:=]\s*(\d+)\b",
            line,
        ):
            key = key.lower()
            setattr(telemetry, key, int(value))

        for key, value in re.findall(
            r"\b("
            r"compiled_bfs_step_active|compiled_bfs_level_active|"
            r"llvm2_bfs_level_active|llvm2_native_fused_level_active|"
            r"llvm2_native_fused_regular_invariants_checked|"
            r"llvm2_native_fused_local_dedup|"
            r"flat_state_primary"
            r")"
            r"\s*[:=]\s*(true|false)\b",
            line,
            flags=re.IGNORECASE,
        ):
            key = key.lower()
            parsed_value = value.lower() == "true"
            if key == "flat_state_primary":
                _set_sticky_false_bool(telemetry, key, parsed_value)
            elif key == "llvm2_native_fused_level_active":
                if parsed_value and explicit_native_fused_level_active is False:
                    continue
                explicit_native_fused_level_active = parsed_value
                telemetry.llvm2_native_fused_level_active = parsed_value
            else:
                setattr(telemetry, key, parsed_value)
            if key == "llvm2_bfs_level_active" and value.lower() == "true":
                telemetry.compiled_bfs_level_active = True
            if key == "llvm2_native_fused_level_active":
                if parsed_value:
                    telemetry.llvm2_bfs_level_active = True
                    telemetry.compiled_bfs_level_active = True

        if match := re.search(
            r"\bllvm2_bfs_level_loop_kind\s*[:=]\s*([A-Za-z0-9_ -]+?)(?=\s+\w+\s*[:=]|\s*$)",
            line,
        ):
            loop_kind = _normalize_loop_kind(match.group(1))
            telemetry.llvm2_bfs_level_active = True
            telemetry.compiled_bfs_level_active = True
            telemetry.llvm2_bfs_level_loop_kind = loop_kind
            if explicit_native_fused_level_active is not False:
                telemetry.llvm2_native_fused_level_active = (
                    loop_kind == "native_fused_llvm2_parent_loop"
                )

        if match := re.search(
            r"\bllvm2_native_fused_mode\s*[:=]\s*([A-Za-z0-9_ -]+?)(?=\s+\w+\s*[:=]|\s*$)",
            line,
        ):
            telemetry.llvm2_native_fused_mode = _normalize_loop_kind(match.group(1))

        if match := re.search(r"\[llvm2\] compiling (\d+) actions \((\d+) invariants,", line):
            telemetry.llvm2_actions_total = int(match.group(1))
            telemetry.llvm2_invariants_total = int(match.group(2))

        if match := re.search(
            r"\[llvm2\] compilation complete: "
            r"(\d+)/(\d+) actions, "
            r"(\d+)/(\d+) invariants, "
            r"(\d+)/(\d+) state constraints compiled",
            line,
        ):
            telemetry.llvm2_actions_compiled = int(match.group(1))
            telemetry.llvm2_actions_total = int(match.group(2))
            telemetry.llvm2_invariants_compiled = int(match.group(3))
            telemetry.llvm2_invariants_total = int(match.group(4))
            telemetry.llvm2_state_constraints_compiled = int(match.group(5))
            telemetry.llvm2_state_constraints_total = int(match.group(6))
        elif match := re.search(
            r"\[llvm2\] compilation complete: "
            r"(\d+)/(\d+) actions, (\d+)/(\d+) invariants compiled",
            line,
        ):
            telemetry.llvm2_actions_compiled = int(match.group(1))
            telemetry.llvm2_actions_total = int(match.group(2))
            telemetry.llvm2_invariants_compiled = int(match.group(3))
            telemetry.llvm2_invariants_total = int(match.group(4))
        elif match := re.search(
            r"\[llvm2\] compilation complete: (\d+)/(\d+) actions compiled",
            line,
        ):
            telemetry.llvm2_actions_compiled = int(match.group(1))
            telemetry.llvm2_actions_total = int(match.group(2))

        if "[llvm2] no safe action bytecodes available" in lower:
            saw_no_safe_actions = True

        if "[llvm2] compiled next-state for action" in lower or "[llvm2] specialized '" in lower:
            action_compiled_lines += 1
        if (
            "[llvm2] skipping action" in lower
            or "[llvm2] failed to compile action" in lower
            or "[llvm2] failed to compile specialization" in lower
        ):
            action_failed_lines += 1

        if "[llvm2] compiled invariant" in lower:
            invariant_compiled_lines += 1
        if "[llvm2] failed to compile invariant" in lower:
            invariant_failed_lines += 1
        if "[llvm2] compiled state constraint" in lower:
            state_constraint_compiled_lines += 1
        if (
            "[llvm2] failed to compile state constraint" in lower
            or "[llvm2] missing bytecode for state constraint" in lower
        ):
            state_constraint_failed_lines += 1

        if "[compiled-bfs]" in lower and (
            "activating compiled bfs loop" in lower
            or "starting compiled bfs level loop" in lower
            or re.search(r"\[compiled-bfs\] (?:fused )?level \d+:", lower)
            or "completed:" in lower
        ):
            telemetry.compiled_bfs_step_active = True

        if match := re.search(
            r"\[compiled-bfs\]\s+starting compiled BFS level loop "
            r"\(([\d,]+) initial states in arena, fused=(true|false)\)",
            line,
        ):
            telemetry.compiled_bfs_step_active = True
            telemetry.compiled_bfs_level_loop_started = True
            telemetry.compiled_bfs_level_loop_initial_states = int(
                match.group(1).replace(",", "")
            )
            telemetry.compiled_bfs_level_loop_fused = match.group(2) == "true"
            if telemetry.compiled_bfs_level_loop_fused:
                telemetry.compiled_bfs_level_active = True

        completion = _parse_compiled_bfs_completion(line)
        if completion:
            _record_compiled_bfs_completion(telemetry, completion)
        if _is_compiled_bfs_execution_timing_line(line, completion):
            _record_compiled_bfs_execution_timing(telemetry, line)

        if "[compiled-bfs]" in lower and (
            "fused=true" in lower or re.search(r"\[compiled-bfs\] fused level \d+:", lower)
        ):
            telemetry.compiled_bfs_level_active = True

        if match := COMPILED_BFS_LEVEL_BUILT_REGEX.search(line):
            telemetry.llvm2_bfs_level_active = True
            telemetry.compiled_bfs_level_active = True
            if match.group("state_len") is not None:
                telemetry.llvm2_native_fused_state_len = int(
                    match.group("state_len").replace(",", "")
                )
            loop_kind = _normalize_loop_kind(match.group("label"))
            if loop_kind.endswith("native_fused_llvm2_parent_loop"):
                telemetry.llvm2_bfs_level_loop_kind = "native_fused_llvm2_parent_loop"
                telemetry.llvm2_native_fused_level_built = True
                if explicit_native_fused_level_active is not False:
                    telemetry.llvm2_native_fused_level_active = True
                if loop_kind.startswith("state_constrained"):
                    telemetry.llvm2_native_fused_mode = "state_constraint_checking"
                elif loop_kind.startswith("action_only"):
                    telemetry.llvm2_native_fused_mode = "action_only"
                elif loop_kind.startswith("invariant_checking"):
                    telemetry.llvm2_native_fused_mode = "invariant_checking"
            else:
                telemetry.llvm2_bfs_level_loop_kind = loop_kind
                telemetry.llvm2_native_fused_level_active = False

        if "[llvm2-native-bfs]" in lower:
            _record_native_bfs_trace_telemetry(telemetry, line)

        if "flat_state_primary=true" in lower:
            _set_sticky_false_bool(telemetry, "flat_state_primary", True)
        elif "flat_state_primary=false" in lower:
            _set_sticky_false_bool(telemetry, "flat_state_primary", False)
        if "[flat-frontier]" in lower:
            flat_frontier_active = _parse_flat_frontier_active(line)
            if flat_frontier_active is not None:
                _set_sticky_false_bool(
                    telemetry,
                    "flat_bfs_frontier_active",
                    flat_frontier_active,
                )
            if match := re.search(r"\b(\d+)\s+fallback\b", lower):
                telemetry.flat_bfs_frontier_fallbacks = _max_known(
                    telemetry.flat_bfs_frontier_fallbacks,
                    int(match.group(1)),
                )

        if _is_fallback_reason(line):
            _append_reason(telemetry.fallback_reasons, line)

    if telemetry.llvm2_actions_compiled is None:
        if action_compiled_lines or action_failed_lines:
            telemetry.llvm2_actions_compiled = action_compiled_lines
            telemetry.llvm2_actions_total = action_compiled_lines + action_failed_lines
        elif saw_no_safe_actions:
            telemetry.llvm2_actions_compiled = 0
            telemetry.llvm2_actions_total = 0

    if telemetry.llvm2_invariants_compiled is None:
        if invariant_compiled_lines or invariant_failed_lines:
            telemetry.llvm2_invariants_compiled = invariant_compiled_lines
            telemetry.llvm2_invariants_total = invariant_compiled_lines + invariant_failed_lines
        elif telemetry.llvm2_invariants_total == 0:
            telemetry.llvm2_invariants_compiled = 0

    if telemetry.llvm2_invariants_total is None and telemetry.llvm2_invariants_compiled == 0:
        telemetry.llvm2_invariants_total = 0

    if telemetry.llvm2_state_constraints_compiled is None:
        if state_constraint_compiled_lines or state_constraint_failed_lines:
            telemetry.llvm2_state_constraints_compiled = state_constraint_compiled_lines
            telemetry.llvm2_state_constraints_total = (
                state_constraint_compiled_lines + state_constraint_failed_lines
            )
        elif telemetry.llvm2_state_constraints_total == 0:
            telemetry.llvm2_state_constraints_compiled = 0

    if (
        telemetry.llvm2_state_constraints_total is None
        and telemetry.llvm2_state_constraints_compiled == 0
    ):
        telemetry.llvm2_state_constraints_total = 0

    if telemetry.compiled_bfs_execution_nanos is not None and not _positive_float(
        telemetry.compiled_bfs_execution_seconds
    ):
        telemetry.compiled_bfs_execution_seconds = (
            telemetry.compiled_bfs_execution_nanos / 1_000_000_000.0
        )

    return telemetry


def latest_flat_primary_backend_segment(combined: str) -> str:
    """Return the latest post-flat-primary backend telemetry segment if present."""
    lines = combined.splitlines(keepends=True)
    marker_line_index = None
    for idx, line in enumerate(lines):
        if FLAT_PRIMARY_REBUILD_MARKER in line:
            marker_line_index = idx
    if marker_line_index is None:
        return combined

    for idx in range(marker_line_index - 1, -1, -1):
        if re.search(r"\bflat_state_primary\s*[:=]\s*true\b", lines[idx]):
            return "".join((lines[idx], *lines[marker_line_index:]))
    return "".join(lines[marker_line_index:])


def _normalize_loop_kind(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", value.lower()).strip("_")


def _parse_compiled_bfs_completion(line: str) -> tuple[int, int, int, int, int] | None:
    match = re.search(
        r"\[compiled-bfs\]\s+completed:\s+"
        r"(\d[\d,]*)\s+levels,\s+"
        r"(\d[\d,]*)\s+parents,\s+"
        r"(\d[\d,]*)\s+generated,\s+"
        r"(\d[\d,]*)\s+new,\s+"
        r"(\d[\d,]*)\s+total states\b",
        line,
        flags=re.IGNORECASE,
    )
    if not match:
        return None
    levels, parents, generated, new, total_states = (
        int(value.replace(",", "")) for value in match.groups()
    )
    return levels, parents, generated, new, total_states


def _is_compiled_bfs_execution_timing_line(
    line: str,
    completion: tuple[int, int, int, int, int] | None,
) -> bool:
    lower = line.lower()
    return completion is not None or (
        "[compiled-bfs]" in lower and "compiled_bfs_execution_" in lower
    )


def _record_compiled_bfs_execution_timing(
    telemetry: Llvm2Telemetry,
    line: str,
) -> None:
    for match in COMPILED_BFS_EXECUTION_NANOS_REGEX.finditer(line):
        telemetry.compiled_bfs_execution_nanos = int(match.group(1).replace(",", ""))
    for match in COMPILED_BFS_EXECUTION_SECONDS_REGEX.finditer(line):
        telemetry.compiled_bfs_execution_seconds = float(match.group(1))


def _record_native_bfs_trace_telemetry(
    telemetry: Llvm2Telemetry,
    line: str,
) -> None:
    if match := re.search(r"\blocal_dedup=(true|false)\b", line, re.IGNORECASE):
        telemetry.llvm2_native_fused_local_dedup = match.group(1).lower() == "true"
    if match := re.search(r"\bgenerated=(\d[\d,]*)\b", line, re.IGNORECASE):
        telemetry.llvm2_native_bfs_trace_generated = _max_known(
            telemetry.llvm2_native_bfs_trace_generated,
            int(match.group(1).replace(",", "")),
        )
    if match := re.search(r"\bstate_count=(\d[\d,]*)\b", line, re.IGNORECASE):
        telemetry.llvm2_native_bfs_trace_state_count = _max_known(
            telemetry.llvm2_native_bfs_trace_state_count,
            int(match.group(1).replace(",", "")),
        )
    if match := re.search(r"\bparents_processed=(\d[\d,]*)\b", line, re.IGNORECASE):
        telemetry.llvm2_native_bfs_trace_parents_processed = _max_known(
            telemetry.llvm2_native_bfs_trace_parents_processed,
            int(match.group(1).replace(",", "")),
        )


def _record_compiled_bfs_completion(
    telemetry: Llvm2Telemetry,
    completion: tuple[int, int, int, int, int],
) -> None:
    levels, parents, generated, new, total_states = completion
    telemetry.compiled_bfs_levels_completed = _min_known(
        telemetry.compiled_bfs_levels_completed,
        levels,
    )
    telemetry.compiled_bfs_parents_processed = _min_known(
        telemetry.compiled_bfs_parents_processed,
        parents,
    )
    telemetry.compiled_bfs_successors_generated = _min_known(
        telemetry.compiled_bfs_successors_generated,
        generated,
    )
    telemetry.compiled_bfs_successors_new = _min_known(
        telemetry.compiled_bfs_successors_new,
        new,
    )
    telemetry.compiled_bfs_total_states = _max_known(
        telemetry.compiled_bfs_total_states,
        total_states,
    )
    if levels == 0 and parents == 0 and generated == 0 and new == 0:
        telemetry.compiled_bfs_zero_work = True


def _min_known(current: int | None, value: int) -> int:
    return value if current is None else min(current, value)


def _max_known(current: int | None, value: int) -> int:
    return value if current is None else max(current, value)


def _parse_flat_frontier_active(line: str) -> bool | None:
    lower = line.lower()
    if "flat_bfs_frontier_active=false" in lower:
        return False
    if "flat_bfs_frontier_active=true" not in lower:
        return None
    fallback_match = re.search(r"\b(\d+)\s+fallback\b", lower)
    return fallback_match is not None and int(fallback_match.group(1)) == 0


def _set_sticky_false_bool(telemetry: Llvm2Telemetry, key: str, value: bool) -> None:
    if value is False:
        setattr(telemetry, key, False)
    elif getattr(telemetry, key) is not False:
        setattr(telemetry, key, True)


def _is_fallback_reason(line: str) -> bool:
    lower = line.lower()
    if "attempting compile via tmir anyway" in lower:
        return False
    fallback_scan = re.sub(r"\(\s*0\s+failed\s*\)", "", lower)
    llvm2_line = "[llvm2]" in lower or "[llvm2][tmir-dump]" in lower
    llvm2_error = "llvm2" in fallback_scan and any(
        token in fallback_scan
        for token in (
            "failed",
            "fallback",
            "falling back",
            "skip",
            "skipping",
            "skipped",
            "unavailable",
            "not eligible",
            "missing bytecode",
            "missing native code",
            "unsupported",
            "not yet supported",
            "lowering",
            "outside the scalar",
            "requires",
        )
    )
    llvm2_selftest_runtime_issue = "[llvm2-selftest]" in lower and any(
        token in lower
        for token in (
            "failed",
            "runtime_error",
            "runtime error",
            "failing closed",
            "missing function pointer",
            "requested interpreter fallback",
            "fallback",
        )
    )
    compiled_bfs_fallback = _is_compiled_bfs_runtime_issue(line)
    flat_fallback = "[flat_state]" in lower and ("fail" in lower or "fallback" in lower)
    flat_frontier_fallback = "[flat-frontier]" in lower and re.search(
        r"\b[1-9]\d*\s+fallback\b",
        lower,
    )
    return (
        (llvm2_line and llvm2_error)
        or llvm2_selftest_runtime_issue
        or compiled_bfs_fallback
        or flat_fallback
        or bool(flat_frontier_fallback)
    )


def _is_compiled_bfs_runtime_issue(line: str) -> bool:
    lower = line.lower()
    if "[compiled-bfs]" not in lower:
        return False
    if "state constraints require" in lower:
        return True
    return any(
        token in lower
        for token in (
            "interpreter path used",
            "not enabled",
            "compiled bfs disabled",
            "fused level build failed",
            "fused level error",
            "became unavailable",
            "fallback",
            "falling back",
            "step error",
            "disabling",
            "disabled",
        )
    )


def _is_allowed_invariant_rust_fallback(reason: str) -> bool:
    lower = reason.lower()
    if "[llvm2]" not in lower:
        return False
    return (
        "failed to compile invariant" in lower
        or "missing bytecode for invariant" in lower
        or "invariant bytecode:" in lower
        or "invariant bytecode skip" in lower
        or "invariant-checking native fused compiledbfslevel unavailable" in lower
        or (
            "native fused compiledbfslevel using action-only fallback" in lower
            and "invariant" in lower
        )
        or (
            "compiledbfsstep not eligible" in lower
            and "invariants compiled" in lower
        )
    )


def _is_state_constraint_fused_level_skip_reason(reason: str) -> bool:
    normalized = " ".join(reason.strip().split())
    expected = (
        "[compiled-bfs] fused level skipped: "
        "state constraints require llvm2 native fused constraint support"
    )
    lower = normalized.lower()
    return (
        re.fullmatch(
            rf"{re.escape(expected.lower())}(?: \(first state constraint: [^)]+\))?",
            lower,
        )
        is not None
    )


def _is_benign_native_fused_state_constraint_diagnostic(reason: str) -> bool:
    return _is_state_constraint_step_skip_reason(
        reason
    ) or _is_state_constraint_fused_level_skip_reason(reason)


def _state_constraint_native_fused_execution_successful(
    telemetry: dict[str, Any] | None,
) -> bool:
    if telemetry is None:
        return False
    actual = _telemetry_int(telemetry, "llvm2_native_fused_state_constraint_count")
    compiled = _telemetry_int(telemetry, "llvm2_state_constraints_compiled")
    total = _telemetry_int(telemetry, "llvm2_state_constraints_total")
    return (
        actual is not None
        and actual > 0
        and compiled == actual
        and total == actual
        and _native_fused_execution_evidence_active(telemetry)
        and telemetry.get("llvm2_native_fused_mode") == "state_constraint_checking"
        and telemetry.get("llvm2_native_fused_regular_invariants_checked") is True
        and telemetry.get("flat_state_primary") is True
        and telemetry.get("flat_bfs_frontier_active") is True
        and _telemetry_int(telemetry, "flat_bfs_frontier_fallbacks") == 0
    )


def _allows_invariant_rust_fallbacks(
    args: argparse.Namespace,
    telemetry: dict[str, Any] | None,
) -> bool:
    if not getattr(args, "allow_llvm2_invariant_rust_fallbacks", False):
        return False
    if not telemetry:
        return False
    return (
        _native_fused_execution_evidence_active(telemetry)
        and telemetry.get("llvm2_native_fused_mode") == "action_only"
        and telemetry.get("flat_state_primary") is True
        and telemetry.get("flat_bfs_frontier_active") is True
        and _telemetry_int(telemetry, "flat_bfs_frontier_fallbacks") == 0
    )


def _is_state_constraint_step_skip_reason(reason: str) -> bool:
    normalized = " ".join(reason.strip().split())
    expected = STATE_CONSTRAINT_STEP_SKIP_REASON.lower()
    lower = normalized.lower()
    return (
        re.fullmatch(
            rf"{re.escape(expected)}(?: \(first state constraint: [^)]+\))?",
            lower,
        )
        is not None
    )


def _disallowed_llvm2_fallback_reasons(
    reasons: list[str],
    spec_name: str,
    args: argparse.Namespace,
    telemetry: dict[str, Any] | None,
) -> list[str]:
    state_constrained_native_fused = _state_constrained_native_fused_active(
        spec_name,
        telemetry,
    )
    allow_state_constraint_step_skip = state_constrained_native_fused
    reasons = [
        reason
        for reason in reasons
        if not (
            allow_state_constraint_step_skip
            and _is_benign_native_fused_state_constraint_diagnostic(reason)
        )
    ]
    if not _allows_invariant_rust_fallbacks(args, telemetry):
        return reasons
    return [
        reason
        for reason in reasons
        if not _is_allowed_invariant_rust_fallback(reason)
    ]


def _compiled_bfs_runtime_issue_reasons(telemetry: dict[str, Any] | None) -> list[str]:
    if not telemetry:
        return []
    state_constraint_native_fused = _state_constraint_native_fused_execution_successful(
        telemetry,
    )
    return [
        reason
        for reason in telemetry.get("fallback_reasons") or []
        if _is_compiled_bfs_runtime_issue(reason)
        and not (
            state_constraint_native_fused
            and _is_benign_native_fused_state_constraint_diagnostic(reason)
        )
    ]


def _compiled_bfs_zero_work_detail(telemetry: dict[str, Any] | None) -> str | None:
    if not telemetry:
        return None
    levels = _telemetry_int(telemetry, "compiled_bfs_levels_completed")
    parents = _telemetry_int(telemetry, "compiled_bfs_parents_processed")
    generated = _telemetry_int(telemetry, "compiled_bfs_successors_generated")
    new = _telemetry_int(telemetry, "compiled_bfs_successors_new")
    zero_counters = (
        levels == 0
        and parents == 0
        and generated == 0
        and new == 0
    )
    if telemetry.get("compiled_bfs_zero_work") is not True and not zero_counters:
        return None
    total_states = _telemetry_int(telemetry, "compiled_bfs_total_states")
    return (
        f"(levels={levels!r}, parents={parents!r}, generated={generated!r}, "
        f"new={new!r}, total_states={total_states!r})"
    )


def _compiled_bfs_positive_completion_detail(
    telemetry: dict[str, Any] | None,
) -> str | None:
    if not telemetry:
        return "(levels=None, parents=None, generated=None, total_states=None)"
    levels = _telemetry_int(telemetry, "compiled_bfs_levels_completed")
    parents = _telemetry_int(telemetry, "compiled_bfs_parents_processed")
    generated = _telemetry_int(telemetry, "compiled_bfs_successors_generated")
    total_states = _telemetry_int(telemetry, "compiled_bfs_total_states")
    if (
        levels is not None
        and levels > 0
        and parents is not None
        and parents > 0
        and generated is not None
        and generated > 0
        and total_states is not None
        and total_states > 0
    ):
        return None
    return (
        f"(levels={levels!r}, parents={parents!r}, "
        f"generated={generated!r}, total_states={total_states!r})"
    )


def _compiled_bfs_successor_evidence_detail(
    run: dict[str, Any],
    telemetry: dict[str, Any] | None,
) -> str | None:
    successors_new = _telemetry_int(telemetry, "compiled_bfs_successors_new")
    total_states = _telemetry_int(telemetry, "compiled_bfs_total_states")
    states_found = run.get("states_found")
    detail = (
        f"(compiled_bfs_successors_new={successors_new!r}, "
        f"compiled_bfs_total_states={total_states!r}, "
        f"states_found={states_found!r})"
    )
    if successors_new is None or successors_new <= 0:
        return detail
    if (
        not isinstance(total_states, int)
        or isinstance(total_states, bool)
        or not isinstance(states_found, int)
        or isinstance(states_found, bool)
        or total_states != states_found
    ):
        return detail
    return None


def _run_transition_failure(run: dict[str, Any]) -> str | None:
    if "transitions" not in run:
        return None
    transitions = run.get("transitions")
    if not isinstance(transitions, int) or isinstance(transitions, bool) or transitions <= 0:
        return f"transition work was not observed (transitions={transitions!r})"
    return None


def _append_reason(reasons: list[str] | None, line: str) -> None:
    if reasons is None:
        return
    if len(line) > MAX_REASON_CHARS:
        line = f"{line[: MAX_REASON_CHARS - 3]}..."
    if line in reasons:
        return
    if len(reasons) < MAX_FALLBACK_REASONS:
        reasons.append(line)
    elif TRUNCATED_FALLBACK_REASON not in reasons:
        reasons[-1] = TRUNCATED_FALLBACK_REASON


def resolve_tla2_binary(args: argparse.Namespace) -> Path | None:
    """Build once with LLVM2 enabled or resolve an explicit tla2 binary."""
    if args.tla2_bin:
        binary = Path(args.tla2_bin)
        if not binary.exists():
            log.error("binary not found: %s", binary)
            return None
        return binary

    target_dir = perf_harness.resolve_target_dir(
        args.target_dir, namespace="benchmark_single_thread"
    )
    build_cmd = perf_harness.CommandSpec(
        argv=[
            "build",
            "--profile",
            args.cargo_profile,
            "-p",
            "tla-cli",
            "--features",
            "llvm2",
            "--target-dir",
            str(target_dir),
            "--bin",
            "tla2",
        ],
        cwd=perf_harness.REPO_ROOT,
    )
    log.info("Building tla2... (%s)", perf_harness.command_to_string(build_cmd.argv))
    build_result = perf_harness.run_command(build_cmd, timeout=900)
    if build_result.returncode != 0:
        log.error("Build failed:\n%s", build_result.stderr)
        return None

    binary = perf_harness.resolve_binary_path(target_dir, args.cargo_profile)
    if not binary.exists():
        log.error("built binary not found: %s", binary)
        return None
    log.info("Using binary: %s", binary)
    return binary


def run_tla2_mode(
    spec: perf_harness.SpecInfo,
    *,
    mode: str,
    run_index: int,
    tla2_bin: Path,
    timeout: int,
    output_dir: Path,
    common_flags: list[str],
    env_overrides: Mapping[str, str] | None = None,
) -> ModeRunResult:
    """Run one single-thread TLA2 measurement for a named backend mode."""
    if mode not in {"interp", "llvm2"}:
        raise ValueError(f"unsupported mode: {mode}")

    perf_harness.ensure_output_dir(output_dir)

    extra_flags = list(common_flags)
    if mode == "interp":
        extra_flags.extend(["--backend", "interpreter"])
        extra_env = {
            "TLA2_LLVM2": "0",
            "TLA2_LLVM2_BFS": "0",
            "TLA2_BYTECODE_VM": "1",
            "TLA2_AUTO_POR": "0",
        }
    else:
        extra_flags.extend(["--backend", "llvm2"])
        extra_env = {
            "TLA2_LLVM2": "1",
            "TLA2_LLVM2_BFS": "1",
            "TLA2_LLVM2_EXISTS": "1",
            "TLA2_BYTECODE_VM": "1",
            "TLA2_AUTO_POR": "0",
        }
    extra_env.update(env_overrides or {})

    cmd = perf_harness.build_tla2_check_command(
        spec,
        binary_path=tla2_bin,
        extra_flags=extra_flags,
        extra_env=extra_env,
        workers=1,
        profile_enum=False,
        profile_eval=False,
    )
    with sanitized_tla2_env():
        result = perf_harness.run_command(cmd, timeout=timeout)

    (output_dir / "stdout.txt").write_text(result.stdout, encoding="utf-8")
    (output_dir / "stderr.txt").write_text(result.stderr, encoding="utf-8")
    perf_harness.write_json(output_dir / "command.json", result.to_dict())

    parsed = perf_harness.parse_profiling_output(result.stdout, result.stderr)
    llvm2_telemetry = (
        parse_llvm2_telemetry(result.stdout, result.stderr)
        if mode == "llvm2"
        else None
    )
    return ModeRunResult(
        tool="tla2",
        mode=mode,
        spec_name=spec.name,
        run_index=run_index,
        elapsed_seconds=result.elapsed_seconds,
        states_found=parsed["states_found"],
        transitions=parsed["transitions"],
        returncode=result.returncode,
        error=parsed["error"],
        artifact_dir=perf_harness.repo_relative(output_dir),
        env_overrides=dict(result.env_overrides) if result.env_overrides else None,
        llvm2_telemetry=llvm2_telemetry,
    )


def median_or_none(values: list[float]) -> float | None:
    """Return the median of a list, or None if it is empty."""
    if not values:
        return None
    return float(statistics.median(values))


def aggregate_llvm2_telemetry(results: list[ModeRunResult]) -> dict[str, Any] | None:
    """Summarize LLVM2 telemetry conservatively across repeated runs."""
    telemetry = [run.llvm2_telemetry for run in results if run.llvm2_telemetry is not None]
    if not telemetry:
        return None

    def known_values(field: str) -> list[Any]:
        values = [getattr(item, field) for item in telemetry]
        return [value for value in values if value is not None]

    def min_int(field: str) -> int | None:
        values = [
            value
            for value in known_values(field)
            if isinstance(value, int) and not isinstance(value, bool)
        ]
        return min(values) if values else None

    def max_int(field: str) -> int | None:
        values = [
            value
            for value in known_values(field)
            if isinstance(value, int) and not isinstance(value, bool)
        ]
        return max(values) if values else None

    def max_float(field: str) -> float | None:
        values = [
            float(value)
            for value in known_values(field)
            if isinstance(value, (int, float))
            and not isinstance(value, bool)
            and math.isfinite(float(value))
        ]
        return max(values) if values else None

    def strict_bool(field: str) -> bool | None:
        values = [getattr(item, field) for item in telemetry]
        if any(value is False for value in values):
            return False
        if all(value is True for value in values):
            return True
        return None

    def strict_all_true(field: str) -> bool:
        return all(getattr(item, field) is True for item in telemetry)

    def count_true(field: str) -> int:
        return sum(1 for item in telemetry if getattr(item, field) is True)

    fallback_reasons: list[str] = []
    for item in telemetry:
        for reason in item.fallback_reasons or []:
            _append_reason(fallback_reasons, reason)

    return {
        "llvm2_actions_compiled": min_int("llvm2_actions_compiled"),
        "llvm2_actions_total": max_int("llvm2_actions_total"),
        "llvm2_invariants_compiled": min_int("llvm2_invariants_compiled"),
        "llvm2_invariants_total": max_int("llvm2_invariants_total"),
        "llvm2_state_constraints_compiled": min_int("llvm2_state_constraints_compiled"),
        "llvm2_state_constraints_total": max_int("llvm2_state_constraints_total"),
        "compiled_bfs_step_active": strict_all_true("compiled_bfs_step_active"),
        "compiled_bfs_level_active": strict_all_true("compiled_bfs_level_active"),
        "compiled_bfs_level_loop_started": strict_all_true(
            "compiled_bfs_level_loop_started"
        ),
        "compiled_bfs_level_loop_initial_states": min_int(
            "compiled_bfs_level_loop_initial_states"
        ),
        "compiled_bfs_level_loop_fused": strict_bool("compiled_bfs_level_loop_fused"),
        "compiled_bfs_levels_completed": min_int("compiled_bfs_levels_completed"),
        "compiled_bfs_parents_processed": min_int("compiled_bfs_parents_processed"),
        "compiled_bfs_successors_generated": min_int("compiled_bfs_successors_generated"),
        "compiled_bfs_successors_new": min_int("compiled_bfs_successors_new"),
        "compiled_bfs_total_states": max_int("compiled_bfs_total_states"),
        "compiled_bfs_zero_work": any(
            item.compiled_bfs_zero_work is True for item in telemetry
        ),
        "compiled_bfs_execution_nanos": max_int("compiled_bfs_execution_nanos"),
        "compiled_bfs_execution_seconds": _max_compiled_bfs_execution_seconds(
            telemetry
        ),
        "llvm2_bfs_level_active": strict_all_true("llvm2_bfs_level_active"),
        "llvm2_native_fused_level_built": strict_all_true(
            "llvm2_native_fused_level_built"
        ),
        "llvm2_native_fused_level_active": strict_all_true(
            "llvm2_native_fused_level_active"
        ),
        "llvm2_native_fused_regular_invariants_checked": all(
            item.llvm2_native_fused_regular_invariants_checked is True for item in telemetry
        ),
        "llvm2_native_fused_mode": _aggregate_native_fused_mode(telemetry),
        "llvm2_native_fused_invariant_count": _aggregate_native_fused_invariant_count(
            telemetry
        ),
        "llvm2_native_fused_state_constraint_count": (
            _aggregate_native_fused_state_constraint_count(telemetry)
        ),
        "llvm2_native_fused_state_len": _aggregate_native_fused_state_len(telemetry),
        "llvm2_native_fused_local_dedup": strict_bool(
            "llvm2_native_fused_local_dedup"
        ),
        "llvm2_native_bfs_trace_generated": max_int(
            "llvm2_native_bfs_trace_generated"
        ),
        "llvm2_native_bfs_trace_state_count": max_int(
            "llvm2_native_bfs_trace_state_count"
        ),
        "llvm2_native_bfs_trace_parents_processed": max_int(
            "llvm2_native_bfs_trace_parents_processed"
        ),
        "llvm2_bfs_level_loop_kind": _aggregate_loop_kind(telemetry),
        "flat_state_primary": strict_bool("flat_state_primary"),
        "flat_bfs_frontier_active": strict_bool("flat_bfs_frontier_active"),
        "flat_bfs_frontier_fallbacks": max_int("flat_bfs_frontier_fallbacks"),
        "runs_with_compiled_bfs_step_active": count_true("compiled_bfs_step_active"),
        "runs_with_compiled_bfs_level_active": count_true("compiled_bfs_level_active"),
        "runs_with_compiled_bfs_level_loop_started": count_true(
            "compiled_bfs_level_loop_started"
        ),
        "runs_with_compiled_bfs_zero_work": sum(
            1 for item in telemetry if item.compiled_bfs_zero_work is True
        ),
        "runs_with_compiled_bfs_execution_timing": sum(
            1
            for item in telemetry
            if _positive_float(item.compiled_bfs_execution_seconds)
            or (
                isinstance(item.compiled_bfs_execution_nanos, int)
                and not isinstance(item.compiled_bfs_execution_nanos, bool)
                and item.compiled_bfs_execution_nanos > 0
            )
        ),
        "runs_with_llvm2_native_fused_level_active": sum(
            1 for item in telemetry if item.llvm2_native_fused_level_active is True
        ),
        "runs_with_llvm2_native_fused_level_built": sum(
            1 for item in telemetry if item.llvm2_native_fused_level_built is True
        ),
        "runs_with_llvm2_native_fused_regular_invariants_checked": sum(
            1
            for item in telemetry
            if item.llvm2_native_fused_regular_invariants_checked is True
        ),
        "runs_with_llvm2_native_fused_state_constraints": sum(
            1
            for item in telemetry
            if (
                isinstance(item.llvm2_native_fused_state_constraint_count, int)
                and not isinstance(item.llvm2_native_fused_state_constraint_count, bool)
                and item.llvm2_native_fused_state_constraint_count > 0
            )
        ),
        "runs_with_flat_bfs_frontier_active": sum(
            1 for item in telemetry if item.flat_bfs_frontier_active is True
        ),
        "fallback_reasons": fallback_reasons,
    }


def _aggregate_loop_kind(telemetry: list[Llvm2Telemetry]) -> str | None:
    kinds = {item.llvm2_bfs_level_loop_kind for item in telemetry if item.llvm2_bfs_level_loop_kind}
    if not kinds:
        return None
    if len(kinds) == 1:
        return next(iter(kinds))
    return "mixed"


def _aggregate_native_fused_mode(telemetry: list[Llvm2Telemetry]) -> str | None:
    native_runs = [item for item in telemetry if item.llvm2_native_fused_level_active is True]
    if not native_runs:
        return None
    modes = {item.llvm2_native_fused_mode for item in native_runs}
    if None in modes:
        return None
    if not modes:
        return None
    if len(modes) == 1:
        return next(iter(modes))
    return "mixed"


def _aggregate_native_fused_invariant_count(telemetry: list[Llvm2Telemetry]) -> int | None:
    native_runs = [item for item in telemetry if item.llvm2_native_fused_level_active is True]
    if not native_runs:
        return None
    counts = [item.llvm2_native_fused_invariant_count for item in native_runs]
    if any(count is None for count in counts):
        return None
    return min(count for count in counts if count is not None)


def _aggregate_native_fused_state_constraint_count(
    telemetry: list[Llvm2Telemetry],
) -> int | None:
    native_runs = [item for item in telemetry if item.llvm2_native_fused_level_active is True]
    if not native_runs:
        return None
    counts = [item.llvm2_native_fused_state_constraint_count for item in native_runs]
    if any(count is None for count in counts):
        return None
    return min(count for count in counts if count is not None)


def _aggregate_native_fused_state_len(telemetry: list[Llvm2Telemetry]) -> int | None:
    native_runs = [item for item in telemetry if item.llvm2_native_fused_level_active is True]
    if not native_runs:
        return None
    lengths = [item.llvm2_native_fused_state_len for item in native_runs]
    if any(length is None for length in lengths):
        return None
    if len(set(lengths)) != 1:
        return None
    return lengths[0]


def aggregate_mode(results: list[ModeRunResult]) -> dict[str, Any]:
    """Summarize repeated runs for one mode."""
    times = [run.elapsed_seconds for run in results if _run_ok(run)]
    execution_times = [
        execution_seconds
        for run in results
        if _run_ok(run)
        for execution_seconds in [_compiled_bfs_execution_seconds(run.llvm2_telemetry)]
        if execution_seconds is not None
    ]
    states = [run.states_found for run in results]
    state_values = {state for state in states if state is not None}
    summary = {
        "runs": [run.to_dict() for run in results],
        "median_seconds": median_or_none(times),
        "state_values": sorted(state_values),
        "consistent_states": len(state_values) <= 1,
        "all_ok": all(_run_ok(run) for run in results),
    }
    if telemetry := aggregate_llvm2_telemetry(results):
        summary["telemetry"] = telemetry
    if execution_times:
        summary["execution_median_seconds"] = median_or_none(execution_times)
    return summary


def _compiled_bfs_execution_seconds(
    telemetry: Llvm2Telemetry | dict[str, Any] | None,
) -> float | None:
    if telemetry is None:
        return None
    if isinstance(telemetry, Llvm2Telemetry):
        seconds = telemetry.compiled_bfs_execution_seconds
        nanos = telemetry.compiled_bfs_execution_nanos
    else:
        seconds = telemetry.get("compiled_bfs_execution_seconds")
        nanos = telemetry.get("compiled_bfs_execution_nanos")
    if isinstance(nanos, int) and not isinstance(nanos, bool) and nanos > 0:
        return nanos / 1_000_000_000.0
    if _positive_float(seconds):
        return float(seconds)
    return None


def _max_compiled_bfs_execution_seconds(
    telemetry: list[Llvm2Telemetry],
) -> float | None:
    values = [
        execution_seconds
        for item in telemetry
        for execution_seconds in [_compiled_bfs_execution_seconds(item)]
        if execution_seconds is not None
    ]
    if not values:
        return None
    return max(values)


def _compiled_bfs_execution_seconds_mismatch(
    telemetry: Llvm2Telemetry | dict[str, Any] | None,
) -> tuple[float, float] | None:
    if telemetry is None:
        return None
    if isinstance(telemetry, Llvm2Telemetry):
        seconds = telemetry.compiled_bfs_execution_seconds
        nanos = telemetry.compiled_bfs_execution_nanos
    else:
        seconds = telemetry.get("compiled_bfs_execution_seconds")
        nanos = telemetry.get("compiled_bfs_execution_nanos")
    if not _positive_float(seconds):
        return None
    if not (isinstance(nanos, int) and not isinstance(nanos, bool) and nanos > 0):
        return None
    derived_seconds = nanos / 1_000_000_000.0
    reported_seconds = float(seconds)
    if math.isclose(
        reported_seconds,
        derived_seconds,
        rel_tol=COMPILED_BFS_EXECUTION_SECONDS_REL_TOL,
        abs_tol=COMPILED_BFS_EXECUTION_SECONDS_ABS_TOL,
    ):
        return None
    return reported_seconds, derived_seconds


def _returncode_ok(returncode: Any) -> bool:
    return isinstance(returncode, int) and not isinstance(returncode, bool) and returncode == 0


def _run_ok(run: Any) -> bool:
    return _returncode_ok(run.returncode) and getattr(run, "error", None) is None


def _all_mode_runs_match_expected(
    results: list[ModeRunResult],
    expected_states: int | None,
) -> bool | None:
    if expected_states is None:
        return None
    return all(run.states_found == expected_states for run in results)


def _all_tlc_runs_match_expected(
    results: list[scaling.ScalingRunResult],
    expected_states: int | None,
) -> bool | None:
    if expected_states is None:
        return None
    return all(run.states_found == expected_states for run in results)


def summarize_spec(
    spec: perf_harness.SpecInfo,
    interp_runs: list[ModeRunResult],
    llvm2_runs: list[ModeRunResult],
    tlc_runs: list[scaling.ScalingRunResult],
) -> dict[str, Any]:
    """Build one summary row for a spec."""
    interp_summary = aggregate_mode(interp_runs)
    llvm2_summary = aggregate_mode(llvm2_runs)
    tlc_times = [run.elapsed_seconds for run in tlc_runs if _run_ok(run)]
    tlc_states = {run.states_found for run in tlc_runs if run.states_found is not None}
    tlc_generated_states = {
        run.states_generated
        for run in tlc_runs
        if isinstance(run.states_generated, int)
        and not isinstance(run.states_generated, bool)
    }
    tlc_median = median_or_none(tlc_times)
    tlc_state_value = next(iter(tlc_states)) if len(tlc_states) == 1 else None
    expected_states = spec.expected_states
    tlc_expected_states_match = _all_tlc_runs_match_expected(tlc_runs, expected_states)
    interp_expected_states_match = _all_mode_runs_match_expected(
        interp_runs,
        expected_states,
    )
    llvm2_expected_states_match = _all_mode_runs_match_expected(
        llvm2_runs,
        expected_states,
    )

    def speedup(summary: dict[str, Any]) -> float | None:
        mode_median = summary["median_seconds"]
        if tlc_median is None or mode_median in (None, 0):
            return None
        return tlc_median / mode_median

    def execution_speedup(summary: dict[str, Any]) -> float | None:
        execution_median = summary.get("execution_median_seconds")
        if tlc_median is None or execution_median in (None, 0):
            return None
        return tlc_median / execution_median

    parity_interp = (
        tlc_state_value is not None
        and interp_summary["consistent_states"]
        and interp_summary["state_values"] == [tlc_state_value]
        and tlc_expected_states_match is not False
        and interp_expected_states_match is not False
    )
    parity_llvm2 = (
        tlc_state_value is not None
        and llvm2_summary["consistent_states"]
        and llvm2_summary["state_values"] == [tlc_state_value]
        and tlc_expected_states_match is not False
        and llvm2_expected_states_match is not False
    )

    speedup_interp_vs_tlc = speedup(interp_summary)
    speedup_llvm2_vs_tlc = speedup(llvm2_summary)
    speedup_llvm2_execution_vs_tlc = execution_speedup(llvm2_summary)
    row = {
        "spec": spec.name,
        "tlc": {
            "runs": [run.to_dict() for run in tlc_runs],
            "median_seconds": tlc_median,
            "state_values": sorted(tlc_states),
            "consistent_states": len(tlc_states) <= 1,
            "generated_state_values": sorted(tlc_generated_states),
            "consistent_generated_states": len(tlc_generated_states) <= 1,
            "expected_states": expected_states,
            "expected_states_match": tlc_expected_states_match,
            "all_ok": all(_run_ok(run) for run in tlc_runs),
        },
        "interp": interp_summary,
        "llvm2": llvm2_summary,
        "parity_interp_vs_tlc": parity_interp,
        "parity_llvm2_vs_tlc": parity_llvm2,
        "speedup_interp_vs_tlc": speedup_interp_vs_tlc,
        "speedup_llvm2_vs_tlc": speedup_llvm2_vs_tlc,
        "speedup_llvm2_execution_vs_tlc": speedup_llvm2_execution_vs_tlc,
    }
    row["interp"]["expected_states"] = expected_states
    row["interp"]["expected_states_match"] = interp_expected_states_match
    row["llvm2"]["expected_states"] = expected_states
    row["llvm2"]["expected_states_match"] = llvm2_expected_states_match
    row["llvm2_evidence"] = classify_llvm2_evidence(row)
    return row


def _ratio_or_none(numerator: Any, denominator: Any) -> float | None:
    if not _positive_float(numerator) or not _positive_float(denominator):
        return None
    return float(numerator) / float(denominator)


def classify_llvm2_evidence(row: dict[str, Any]) -> dict[str, Any]:
    """Derive concise per-spec evidence labels for human gate reports."""
    telemetry = row.get("llvm2", {}).get("telemetry") or {}
    actions_all = _fraction_is_complete(
        telemetry.get("llvm2_actions_compiled"),
        telemetry.get("llvm2_actions_total"),
        require_positive=True,
    )
    invariants_all = _fraction_is_complete(
        telemetry.get("llvm2_invariants_compiled"),
        telemetry.get("llvm2_invariants_total"),
        require_positive=False,
    )
    action_only = None
    native_fused_mode = telemetry.get("llvm2_native_fused_mode")
    if native_fused_mode == "action_only":
        action_only = True
    elif native_fused_mode == "invariant_checking":
        action_only = False
    elif actions_all is not None and invariants_all is not None:
        action_only = actions_all and not invariants_all

    flat_primary = telemetry.get("flat_state_primary")
    flat_frontier = telemetry.get("flat_bfs_frontier_active")
    flat_frontier_fallbacks = _telemetry_int(telemetry, "flat_bfs_frontier_fallbacks")
    flat_layout = None
    if (
        flat_primary is False
        or flat_frontier is False
        or (
            flat_frontier_fallbacks is not None and flat_frontier_fallbacks != 0
        )
    ):
        flat_layout = False
    elif flat_primary is True and flat_frontier is True and flat_frontier_fallbacks == 0:
        flat_layout = True

    speedup = row.get("speedup_llvm2_vs_tlc")
    native_fused_regular_invariants_checked = telemetry.get(
        "llvm2_native_fused_regular_invariants_checked"
    )
    if not isinstance(native_fused_regular_invariants_checked, bool):
        native_fused_regular_invariants_checked = None
    return {
        "native_fused": _native_fused_execution_evidence_active(telemetry),
        "native_fused_regular_invariants_checked": native_fused_regular_invariants_checked,
        "action_only": action_only,
        "flat_layout": flat_layout,
        "tlc_wins": speedup is not None and speedup < 1.0,
        "winner": _winner_label(speedup),
    }


def _fraction_is_complete(
    numerator: Any,
    denominator: Any,
    *,
    require_positive: bool,
) -> bool | None:
    if (
        not isinstance(numerator, int)
        or isinstance(numerator, bool)
        or not isinstance(denominator, int)
        or isinstance(denominator, bool)
    ):
        return None
    if denominator < 0:
        return None
    if require_positive and denominator <= 0:
        return False
    return numerator == denominator


def _winner_label(speedup_llvm2_vs_tlc: Any) -> str:
    if not isinstance(speedup_llvm2_vs_tlc, (int, float)) or isinstance(
        speedup_llvm2_vs_tlc, bool
    ):
        return "n/a"
    if speedup_llvm2_vs_tlc > 1.0:
        return "LLVM2"
    if speedup_llvm2_vs_tlc < 1.0:
        return "TLC"
    return "tie"


def _expected_native_fused_state_constraint_count(
    spec_name: str,
    telemetry: dict[str, Any] | None,
) -> int | None:
    expected = NATIVE_FUSED_STATE_CONSTRAINT_COUNTS.get(spec_name)
    if expected is not None:
        return expected
    total = _telemetry_int(telemetry, "llvm2_state_constraints_total")
    if total is not None and total > 0:
        return total
    return None


def _native_fused_execution_evidence_active(telemetry: dict[str, Any] | None) -> bool:
    if not telemetry:
        return False
    initial_states = _telemetry_int(
        telemetry,
        "compiled_bfs_level_loop_initial_states",
    )
    return (
        telemetry.get("llvm2_native_fused_level_active") is True
        and telemetry.get("llvm2_native_fused_level_built") is True
        and telemetry.get("compiled_bfs_level_active") is True
        and telemetry.get("compiled_bfs_level_loop_started") is True
        and telemetry.get("compiled_bfs_level_loop_fused") is True
        and initial_states is not None
        and initial_states > 0
        and telemetry.get("llvm2_bfs_level_loop_kind") == "native_fused_llvm2_parent_loop"
        and _compiled_bfs_positive_completion_detail(telemetry) is None
    )


def _state_constrained_native_fused_active(
    spec_name: str,
    telemetry: dict[str, Any] | None,
) -> bool:
    if not telemetry:
        return False
    if spec_name not in NATIVE_FUSED_STATE_CONSTRAINT_COUNTS:
        return False
    expected = _expected_native_fused_state_constraint_count(spec_name, telemetry)
    if expected is None or expected <= 0:
        return False
    actual = _telemetry_int(telemetry, "llvm2_native_fused_state_constraint_count")
    compiled = _telemetry_int(telemetry, "llvm2_state_constraints_compiled")
    total = _telemetry_int(telemetry, "llvm2_state_constraints_total")
    return (
        _native_fused_execution_evidence_active(telemetry)
        and telemetry.get("llvm2_native_fused_mode") == "state_constraint_checking"
        and actual == expected
        and compiled == expected
        and total == expected
        and telemetry.get("llvm2_native_fused_regular_invariants_checked") is True
        and telemetry.get("flat_state_primary") is True
        and telemetry.get("flat_bfs_frontier_active") is True
        and _telemetry_int(telemetry, "flat_bfs_frontier_fallbacks") == 0
    )


def evaluate_llvm2_truth_gates(row: dict[str, Any], args: argparse.Namespace) -> list[str]:
    """Return human-readable gate failures for one spec row."""
    failures: list[str] = []
    spec = row["spec"]
    require_native_fused = getattr(args, "require_llvm2_native_fused_level", False)
    require_compiled_bfs = (
        getattr(args, "require_llvm2_compiled_bfs", False) or require_native_fused
    )
    require_fused_level = (
        getattr(args, "require_llvm2_fused_level", False) or require_native_fused
    )
    require_flat_state_primary = (
        getattr(args, "require_flat_state_primary", False) or require_native_fused
    )
    require_flat_bfs_frontier = (
        getattr(args, "require_flat_bfs_frontier", False) or require_native_fused
    )
    require_no_llvm2_fallbacks = (
        getattr(args, "require_no_llvm2_fallbacks", False) or require_native_fused
    )

    if getattr(args, "require_llvm2_compiled_actions", False):
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            compiled = _telemetry_int(telemetry, "llvm2_actions_compiled")
            total = _telemetry_int(telemetry, "llvm2_actions_total")
            if compiled is None or compiled <= 0:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    f"compiled actions gate failed ({compiled!r}/{total!r})"
                )

    if getattr(args, "require_llvm2_all_actions", False):
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            compiled = _telemetry_int(telemetry, "llvm2_actions_compiled")
            total = _telemetry_int(telemetry, "llvm2_actions_total")
            if compiled is None or total is None or total <= 0 or compiled != total:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    f"all-actions gate failed ({compiled!r}/{total!r})"
                )

    if getattr(args, "require_llvm2_compiled_invariants", False):
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            compiled = _telemetry_int(telemetry, "llvm2_invariants_compiled")
            total = _telemetry_int(telemetry, "llvm2_invariants_total")
            if (
                compiled is None
                or total is None
                or total <= 0
                or compiled <= 0
                or compiled != total
            ):
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    f"compiled invariants gate failed ({compiled!r}/{total!r})"
                )
            if (
                telemetry
                and telemetry.get("llvm2_native_fused_level_active") is True
                and telemetry.get("llvm2_native_fused_regular_invariants_checked") is not True
            ):
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "native fused regular invariants were not checked by the backend "
                    f"(llvm2_native_fused_regular_invariants_checked="
                    f"{telemetry.get('llvm2_native_fused_regular_invariants_checked')!r})"
                )
            elif telemetry and telemetry.get("llvm2_native_fused_level_active") is True:
                native_fused_mode = telemetry.get("llvm2_native_fused_mode")
                native_invariant_count = _telemetry_int(
                    telemetry,
                    "llvm2_native_fused_invariant_count",
                )
                if native_fused_mode not in {
                    "invariant_checking",
                    "state_constraint_checking",
                } or native_invariant_count != total:
                    failures.append(
                        f"{spec} llvm2 run {run['run_index']}: "
                        "native fused invariant coverage did not include all regular invariants "
                        f"(llvm2_native_fused_mode={native_fused_mode!r}, "
                        f"llvm2_native_fused_invariant_count={native_invariant_count!r}, "
                        f"llvm2_invariants_total={total!r})"
                    )

    if require_compiled_bfs:
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            if not telemetry or not (
                telemetry.get("compiled_bfs_step_active") is True
                or _state_constrained_native_fused_active(spec, telemetry)
            ):
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: compiled BFS step was not active"
                )
            runtime_issue_reasons = _compiled_bfs_runtime_issue_reasons(telemetry)
            if runtime_issue_reasons:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "compiled BFS runtime fallback/error reasons observed "
                    f"({len(runtime_issue_reasons)})"
                )
            if transition_failure := _run_transition_failure(run):
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: {transition_failure}"
                )

    if getattr(args, "require_llvm2_successor_telemetry", False):
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            successor_detail = _compiled_bfs_successor_evidence_detail(run, telemetry)
            if successor_detail is not None:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "compiled BFS successor telemetry did not prove admitted states "
                    f"{successor_detail}"
                )

    if require_fused_level:
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            if (
                not telemetry
                or telemetry.get("compiled_bfs_level_active") is not True
                or telemetry.get("compiled_bfs_level_loop_started") is not True
                or telemetry.get("compiled_bfs_level_loop_fused") is not True
                or _telemetry_int(telemetry, "compiled_bfs_level_loop_initial_states") is None
                or _telemetry_int(telemetry, "compiled_bfs_level_loop_initial_states") <= 0
            ):
                loop_fused = (
                    telemetry.get("compiled_bfs_level_loop_fused") if telemetry else None
                )
                initial_states = (
                    telemetry.get("compiled_bfs_level_loop_initial_states")
                    if telemetry
                    else None
                )
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "fused BFS level did not start executing "
                    f"(compiled_bfs_level_active="
                    f"{telemetry.get('compiled_bfs_level_active') if telemetry else None!r}, "
                    f"compiled_bfs_level_loop_started="
                    f"{telemetry.get('compiled_bfs_level_loop_started') if telemetry else None!r}, "
                    f"compiled_bfs_level_loop_fused={loop_fused!r}, "
                    f"compiled_bfs_level_loop_initial_states={initial_states!r})"
                )
            positive_completion_detail = _compiled_bfs_positive_completion_detail(telemetry)
            if positive_completion_detail is not None:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "fused BFS level did not report positive completion work "
                    f"{positive_completion_detail}"
                )
            runtime_issue_reasons = _compiled_bfs_runtime_issue_reasons(telemetry)
            if runtime_issue_reasons and not require_compiled_bfs:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "compiled BFS runtime fallback/error reasons observed "
                    f"({len(runtime_issue_reasons)})"
                )
            if not require_compiled_bfs and (
                transition_failure := _run_transition_failure(run)
            ):
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: {transition_failure}"
                )

    if require_native_fused:
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            loop_kind = telemetry.get("llvm2_bfs_level_loop_kind") if telemetry else None
            compiled_step_or_constrained_native = (
                telemetry
                and (
                    telemetry.get("compiled_bfs_step_active") is True
                    or _state_constrained_native_fused_active(spec, telemetry)
                )
            )
            if not telemetry or not (
                telemetry.get("llvm2_native_fused_level_active") is True
                and telemetry.get("llvm2_native_fused_level_built") is True
                and compiled_step_or_constrained_native
                and telemetry.get("compiled_bfs_level_active") is True
                and telemetry.get("compiled_bfs_level_loop_started") is True
                and telemetry.get("compiled_bfs_level_loop_fused") is True
                and _telemetry_int(telemetry, "compiled_bfs_level_loop_initial_states") is not None
                and _telemetry_int(telemetry, "compiled_bfs_level_loop_initial_states") > 0
                and loop_kind == "native_fused_llvm2_parent_loop"
            ):
                compiled_step = telemetry.get("compiled_bfs_step_active") if telemetry else None
                compiled_level = telemetry.get("compiled_bfs_level_active") if telemetry else None
                loop_started = (
                    telemetry.get("compiled_bfs_level_loop_started") if telemetry else None
                )
                loop_fused = (
                    telemetry.get("compiled_bfs_level_loop_fused") if telemetry else None
                )
                initial_states = (
                    telemetry.get("compiled_bfs_level_loop_initial_states")
                    if telemetry
                    else None
                )
                level_built = (
                    telemetry.get("llvm2_native_fused_level_built") if telemetry else None
                )
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    f"native LLVM2 fused BFS level was not active "
                    f"(loop_kind={loop_kind!r}, "
                    f"llvm2_native_fused_level_built={level_built!r}, "
                    f"compiled_bfs_step_active={compiled_step!r}, "
                    f"compiled_bfs_level_active={compiled_level!r}, "
                    f"compiled_bfs_level_loop_started={loop_started!r}, "
                    f"compiled_bfs_level_loop_fused={loop_fused!r}, "
                    f"compiled_bfs_level_loop_initial_states={initial_states!r})"
                )
            zero_work_detail = _compiled_bfs_zero_work_detail(telemetry)
            if zero_work_detail is not None:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "compiled BFS loop completed without processing work "
                    f"{zero_work_detail}"
                )
            positive_completion_detail = _compiled_bfs_positive_completion_detail(telemetry)
            if positive_completion_detail is not None:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "compiled BFS loop did not report positive native-fused work "
                    f"{positive_completion_detail}"
                )
            expected_state_constraint_count = (
                _expected_native_fused_state_constraint_count(spec, telemetry)
            )
            expected_state_len = NATIVE_FUSED_STATE_LENGTHS.get(spec)
            if expected_state_len is not None:
                actual_state_len = _telemetry_int(
                    telemetry,
                    "llvm2_native_fused_state_len",
                )
                if actual_state_len != expected_state_len:
                    failures.append(
                        f"{spec} llvm2 run {run['run_index']}: "
                        "native fused state length did not match the real spec "
                        f"layout (llvm2_native_fused_state_len="
                        f"{actual_state_len!r}, expected={expected_state_len!r})"
                    )
            if expected_state_constraint_count is not None:
                actual_state_constraint_count = _telemetry_int(
                    telemetry,
                    "llvm2_native_fused_state_constraint_count",
                )
                compiled_state_constraint_count = _telemetry_int(
                    telemetry,
                    "llvm2_state_constraints_compiled",
                )
                total_state_constraint_count = _telemetry_int(
                    telemetry,
                    "llvm2_state_constraints_total",
                )
                native_fused_mode = (
                    telemetry.get("llvm2_native_fused_mode") if telemetry else None
                )
                if (
                    actual_state_constraint_count != expected_state_constraint_count
                    or native_fused_mode != "state_constraint_checking"
                    or compiled_state_constraint_count != expected_state_constraint_count
                    or total_state_constraint_count != expected_state_constraint_count
                ):
                    failures.append(
                        f"{spec} llvm2 run {run['run_index']}: "
                        "native fused state constraints were not checked by the backend "
                        f"(llvm2_native_fused_state_constraint_count="
                        f"{actual_state_constraint_count!r}, "
                        f"llvm2_state_constraints_compiled="
                        f"{compiled_state_constraint_count!r}, "
                        f"llvm2_state_constraints_total="
                        f"{total_state_constraint_count!r}, "
                        f"expected={expected_state_constraint_count!r}, "
                        f"llvm2_native_fused_mode={native_fused_mode!r})"
                    )

    if require_flat_state_primary:
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            if not telemetry or telemetry.get("flat_state_primary") is not True:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: flat_state_primary was not true"
                )

    if require_flat_bfs_frontier:
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry")
            frontier_fallbacks = (
                _telemetry_int(telemetry, "flat_bfs_frontier_fallbacks")
                if telemetry
                else None
            )
            if (
                not telemetry
                or telemetry.get("flat_bfs_frontier_active") is not True
                or frontier_fallbacks != 0
            ):
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "flat BFS frontier did not report explicit active=true with 0 fallback "
                    f"(active={telemetry.get('flat_bfs_frontier_active') if telemetry else None!r}, "
                    f"fallbacks={frontier_fallbacks!r})"
                )

    if require_no_llvm2_fallbacks:
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry") or {}
            reasons = telemetry.get("fallback_reasons") or []
            disallowed_reasons = _disallowed_llvm2_fallback_reasons(
                reasons,
                spec,
                args,
                telemetry,
            )
            if disallowed_reasons:
                if len(disallowed_reasons) == len(reasons):
                    detail = f"LLVM2 fallback reasons observed ({len(reasons)})"
                else:
                    detail = (
                        "non-invariant LLVM2 fallback reasons observed "
                        f"({len(disallowed_reasons)} disallowed of {len(reasons)} total)"
                    )
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    f"{detail}"
                )

    if getattr(args, "require_llvm2_faster_than_tlc", False):
        speedup = row["speedup_llvm2_vs_tlc"]
        if speedup is None or speedup <= 1.0:
            failures.append(
                f"{spec}: llvm2 median was not faster than TLC "
                f"(speedup_llvm2_vs_tlc={speedup!r})"
            )

    if getattr(args, "require_llvm2_execution_faster_than_tlc", False):
        for run in row["llvm2"]["runs"]:
            telemetry = run.get("llvm2_telemetry") or {}
            mismatch = _compiled_bfs_execution_seconds_mismatch(telemetry)
            if mismatch is not None:
                reported_seconds, derived_seconds = mismatch
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: compiled BFS execution "
                    "seconds/nanos mismatch "
                    f"(compiled_bfs_execution_seconds={reported_seconds!r}, "
                    f"compiled_bfs_execution_nanos="
                    f"{telemetry.get('compiled_bfs_execution_nanos')!r}, "
                    f"derived_seconds={derived_seconds!r})"
                )
            execution_seconds = _compiled_bfs_execution_seconds(telemetry)
            if execution_seconds is None:
                failures.append(
                    f"{spec} llvm2 run {run['run_index']}: "
                    "compiled BFS execution timing telemetry was missing or non-positive "
                    f"(compiled_bfs_execution_seconds="
                    f"{telemetry.get('compiled_bfs_execution_seconds')!r}, "
                    f"compiled_bfs_execution_nanos="
                    f"{telemetry.get('compiled_bfs_execution_nanos')!r})"
                )
        speedup = row.get("speedup_llvm2_execution_vs_tlc")
        if speedup is None or speedup <= 1.0:
            failures.append(
                f"{spec}: llvm2 execution median was not faster than TLC "
                f"(speedup_llvm2_execution_vs_tlc={speedup!r})"
            )

    return failures


def _telemetry_int(telemetry: dict[str, Any] | None, field: str) -> int | None:
    if telemetry is None:
        return None
    value = telemetry.get(field)
    return value if isinstance(value, int) and not isinstance(value, bool) else None


def _positive_float(value: Any) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
        and value > 0.0
    )


def render_markdown(report: dict[str, Any]) -> str:
    """Render a concise markdown report."""
    lines = [
        "# Single-Thread TLA2 Backends vs TLC Benchmark",
        "",
        f"**Timestamp:** {report['timestamp']}",
        f"**Commit:** {report['git_commit']}",
        f"**Artifact bundle:** `{report['artifact_bundle']}`",
        "",
        "## Backend Controls",
        "",
        "| Control | Value |",
        "|---------|-------|",
    ]
    for key, value in sorted(
        (report.get("backend_controls") or {}).get("llvm2_env", {}).items()
    ):
        lines.append(f"| `{key}` | `{value}` |")
    lines.extend(
        [
            "",
        ]
    )
    lines.extend(
        [
            "## Command",
            "",
            f"`{report['invocation']}`",
            "",
            "## Results",
            "",
            "| Spec | TLC median (s) | Interp median (s) | LLVM2 wall median (s) | LLVM2 exec median (s) | Interp/TLC | LLVM2 wall/TLC | LLVM2 exec/TLC | Winner | Parity | Native fused | Native invariant checks | Action-only | Flat layout | LLVM2 actions | LLVM2 invariants | BFS step | Fused level | Loop fused | Loop initial states | LLVM2 level | Native LLVM2 level | Flat primary | Flat BFS | Fallbacks | Gates |",
            "|------|----------------|-------------------|-----------------------|-----------------------|------------|----------------|----------------|--------|--------|--------------|-------------------------|-------------|-------------|---------------|------------------|----------|-------------|------------|---------------------|-------------|--------------------|--------------|----------|-----------|-------|",
        ]
    )
    for row in report["rows"]:
        tlc_median = _fmt_seconds(row["tlc"]["median_seconds"])
        interp_median = _fmt_seconds(row["interp"]["median_seconds"])
        llvm2_median = _fmt_seconds(row["llvm2"]["median_seconds"])
        llvm2_execution_median = _fmt_seconds(
            row["llvm2"].get("execution_median_seconds")
        )
        interp_ratio = _fmt_ratio(row["speedup_interp_vs_tlc"])
        llvm2_ratio = _fmt_ratio(row["speedup_llvm2_vs_tlc"])
        llvm2_execution_ratio = _fmt_ratio(
            row.get("speedup_llvm2_execution_vs_tlc")
        )
        parity = "PASS" if row["parity_interp_vs_tlc"] and row["parity_llvm2_vs_tlc"] else "FAIL"
        telemetry = row["llvm2"].get("telemetry", {})
        evidence = row.get("llvm2_evidence") or classify_llvm2_evidence(row)
        gate_failures = row.get("llvm2_gate_failures", [])
        lines.append(
            f"| {row['spec']} | {tlc_median} | {interp_median} | {llvm2_median} | "
            f"{llvm2_execution_median} | {interp_ratio} | {llvm2_ratio} | "
            f"{llvm2_execution_ratio} | {evidence.get('winner', 'n/a')} | "
            f"{parity} | "
            f"{_fmt_bool(evidence.get('native_fused'))} | "
            f"{_fmt_bool(evidence.get('native_fused_regular_invariants_checked'))} | "
            f"{_fmt_bool(evidence.get('action_only'))} | "
            f"{_fmt_bool(evidence.get('flat_layout'))} | "
            f"{_fmt_fraction(telemetry.get('llvm2_actions_compiled'), telemetry.get('llvm2_actions_total'))} | "
            f"{_fmt_fraction(telemetry.get('llvm2_invariants_compiled'), telemetry.get('llvm2_invariants_total'))} | "
            f"{_fmt_bool(telemetry.get('compiled_bfs_step_active'))} | "
            f"{_fmt_bool(telemetry.get('compiled_bfs_level_active'))} | "
            f"{_fmt_bool(telemetry.get('compiled_bfs_level_loop_fused'))} | "
            f"{_fmt_int(telemetry.get('compiled_bfs_level_loop_initial_states'))} | "
            f"{_fmt_loop_kind(telemetry.get('llvm2_bfs_level_loop_kind'))} | "
            f"{_fmt_bool(telemetry.get('llvm2_native_fused_level_active'))} | "
            f"{_fmt_bool(telemetry.get('flat_state_primary'))} | "
            f"{_fmt_bool(telemetry.get('flat_bfs_frontier_active'))} | "
            f"{len(telemetry.get('fallback_reasons') or [])} | "
            f"{'PASS' if not gate_failures else 'FAIL'} |"
        )
    return "\n".join(lines)


def _fmt_seconds(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{value:.3f}"


def _fmt_ratio(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{value:.2f}x"


def _fmt_fraction(numerator: Any, denominator: Any) -> str:
    if numerator is None or denominator is None:
        return "n/a"
    return f"{numerator}/{denominator}"


def _fmt_bool(value: Any) -> str:
    if value is None:
        return "n/a"
    return "yes" if value else "no"


def _fmt_int(value: Any) -> str:
    if not isinstance(value, int) or isinstance(value, bool):
        return "n/a"
    return str(value)


def _fmt_loop_kind(value: Any) -> str:
    if value is None:
        return "n/a"
    return str(value).replace("_", " ")


def build_cli() -> argparse.ArgumentParser:
    """Build the CLI parser."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--specs", nargs="+", default=list(DEFAULT_SPECS))
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--output-dir", default=None)
    parser.add_argument("--tla2-bin", default=None)
    parser.add_argument("--cargo-profile", default="release")
    parser.add_argument("--target-dir", default=None)
    parser.add_argument(
        "--tla2-flag",
        action="append",
        default=[],
        help="extra flag passed to both TLA2 modes",
    )
    parser.add_argument(
        "--interp-env",
        action="append",
        default=[],
        help="KEY=VALUE override for interpreter mode",
    )
    parser.add_argument(
        "--llvm2-env",
        action="append",
        default=[],
        help="KEY=VALUE override for LLVM2 mode",
    )
    parser.add_argument(
        "--require-llvm2-compiled-actions",
        action="store_true",
        help="fail if any LLVM2 run compiles zero actions or lacks action telemetry",
    )
    parser.add_argument(
        "--require-llvm2-all-actions",
        action="store_true",
        help="fail if any LLVM2 run does not compile every reported action",
    )
    parser.add_argument(
        "--require-llvm2-compiled-invariants",
        action="store_true",
        help="fail if any LLVM2 run does not compile every reported invariant",
    )
    parser.add_argument(
        "--require-llvm2-compiled-bfs",
        action="store_true",
        help="fail if any LLVM2 run does not activate the compiled BFS step loop",
    )
    parser.add_argument(
        "--require-llvm2-fused-level",
        action="store_true",
        help="fail if any LLVM2 run does not activate the fused compiled BFS level loop",
    )
    parser.add_argument(
        "--require-llvm2-native-fused-level",
        action="store_true",
        help=(
            "fail if any LLVM2 run does not report the native LLVM2-generated "
            "fused BFS parent loop"
        ),
    )
    parser.add_argument(
        "--require-llvm2-successor-telemetry",
        action="store_true",
        help=(
            "fail if compiled BFS successor telemetry does not report positive "
            "new states and a total state count matching states_found"
        ),
    )
    parser.add_argument(
        "--require-flat-state-primary",
        action="store_true",
        help="fail if any LLVM2 run does not report flat_state_primary=true",
    )
    parser.add_argument(
        "--require-flat-bfs-frontier",
        action="store_true",
        help="fail if any LLVM2 run does not report flat-frontier activity",
    )
    parser.add_argument(
        "--require-no-llvm2-fallbacks",
        action="store_true",
        help="fail if LLVM2 fallback or unsupported-lowering reasons are observed",
    )
    parser.add_argument(
        "--allow-llvm2-invariant-rust-fallbacks",
        action="store_true",
        help=(
            "with --require-no-llvm2-fallbacks, allow invariant compilation "
            "fallback diagnostics only when the run proves the native fused "
            "LLVM2 level and flat frontier are active; invariants are then "
            "checked by the Rust path after flat/global dedup"
        ),
    )
    parser.add_argument(
        "--require-llvm2-faster-than-tlc",
        action="store_true",
        help="fail if LLVM2 median runtime is not faster than TLC for every spec",
    )
    parser.add_argument(
        "--require-llvm2-execution-faster-than-tlc",
        action="store_true",
        help=(
            "fail if LLVM2 compiled-BFS execution median, excluding cold JIT "
            "build/setup time, is not faster than TLC wall time for every spec"
        ),
    )
    return parser


def validate_cli(args: argparse.Namespace, parser: argparse.ArgumentParser) -> None:
    """Reject unsafe gate flag combinations."""
    if (
        getattr(args, "allow_llvm2_invariant_rust_fallbacks", False)
        and getattr(args, "require_llvm2_compiled_invariants", False)
    ):
        parser.error(
            "--allow-llvm2-invariant-rust-fallbacks conflicts with "
            "--require-llvm2-compiled-invariants"
        )

    if getattr(args, "require_llvm2_native_fused_level", False):
        for override in getattr(args, "llvm2_env", []):
            key, sep, value = override.partition("=")
            required_value = REQUIRED_NATIVE_FUSED_ENV.get(key)
            if sep and required_value is not None and value != required_value:
                parser.error(
                    "--require-llvm2-native-fused-level requires "
                    f"{key}={required_value}; --llvm2-env supplied {override}"
                )

    if not getattr(args, "allow_llvm2_invariant_rust_fallbacks", False):
        return

    required = [
        "require_no_llvm2_fallbacks",
        "require_llvm2_fused_level",
        "require_llvm2_native_fused_level",
        "require_flat_state_primary",
        "require_flat_bfs_frontier",
    ]
    missing = [flag for flag in required if not getattr(args, flag, False)]
    if missing:
        parser.error(
            "--allow-llvm2-invariant-rust-fallbacks requires "
            + " ".join(f"--{flag.replace('_', '-')}" for flag in missing)
        )


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    parser = build_cli()
    args = parser.parse_args()
    validate_cli(args, parser)

    if args.runs <= 0:
        raise ValueError("--runs must be positive")

    interp_env = parse_env_overrides(args.interp_env)
    llvm2_env = parse_env_overrides(args.llvm2_env)
    if args.require_llvm2_native_fused_level:
        llvm2_env = {
            **REQUIRED_NATIVE_FUSED_ENV,
            **llvm2_env,
        }

    tla2_binary = resolve_tla2_binary(args)
    if tla2_binary is None:
        return 1

    timestamp = perf_harness.current_timestamp()
    output_dir = (
        Path(args.output_dir)
        if args.output_dir
        else perf_harness.REPORTS_ROOT / timestamp / "single-thread-backends-vs-tlc"
    )
    perf_harness.ensure_output_dir(output_dir)

    rows: list[dict[str, Any]] = []
    exit_code = 0
    for spec_name in args.specs:
        spec = resolve_benchmark_spec(spec_name, output_dir)
        timeout = max(args.timeout, spec.timeout_seconds)
        log.info("Benchmarking %s", spec.name)

        tlc_runs: list[scaling.ScalingRunResult] = []
        interp_runs: list[ModeRunResult] = []
        llvm2_runs: list[ModeRunResult] = []
        for run_index in range(1, args.runs + 1):
            log.info("  run %d/%d: TLC", run_index, args.runs)
            tlc_run = scaling.run_tlc_check(
                spec,
                workers=1,
                timeout=timeout,
                output_dir=output_dir / spec.name / f"tlc-run{run_index}",
            )
            tlc_runs.append(tlc_run)
            log.info("    TLC %.3fs, states=%s", tlc_run.elapsed_seconds, tlc_run.states_found)

            log.info("  run %d/%d: TLA2 interp", run_index, args.runs)
            interp_run = run_tla2_mode(
                spec,
                mode="interp",
                run_index=run_index,
                tla2_bin=tla2_binary,
                timeout=timeout,
                output_dir=output_dir / spec.name / f"interp-run{run_index}",
                common_flags=list(args.tla2_flag),
                env_overrides=interp_env,
            )
            interp_runs.append(interp_run)
            log.info(
                "    interp %.3fs, states=%s",
                interp_run.elapsed_seconds,
                interp_run.states_found,
            )

            log.info("  run %d/%d: TLA2 llvm2", run_index, args.runs)
            llvm2_run = run_tla2_mode(
                spec,
                mode="llvm2",
                run_index=run_index,
                tla2_bin=tla2_binary,
                timeout=timeout,
                output_dir=output_dir / spec.name / f"llvm2-run{run_index}",
                common_flags=list(args.tla2_flag),
                env_overrides=llvm2_env,
            )
            llvm2_runs.append(llvm2_run)
            log.info(
                "    llvm2 %.3fs, states=%s",
                llvm2_run.elapsed_seconds,
                llvm2_run.states_found,
            )

        row = summarize_spec(
            spec,
            interp_runs,
            llvm2_runs,
            tlc_runs,
        )
        gate_failures = evaluate_llvm2_truth_gates(row, args)
        row["llvm2_gate_failures"] = gate_failures
        rows.append(row)
        if row["parity_interp_vs_tlc"] is not True or row["parity_llvm2_vs_tlc"] is not True:
            exit_code = 1
        if (
            row["tlc"]["all_ok"] is not True
            or row["interp"]["all_ok"] is not True
            or row["llvm2"]["all_ok"] is not True
        ):
            exit_code = 1
        if gate_failures:
            exit_code = 1
            for failure in gate_failures:
                log.error("LLVM2 truth gate failed: %s", failure)

    invocation = shlex.join([Path(__file__).name, *sys.argv[1:]])
    report = {
        "timestamp": timestamp,
        "git_commit": perf_harness.git_commit_short(),
        "artifact_bundle": perf_harness.repo_relative(output_dir),
        "invocation": invocation,
        "backend_controls": {
            "llvm2_env": dict(sorted(llvm2_env.items())),
        },
        "gate_flags": {
            "require_llvm2_compiled_actions": args.require_llvm2_compiled_actions,
            "require_llvm2_all_actions": args.require_llvm2_all_actions,
            "require_llvm2_compiled_invariants": args.require_llvm2_compiled_invariants,
            "require_llvm2_compiled_bfs": args.require_llvm2_compiled_bfs,
            "require_llvm2_fused_level": args.require_llvm2_fused_level,
            "require_llvm2_native_fused_level": args.require_llvm2_native_fused_level,
            "require_llvm2_successor_telemetry": args.require_llvm2_successor_telemetry,
            "require_flat_state_primary": args.require_flat_state_primary,
            "require_flat_bfs_frontier": args.require_flat_bfs_frontier,
            "require_no_llvm2_fallbacks": args.require_no_llvm2_fallbacks,
            "allow_llvm2_invariant_rust_fallbacks": args.allow_llvm2_invariant_rust_fallbacks,
            "require_llvm2_faster_than_tlc": args.require_llvm2_faster_than_tlc,
            "require_llvm2_execution_faster_than_tlc": (
                args.require_llvm2_execution_faster_than_tlc
            ),
        },
        "rows": rows,
    }

    markdown = render_markdown(report)
    perf_harness.write_json(output_dir / "summary.json", report)
    (output_dir / "summary.md").write_text(markdown, encoding="utf-8")

    log.info("Summary JSON: %s", output_dir / "summary.json")
    log.info("Summary markdown: %s", output_dir / "summary.md")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
