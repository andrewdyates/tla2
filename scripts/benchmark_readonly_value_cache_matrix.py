#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Run the #3285 read-only value-cache control/treatment matrix."""

from __future__ import annotations

import argparse
import logging
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import perf_harness
import perf_harness_scaling as scaling

log = logging.getLogger(__name__)

DEFAULT_SPEC = "MCKVSSafetySmall"
DEFAULT_WORKERS = (1, 2, 4, 8)
STABLE_JSON = perf_harness.REPORTS_ROOT / "issue-3285-readonly-value-cache-current.json"
STABLE_MD = perf_harness.REPORTS_ROOT / "issue-3285-readonly-value-cache-current.md"
MODES = (
    ("control", None),
    ("treatment", {"TLA2_PARALLEL_READONLY_VALUE_CACHES": "1"}),
)


def parse_workers(value: str) -> list[int]:
    """Parse a comma-separated worker list."""
    workers: list[int] = []
    for item in value.split(","):
        candidate = item.strip()
        if not candidate:
            continue
        parsed = int(candidate)
        if parsed <= 0:
            raise ValueError("worker counts must be positive integers")
        workers.append(parsed)
    if not workers:
        raise ValueError("at least one worker count is required")
    return workers


def resolve_tla2_binary(args: argparse.Namespace) -> Path | None:
    """Build once or resolve an explicit binary."""
    if args.tla2_bin:
        binary = Path(args.tla2_bin)
        if not binary.exists():
            log.error("binary not found: %s", binary)
            return None
        return binary

    target_dir = perf_harness.resolve_target_dir(
        args.target_dir, namespace="readonly_value_cache_matrix"
    )
    build_cmd = perf_harness.build_cargo_build_command(args.cargo_profile, target_dir)
    log.info("Building tla2... (%s)", perf_harness.command_to_string(build_cmd.argv))
    build_result = perf_harness.run_command(build_cmd, timeout=600)
    if build_result.returncode != 0:
        log.error("Build failed:\n%s", build_result.stderr)
        return None

    binary = perf_harness.resolve_binary_path(target_dir, args.cargo_profile)
    if not binary.exists():
        log.error("built binary not found: %s", binary)
        return None
    log.info("Using binary: %s", binary)
    return binary


def build_mode_row(
    spec: perf_harness.SpecInfo,
    mode: str,
    run: scaling.ScalingRunResult,
    *,
    env_overrides: dict[str, str] | None,
) -> dict[str, Any]:
    """Normalize a single control/treatment run into a report row."""
    exact_state_parity = (
        spec.expected_states is not None
        and run.states_found is not None
        and run.states_found == spec.expected_states
        and run.returncode == 0
    )
    return {
        "spec": spec.name,
        "workers": run.workers,
        "mode": mode,
        "env_overrides": env_overrides,
        "elapsed_seconds": run.elapsed_seconds,
        "states_found": run.states_found,
        "expected_states": spec.expected_states,
        "exact_state_parity": exact_state_parity,
        "returncode": run.returncode,
        "error": run.error,
        "artifact_dir": run.artifact_dir,
    }


def summarize_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Pair control/treatment rows by worker and compute deltas."""
    paired: dict[int, dict[str, dict[str, Any]]] = {}
    for row in rows:
        paired.setdefault(row["workers"], {})[row["mode"]] = row

    pair_rows: list[dict[str, Any]] = []
    parity_fail = 0
    for workers in sorted(paired):
        control = paired[workers].get("control")
        treatment = paired[workers].get("treatment")
        control_time = control["elapsed_seconds"] if control else None
        treatment_time = treatment["elapsed_seconds"] if treatment else None
        delta = None
        ratio = None
        if control_time is not None and treatment_time is not None:
            delta = treatment_time - control_time
            if control_time > 0:
                ratio = treatment_time / control_time
        exact_state_parity = bool(
            control
            and treatment
            and control["exact_state_parity"]
            and treatment["exact_state_parity"]
            and control["states_found"] == treatment["states_found"]
        )
        if not exact_state_parity:
            parity_fail += 1
        pair_rows.append(
            {
                "workers": workers,
                "control": control,
                "treatment": treatment,
                "delta_seconds": delta,
                "treatment_over_control": ratio,
                "exact_state_parity": exact_state_parity,
            }
        )

    return {
        "pair_rows": pair_rows,
        "total_rows": len(rows),
        "worker_pairs": len(pair_rows),
        "parity_pass": len(pair_rows) - parity_fail,
        "parity_fail": parity_fail,
    }


def render_markdown(report: dict[str, Any]) -> str:
    """Render the readonly-cache matrix as markdown."""
    lines = [
        "# Read-Only Value Cache Matrix",
        "",
        "**Issue:** #3285",
        f"**Spec:** {report.get('spec', 'unknown')}",
        f"**Commit:** {report.get('git_commit', 'unknown')}",
        f"**Timestamp:** {report.get('timestamp', 'unknown')}",
        f"**Artifacts:** `{report.get('artifact_bundle', 'N/A')}`",
        "",
        "## Summary",
        "",
    ]

    summary = report.get("summary", {})
    expected_states = report.get("expected_states")
    if expected_states is not None:
        lines.append(f"- Expected TLC state count: {expected_states:,}")
    lines.append(f"- Worker pairs: {summary.get('worker_pairs', 0)}")
    lines.append(f"- Parity pass: {summary.get('parity_pass', 0)}")
    lines.append(f"- Parity fail: {summary.get('parity_fail', 0)}")
    lines.append("")
    lines.extend(_render_pair_table(summary.get("pair_rows", [])))
    lines.extend(_render_artifact_table(report.get("rows", [])))
    return "\n".join(lines)


def _render_pair_table(pair_rows: list[dict[str, Any]]) -> list[str]:
    lines = [
        "## Control vs Treatment",
        "",
        "| Workers | Control (s) | Treatment (s) | Delta (s) | Treatment/Control | States | Parity |",
        "|---------|-------------|---------------|-----------|-------------------|--------|--------|",
    ]
    for pair in pair_rows:
        control = pair.get("control") or {}
        treatment = pair.get("treatment") or {}
        states = control.get("states_found")
        state_text = f"{states:,}" if states is not None else "?"
        lines.append(
            f"| {pair.get('workers', '?')} "
            f"| {_fmt_seconds(control.get('elapsed_seconds'))} "
            f"| {_fmt_seconds(treatment.get('elapsed_seconds'))} "
            f"| {_fmt_delta(pair.get('delta_seconds'))} "
            f"| {_fmt_ratio(pair.get('treatment_over_control'))} "
            f"| {state_text} "
            f"| {'PASS' if pair.get('exact_state_parity') else 'FAIL'} |"
        )
    lines.append("")
    return lines


def _render_artifact_table(rows: list[dict[str, Any]]) -> list[str]:
    lines = [
        "## Run Artifacts",
        "",
        "| Mode | Workers | Artifact |",
        "|------|---------|----------|",
    ]
    for row in rows:
        lines.append(
            f"| {row.get('mode', '?')} | {row.get('workers', '?')} "
            f"| `{row.get('artifact_dir', 'N/A')}` |"
        )
    lines.append("")
    return lines


def _fmt_seconds(value: float | None) -> str:
    if value is None:
        return "N/A"
    return f"{value:.1f}"


def _fmt_delta(value: float | None) -> str:
    if value is None:
        return "N/A"
    return f"{value:+.1f}"


def _fmt_ratio(value: float | None) -> str:
    if value is None:
        return "N/A"
    return f"{value:.3f}x"


def run_matrix(
    spec: perf_harness.SpecInfo,
    *,
    worker_counts: list[int],
    timeout: int,
    output_dir: Path,
    tla2_binary: Path,
) -> tuple[list[dict[str, Any]], int]:
    """Run the same-build control/treatment matrix."""
    rows: list[dict[str, Any]] = []
    exit_code = 0

    for mode, env_overrides in MODES:
        log.info("Mode: %s", mode)
        for workers in worker_counts:
            log.info("  workers=%d", workers)
            run = scaling.run_tla2_check(
                spec,
                workers=workers,
                timeout=timeout,
                output_dir=output_dir / spec.name / f"{mode}-workers{workers}",
                tla2_bin=tla2_binary,
                extra_env=env_overrides,
            )
            row = build_mode_row(
                spec,
                mode,
                run,
                env_overrides=env_overrides,
            )
            rows.append(row)
            if not row["exact_state_parity"]:
                exit_code = 1
            log.info(
                "    %s: %.1fs/%s parity=%s (w=%d)",
                mode,
                row["elapsed_seconds"],
                "?" if row["states_found"] is None else f"{row['states_found']:,}",
                "PASS" if row["exact_state_parity"] else "FAIL",
                workers,
            )

    return rows, exit_code


def build_cli() -> argparse.ArgumentParser:
    """Build the CLI parser."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spec", default=DEFAULT_SPEC)
    parser.add_argument("--workers", default="1,2,4,8")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--output-dir", default=None)
    parser.add_argument("--current-json", default=str(STABLE_JSON))
    parser.add_argument("--current-markdown", default=str(STABLE_MD))
    parser.add_argument("--tla2-bin", default=None)
    parser.add_argument("--cargo-profile", default="release")
    parser.add_argument("--target-dir", default=None)
    return parser


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    args = build_cli().parse_args()

    worker_counts = parse_workers(args.workers)
    spec = perf_harness.require_spec(args.spec)
    timestamp = perf_harness.current_timestamp()
    output_dir = (
        Path(args.output_dir)
        if args.output_dir
        else perf_harness.REPORTS_ROOT / timestamp / "issue-3285-readonly-value-cache-matrix"
    )
    perf_harness.ensure_output_dir(output_dir)

    tla2_binary = resolve_tla2_binary(args)
    if tla2_binary is None:
        return 1

    rows, exit_code = run_matrix(
        spec,
        worker_counts=worker_counts,
        timeout=args.timeout,
        output_dir=output_dir,
        tla2_binary=tla2_binary,
    )

    report = {
        "issue": 3285,
        "timestamp": timestamp,
        "git_commit": perf_harness.git_commit_short(),
        "artifact_bundle": perf_harness.repo_relative(output_dir),
        "spec": spec.name,
        "expected_states": spec.expected_states,
        "rows": rows,
        "summary": summarize_rows(rows),
    }
    current_json = Path(args.current_json)
    current_md = Path(args.current_markdown)
    perf_harness.ensure_output_dir(current_json.parent)
    perf_harness.ensure_output_dir(current_md.parent)
    perf_harness.write_json(current_json, report)
    current_md.write_text(render_markdown(report), encoding="utf-8")

    log.info("Current JSON report: %s", current_json)
    log.info("Current markdown report: %s", current_md)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
