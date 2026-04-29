#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Scaling-matrix helpers for #3202 Category C parallel benchmarks.

Builds on the shared substrate in perf_harness.py. All run/report functions
live here so perf_harness.py stays under the 500-line file-size limit.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

import perf_harness

TLC_JAR = Path.home() / "tlaplus" / "tla2tools.jar"
TLC_FINAL_SUMMARY_REGEX = re.compile(
    r"^\s*([0-9][0-9,]*)\s+states generated,\s+"
    r"([0-9][0-9,]*)\s+distinct states found,\s+"
    r"([0-9][0-9,]*)\s+states left(?:\s+on queue\.)?\s*$",
    re.MULTILINE,
)
RUN_INDEX_REGEX = re.compile(r"(?:^|[-_])run([0-9]+)$")


@dataclass
class ScalingRunResult:
    """Normalized result from a single TLA2 or TLC benchmark run."""

    tool: str
    spec_name: str
    workers: int
    elapsed_seconds: float
    states_found: int | None
    distinct_states: int | None
    returncode: int
    error: str | None
    artifact_dir: str | None
    run_index: int | None = None
    transitions: int | None = None
    states_generated: int | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "tool": self.tool,
            "spec_name": self.spec_name,
            "run_index": self.run_index,
            "workers": self.workers,
            "elapsed_seconds": self.elapsed_seconds,
            "states_found": self.states_found,
            "distinct_states": self.distinct_states,
            "transitions": self.transitions,
            "states_generated": self.states_generated,
            "returncode": self.returncode,
            "error": self.error,
            "artifact_dir": self.artifact_dir,
        }


def run_tla2_check(
    spec: perf_harness.SpecInfo,
    *,
    workers: int,
    timeout: int | float,
    output_dir: Path,
    tla2_bin: str | Path | None = None,
    extra_env: Mapping[str, str] | None = None,
) -> ScalingRunResult:
    """Run tla2 check and return normalized results.

    tla2_bin must be an explicit pre-built binary path (build once, run many).
    """
    if tla2_bin is None:
        raise ValueError(
            "tla2_bin is required for scaling benchmarks (build once, run many)"
        )

    perf_harness.ensure_output_dir(output_dir)
    binary_path = Path(tla2_bin)

    cmd = perf_harness.build_tla2_check_command(
        spec,
        binary_path=binary_path,
        extra_env=extra_env,
        workers=workers,
        profile_enum=False,
        profile_eval=False,
    )
    result = perf_harness.run_command(cmd, timeout=timeout)

    (output_dir / "stdout.txt").write_text(result.stdout, encoding="utf-8")
    (output_dir / "stderr.txt").write_text(result.stderr, encoding="utf-8")
    perf_harness.write_json(output_dir / "command.json", result.to_dict())

    parsed = perf_harness.parse_profiling_output(result.stdout, result.stderr)

    return ScalingRunResult(
        tool="tla2",
        spec_name=spec.name,
        workers=workers,
        elapsed_seconds=result.elapsed_seconds,
        states_found=parsed["states_found"],
        distinct_states=parsed["states_found"],
        returncode=result.returncode,
        error=parsed["error"],
        artifact_dir=perf_harness.repo_relative(output_dir),
        transitions=parsed["transitions"],
    )


def parse_tlc_states(text: str) -> tuple[int | None, int | None]:
    """Parse TLC output for generated and distinct state counts."""
    matches = list(TLC_FINAL_SUMMARY_REGEX.finditer(text))
    if not matches:
        return None, None
    match = matches[-1]
    generated = int(match.group(1).replace(",", ""))
    distinct = int(match.group(2).replace(",", ""))
    return generated, distinct


def infer_run_index(output_dir: Path) -> int | None:
    """Infer repeated-run index from artifact directories like tlc-run3."""
    match = RUN_INDEX_REGEX.search(output_dir.name)
    if not match:
        return None
    return int(match.group(1))


def run_tlc_check(
    spec: perf_harness.SpecInfo,
    *,
    workers: int,
    timeout: int | float,
    output_dir: Path,
) -> ScalingRunResult:
    """Run TLC (Java) on a spec and return normalized results."""
    if not TLC_JAR.exists():
        raise FileNotFoundError(f"TLC jar not found: {TLC_JAR}")

    perf_harness.ensure_output_dir(output_dir)
    tla_path, cfg_path = perf_harness.validate_spec_files(spec)
    metadir = perf_harness.ensure_output_dir(output_dir / "tlc-metadir")

    cmd = perf_harness.CommandSpec(
        argv=[
            "java",
            "-jar",
            str(TLC_JAR),
            str(tla_path),
            "-config",
            str(cfg_path),
            "-metadir",
            str(metadir),
            "-workers", str(workers),
        ],
        cwd=tla_path.parent,
    )
    result = perf_harness.run_command(cmd, timeout=timeout)

    (output_dir / "stdout.txt").write_text(result.stdout, encoding="utf-8")
    (output_dir / "stderr.txt").write_text(result.stderr, encoding="utf-8")
    perf_harness.write_json(output_dir / "command.json", result.to_dict())

    generated, distinct = parse_tlc_states(f"{result.stdout}\n{result.stderr}")
    error = None
    if result.returncode != 0:
        error = perf_harness.extract_first_error(
            f"{result.stdout}\n{result.stderr}"
        )

    return ScalingRunResult(
        tool="tlc",
        spec_name=spec.name,
        workers=workers,
        elapsed_seconds=result.elapsed_seconds,
        states_found=distinct,
        distinct_states=distinct,
        returncode=result.returncode,
        error=error,
        artifact_dir=perf_harness.repo_relative(output_dir),
        run_index=infer_run_index(output_dir),
        states_generated=generated,
    )


def build_scaling_row(
    spec: perf_harness.SpecInfo,
    tla2_run: ScalingRunResult,
    tlc_run: ScalingRunResult,
) -> dict[str, Any]:
    """Build a single scaling comparison row from paired TLA2 and TLC runs."""
    exact_parity = (
        tla2_run.states_found is not None
        and tlc_run.states_found is not None
        and tla2_run.states_found == tlc_run.states_found
    )
    speedup = None
    if (
        tlc_run.elapsed_seconds > 0
        and tla2_run.elapsed_seconds > 0
        and tla2_run.returncode == 0
        and tlc_run.returncode == 0
    ):
        speedup = tlc_run.elapsed_seconds / tla2_run.elapsed_seconds

    return {
        "spec": spec.name,
        "workers": tla2_run.workers,
        "tla2": tla2_run.to_dict(),
        "tlc": tlc_run.to_dict(),
        "exact_state_parity": exact_parity,
        "speedup": speedup,
    }


def summarize_scaling_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Aggregate scaling rows into a summary with per-spec breakdowns."""
    total = len(rows)
    parity_pass = sum(1 for r in rows if r["exact_state_parity"])
    by_spec: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        by_spec.setdefault(row["spec"], []).append(row)

    spec_summaries = {}
    for spec_name, spec_rows in by_spec.items():
        speedups = [
            r["speedup"] for r in spec_rows if r["speedup"] is not None
        ]
        spec_summaries[spec_name] = {
            "rows": len(spec_rows),
            "parity_pass": sum(
                1 for r in spec_rows if r["exact_state_parity"]
            ),
            "min_speedup": min(speedups) if speedups else None,
            "max_speedup": max(speedups) if speedups else None,
            "worker_counts": [r["workers"] for r in spec_rows],
        }

    return {
        "total_rows": total,
        "parity_pass": parity_pass,
        "parity_fail": total - parity_pass,
        "by_spec": spec_summaries,
    }


def render_scaling_markdown(report: dict[str, Any]) -> str:
    """Render a scaling report dict as a markdown document."""
    lines = [
        "# Category C Parallel Scaling Report",
        "",
        "**Issue:** #3202",
        f"**Commit:** {report.get('git_commit', 'unknown')}",
        f"**Timestamp:** {report.get('timestamp', 'unknown')}",
        f"**Artifacts:** `{report.get('artifact_bundle', 'N/A')}`",
        "",
        "## Summary",
        "",
    ]

    summary = report.get("summary", {})
    lines.append(f"- Total rows: {summary.get('total_rows', 0)}")
    lines.append(f"- Parity pass: {summary.get('parity_pass', 0)}")
    lines.append(f"- Parity fail: {summary.get('parity_fail', 0)}")
    lines.append("")
    lines.extend(_render_matrix_table(report.get("rows", [])))
    lines.extend(_render_selector_section(report.get("selector", {})))
    return "\n".join(lines)


def _render_matrix_table(rows: list[dict[str, Any]]) -> list[str]:
    """Render the scaling matrix as a markdown table."""
    lines = [
        "## Scaling Matrix",
        "",
        "| Spec | Workers | TLA2 (s) | TLC (s) | Speedup | States | Parity |",
        "|------|---------|----------|---------|---------|--------|--------|",
    ]
    for row in rows:
        tla2 = row.get("tla2", {})
        tlc = row.get("tlc", {})
        tla2_t = f"{tla2.get('elapsed_seconds', 0):.1f}"
        tlc_t = f"{tlc.get('elapsed_seconds', 0):.1f}"
        sp = row.get("speedup")
        sp_str = f"{sp:.2f}x" if sp is not None else "N/A"
        st = tla2.get("states_found")
        st_str = f"{st:,}" if st is not None else "?"
        parity = "PASS" if row.get("exact_state_parity") else "FAIL"
        lines.append(
            f"| {row.get('spec', '?')} | {row.get('workers', '?')} "
            f"| {tla2_t} | {tlc_t} | {sp_str} | {st_str} | {parity} |"
        )
    lines.append("")
    return lines


def _render_selector_section(selector: dict[str, Any]) -> list[str]:
    """Render the selector policy section."""
    lines = [
        "## Selector Policy",
        "",
        f"**Action:** {selector.get('action', 'N/A')}",
    ]
    if selector.get("note"):
        lines.append(f"**Note:** {selector['note']}")
    lines.append("")
    return lines
