#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Run the issue #3202 Category C scaling matrix and persist current artifacts."""

from __future__ import annotations

import argparse
import json
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

DEFAULT_SPECS = ("MCKVSSafetySmall", "MCBoulanger")
DEFAULT_WORKERS = (1, 2, 4, 8)
STABLE_JSON = perf_harness.REPORTS_ROOT / "issue-3202-category-c-parallel-scaling-current.json"
STABLE_MD = perf_harness.REPORTS_ROOT / "issue-3202-category-c-parallel-scaling-current.md"


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
    """Build once or resolve an explicit binary. Returns None on failure."""
    if args.tla2_bin:
        binary = Path(args.tla2_bin)
        if not binary.exists():
            log.error("binary not found: %s", binary)
            return None
        return binary

    target_dir = perf_harness.resolve_target_dir(
        args.target_dir, namespace="benchmark_scaling"
    )
    build_cmd = perf_harness.build_cargo_build_command(
        args.cargo_profile, target_dir
    )
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


def run_matrix(
    specs: list[str],
    worker_counts: list[int],
    timeout: int,
    output_dir: Path,
    tla2_binary: Path,
) -> tuple[list[dict[str, Any]], int]:
    """Run all (spec, workers) combinations and return (rows, exit_code)."""
    rows: list[dict[str, Any]] = []
    exit_code = 0

    for spec_name in specs:
        spec = perf_harness.require_spec(spec_name)
        log.info("Benchmarking %s", spec.name)
        for workers in worker_counts:
            log.info("  workers=%d", workers)
            spec_dir = output_dir / spec.name
            tla2_run = scaling.run_tla2_check(
                spec,
                workers=workers,
                timeout=timeout,
                output_dir=spec_dir / f"tla2-workers{workers}",
                tla2_bin=tla2_binary,
            )
            tlc_run = scaling.run_tlc_check(
                spec,
                workers=workers,
                timeout=timeout,
                output_dir=spec_dir / f"tlc-workers{workers}",
            )
            row = scaling.build_scaling_row(spec, tla2_run, tlc_run)
            rows.append(row)

            if not row["exact_state_parity"]:
                exit_code = 1

            _log_row(tla2_run, tlc_run, row)

    return rows, exit_code


def _log_row(
    tla2_run: scaling.ScalingRunResult,
    tlc_run: scaling.ScalingRunResult,
    row: dict[str, Any],
) -> str:
    """Log a self-contained row summary and return the formatted line."""
    tla2_st = "?" if tla2_run.states_found is None else f"{tla2_run.states_found:,}"
    tlc_st = "?" if tlc_run.states_found is None else f"{tlc_run.states_found:,}"
    parity = "PASS" if row["exact_state_parity"] else "FAIL"
    line = (
        f"{row['spec']}: "
        f"TLA2={tla2_run.elapsed_seconds:.1f}s/{tla2_st} "
        f"TLC={tlc_run.elapsed_seconds:.1f}s/{tlc_st} "
        f"parity={parity} (w={row['workers']})"
    )
    log.info("    %s", line)
    return line


def build_cli() -> argparse.ArgumentParser:
    """Build the argument parser."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--specs", nargs="+", default=list(DEFAULT_SPECS))
    parser.add_argument("--workers", default="1,2,4,8")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--output-dir", default=None)
    parser.add_argument("--current-json", default=str(STABLE_JSON))
    parser.add_argument("--current-markdown", default=str(STABLE_MD))
    parser.add_argument("--selector-action", default="unchanged")
    parser.add_argument("--selector-note", default="")
    parser.add_argument("--tla2-bin", default=None)
    parser.add_argument("--cargo-profile", default="release")
    parser.add_argument("--target-dir", default=None)
    return parser


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    args = build_cli().parse_args()

    worker_counts = parse_workers(args.workers)
    timestamp = perf_harness.current_timestamp()
    output_dir = (
        Path(args.output_dir) if args.output_dir
        else perf_harness.REPORTS_ROOT / timestamp / "issue-3202-category-c-parallel-scaling"
    )
    perf_harness.ensure_output_dir(output_dir)

    tla2_binary = resolve_tla2_binary(args)
    if tla2_binary is None:
        return 1

    rows, exit_code = run_matrix(
        args.specs, worker_counts, args.timeout, output_dir, tla2_binary
    )

    report = {
        "issue": 3202,
        "timestamp": timestamp,
        "git_commit": perf_harness.git_commit_short(),
        "artifact_bundle": perf_harness.repo_relative(output_dir),
        "rows": rows,
        "summary": scaling.summarize_scaling_rows(rows),
        "selector": {
            "action": args.selector_action,
            "note": args.selector_note,
        },
    }
    markdown = scaling.render_scaling_markdown(report)

    current_json = Path(args.current_json)
    current_md = Path(args.current_markdown)
    perf_harness.ensure_output_dir(current_json.parent)
    perf_harness.ensure_output_dir(current_md.parent)
    current_json.write_text(json.dumps(report, indent=2), encoding="utf-8")
    current_md.write_text(markdown, encoding="utf-8")

    log.info("Current JSON report: %s", current_json)
    log.info("Current markdown report: %s", current_md)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
