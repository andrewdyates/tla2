#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Run a repeated single-thread TLC vs TLA2 baseline/JIT comparison."""

from __future__ import annotations

import argparse
import json
import logging
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
    "CoffeeCan1000Beans",
    "MCBakery",
    "MCLamportMutex",
    "EWD998Small",
)


@dataclass
class ModeRunResult:
    """Normalized result for one run of TLC or one TLA2 mode."""

    tool: str
    mode: str
    spec_name: str
    run_index: int
    elapsed_seconds: float
    states_found: int | None
    returncode: int
    error: str | None
    artifact_dir: str | None
    env_overrides: dict[str, str] | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "tool": self.tool,
            "mode": self.mode,
            "spec_name": self.spec_name,
            "run_index": self.run_index,
            "elapsed_seconds": self.elapsed_seconds,
            "states_found": self.states_found,
            "returncode": self.returncode,
            "error": self.error,
            "artifact_dir": self.artifact_dir,
            "env_overrides": self.env_overrides,
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


def resolve_tla2_binary(args: argparse.Namespace) -> Path | None:
    """Build once or resolve an explicit tla2 binary."""
    if args.tla2_bin:
        binary = Path(args.tla2_bin)
        if not binary.exists():
            log.error("binary not found: %s", binary)
            return None
        return binary

    target_dir = perf_harness.resolve_target_dir(
        args.target_dir, namespace="benchmark_single_thread"
    )
    build_cmd = perf_harness.build_cargo_build_command(args.cargo_profile, target_dir)
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
    """Run one single-thread TLA2 measurement for a named mode."""
    if mode not in {"interp", "jit"}:
        raise ValueError(f"unsupported mode: {mode}")

    perf_harness.ensure_output_dir(output_dir)

    extra_flags = list(common_flags)
    extra_env = dict(env_overrides or {})
    if mode == "jit":
        extra_flags.extend(["--jit", "--show-tiers"])
        extra_env.setdefault("TLA2_SHOW_TIERS", "1")

    cmd = perf_harness.build_tla2_check_command(
        spec,
        binary_path=tla2_bin,
        extra_flags=extra_flags,
        extra_env=extra_env,
        workers=1,
        profile_enum=False,
        profile_eval=False,
    )
    result = perf_harness.run_command(cmd, timeout=timeout)

    (output_dir / "stdout.txt").write_text(result.stdout, encoding="utf-8")
    (output_dir / "stderr.txt").write_text(result.stderr, encoding="utf-8")
    perf_harness.write_json(output_dir / "command.json", result.to_dict())

    parsed = perf_harness.parse_profiling_output(result.stdout, result.stderr)
    return ModeRunResult(
        tool="tla2",
        mode=mode,
        spec_name=spec.name,
        run_index=run_index,
        elapsed_seconds=result.elapsed_seconds,
        states_found=parsed["states_found"],
        returncode=result.returncode,
        error=parsed["error"],
        artifact_dir=perf_harness.repo_relative(output_dir),
        env_overrides=dict(result.env_overrides) if result.env_overrides else None,
    )


def median_or_none(values: list[float]) -> float | None:
    """Return the median of a list, or None if it is empty."""
    if not values:
        return None
    return float(statistics.median(values))


def aggregate_mode(results: list[ModeRunResult]) -> dict[str, Any]:
    """Summarize repeated runs for one mode."""
    times = [run.elapsed_seconds for run in results if run.returncode == 0]
    states = [run.states_found for run in results]
    state_values = {state for state in states if state is not None}
    return {
        "runs": [run.to_dict() for run in results],
        "median_seconds": median_or_none(times),
        "state_values": sorted(state_values),
        "consistent_states": len(state_values) <= 1,
        "all_ok": all(run.returncode == 0 for run in results),
    }


def summarize_spec(
    spec: perf_harness.SpecInfo,
    interp_runs: list[ModeRunResult],
    jit_runs: list[ModeRunResult],
    tlc_runs: list[scaling.ScalingRunResult],
) -> dict[str, Any]:
    """Build one summary row for a spec."""
    interp_summary = aggregate_mode(interp_runs)
    jit_summary = aggregate_mode(jit_runs)
    tlc_times = [run.elapsed_seconds for run in tlc_runs if run.returncode == 0]
    tlc_states = {run.states_found for run in tlc_runs if run.states_found is not None}
    tlc_median = median_or_none(tlc_times)
    tlc_state_value = next(iter(tlc_states)) if len(tlc_states) == 1 else None

    def speedup(summary: dict[str, Any]) -> float | None:
        mode_median = summary["median_seconds"]
        if tlc_median is None or mode_median in (None, 0):
            return None
        return tlc_median / mode_median

    parity_interp = (
        tlc_state_value is not None
        and interp_summary["consistent_states"]
        and interp_summary["state_values"] == [tlc_state_value]
    )
    parity_jit = (
        tlc_state_value is not None
        and jit_summary["consistent_states"]
        and jit_summary["state_values"] == [tlc_state_value]
    )

    return {
        "spec": spec.name,
        "tlc": {
            "runs": [run.to_dict() for run in tlc_runs],
            "median_seconds": tlc_median,
            "state_values": sorted(tlc_states),
            "consistent_states": len(tlc_states) <= 1,
            "all_ok": all(run.returncode == 0 for run in tlc_runs),
        },
        "interp": interp_summary,
        "jit": jit_summary,
        "parity_interp_vs_tlc": parity_interp,
        "parity_jit_vs_tlc": parity_jit,
        "speedup_interp_vs_tlc": speedup(interp_summary),
        "speedup_jit_vs_tlc": speedup(jit_summary),
    }


def render_markdown(report: dict[str, Any]) -> str:
    """Render a concise markdown report."""
    lines = [
        "# Single-Thread TLA2 vs TLC Benchmark",
        "",
        f"**Timestamp:** {report['timestamp']}",
        f"**Commit:** {report['git_commit']}",
        f"**Artifact bundle:** `{report['artifact_bundle']}`",
        "",
        "## Command",
        "",
        f"`{report['invocation']}`",
        "",
        "## Results",
        "",
        "| Spec | TLC median (s) | TLA2 median (s) | JIT median (s) | TLA2/TLC | JIT/TLC | Parity |",
        "|------|----------------|-----------------|----------------|----------|---------|--------|",
    ]
    for row in report["rows"]:
        tlc_median = _fmt_seconds(row["tlc"]["median_seconds"])
        interp_median = _fmt_seconds(row["interp"]["median_seconds"])
        jit_median = _fmt_seconds(row["jit"]["median_seconds"])
        interp_ratio = _fmt_ratio(row["speedup_interp_vs_tlc"])
        jit_ratio = _fmt_ratio(row["speedup_jit_vs_tlc"])
        parity = "PASS" if row["parity_interp_vs_tlc"] and row["parity_jit_vs_tlc"] else "FAIL"
        lines.append(
            f"| {row['spec']} | {tlc_median} | {interp_median} | {jit_median} | "
            f"{interp_ratio} | {jit_ratio} | {parity} |"
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
        help="extra flag passed to both TLA2 baseline and JIT modes",
    )
    parser.add_argument(
        "--interp-env",
        action="append",
        default=[],
        help="KEY=VALUE override for baseline TLA2 mode",
    )
    parser.add_argument(
        "--jit-env",
        action="append",
        default=[],
        help="KEY=VALUE override for JIT TLA2 mode",
    )
    return parser


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    args = build_cli().parse_args()

    if args.runs <= 0:
        raise ValueError("--runs must be positive")

    interp_env = parse_env_overrides(args.interp_env)
    jit_env = parse_env_overrides(args.jit_env)

    tla2_binary = resolve_tla2_binary(args)
    if tla2_binary is None:
        return 1

    timestamp = perf_harness.current_timestamp()
    output_dir = (
        Path(args.output_dir)
        if args.output_dir
        else perf_harness.REPORTS_ROOT / timestamp / "single-thread-jit-vs-tlc"
    )
    perf_harness.ensure_output_dir(output_dir)

    rows: list[dict[str, Any]] = []
    exit_code = 0
    for spec_name in args.specs:
        spec = perf_harness.require_spec(spec_name)
        log.info("Benchmarking %s", spec.name)

        tlc_runs: list[scaling.ScalingRunResult] = []
        interp_runs: list[ModeRunResult] = []
        jit_runs: list[ModeRunResult] = []

        for run_index in range(1, args.runs + 1):
            log.info("  run %d/%d: TLC", run_index, args.runs)
            tlc_run = scaling.run_tlc_check(
                spec,
                workers=1,
                timeout=args.timeout,
                output_dir=output_dir / spec.name / f"tlc-run{run_index}",
            )
            tlc_runs.append(tlc_run)
            log.info(
                "    TLC %.3fs, states=%s",
                tlc_run.elapsed_seconds,
                tlc_run.states_found,
            )

            log.info("  run %d/%d: TLA2 baseline", run_index, args.runs)
            interp_run = run_tla2_mode(
                spec,
                mode="interp",
                run_index=run_index,
                tla2_bin=tla2_binary,
                timeout=args.timeout,
                output_dir=output_dir / spec.name / f"interp-run{run_index}",
                common_flags=list(args.tla2_flag),
                env_overrides=interp_env,
            )
            interp_runs.append(interp_run)
            log.info(
                "    baseline %.3fs, states=%s",
                interp_run.elapsed_seconds,
                interp_run.states_found,
            )

            log.info("  run %d/%d: TLA2 JIT", run_index, args.runs)
            jit_run = run_tla2_mode(
                spec,
                mode="jit",
                run_index=run_index,
                tla2_bin=tla2_binary,
                timeout=args.timeout,
                output_dir=output_dir / spec.name / f"jit-run{run_index}",
                common_flags=list(args.tla2_flag),
                env_overrides=jit_env,
            )
            jit_runs.append(jit_run)
            log.info(
                "    JIT %.3fs, states=%s",
                jit_run.elapsed_seconds,
                jit_run.states_found,
            )

        row = summarize_spec(spec, interp_runs, jit_runs, tlc_runs)
        rows.append(row)
        if not row["parity_interp_vs_tlc"] or not row["parity_jit_vs_tlc"]:
            exit_code = 1
        if not row["tlc"]["all_ok"] or not row["interp"]["all_ok"] or not row["jit"]["all_ok"]:
            exit_code = 1

    invocation = shlex.join([Path(__file__).name, *sys.argv[1:]])
    report = {
        "timestamp": timestamp,
        "git_commit": perf_harness.git_commit_short(),
        "artifact_bundle": perf_harness.repo_relative(output_dir),
        "invocation": invocation,
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
