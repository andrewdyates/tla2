#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Execution and artifact helpers for scripts/profile_spec.py."""

from __future__ import annotations

import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import perf_harness
from profile_sample_capture import record_sample_skip, run_sample_capture
from perf_harness import CommandResult, CommandSpec, SpecInfo

@dataclass(frozen=True)
class RunConfig:
    """Validated CLI state for one profiling invocation."""

    spec: SpecInfo
    workers: int
    timeout: int
    extra_flags: str
    cargo_profile: str
    output_dir: Path
    target_dir: Path
    binary_path: Path
    build_command: CommandSpec
    run_command: CommandSpec
    sample_seconds: int | None
    sample_interval_ms: int
    warmup_seconds: float
    timestamp: str
def write_line(message: str = "", *, stderr: bool = False) -> None:
    """Write one line to stdout or stderr."""
    stream = sys.stderr if stderr else sys.stdout
    stream.write(f"{message}\n")
def list_specs() -> int:
    """Print the available spec names."""
    write_line("Available specs:")
    for spec in perf_harness.ALL_SPECS:
        write_line(f"  {spec.name}")
    return 0
def completed_result(
    command: CommandSpec,
    *,
    started: float,
    returncode: int,
    stdout: str,
    stderr: str,
) -> CommandResult:
    """Create a completed CommandResult from collected process output."""
    return CommandResult(
        argv=command.argv,
        cwd=str(command.cwd),
        returncode=returncode,
        elapsed_seconds=time.monotonic() - started,
        stdout=stdout,
        stderr=stderr,
    )
def timeout_result(
    command: CommandSpec,
    *,
    started: float,
    timeout: int,
    stdout: str,
    stderr: str,
) -> CommandResult:
    """Create a timeout-shaped CommandResult with a consistent message."""
    combined_stderr = stderr or f"Timeout after {timeout} seconds"
    if stderr:
        combined_stderr = f"{stderr}\n\nTimeout after {timeout} seconds"
    return completed_result(
        command,
        started=started,
        returncode=124,
        stdout=stdout,
        stderr=combined_stderr,
    )
def run_command_with_optional_sample(
    command: CommandSpec,
    *,
    timeout: int,
    sample_seconds: int | None,
    sample_interval_ms: int,
    warmup_seconds: float,
    sample_output_path: Path | None,
) -> tuple[CommandResult, dict[str, Any] | None]:
    """Run the checker and optionally attach macOS `sample` to the process."""
    if sample_seconds is None:
        return perf_harness.run_command(command, timeout=timeout), None

    started = time.monotonic()
    process = subprocess.Popen(
        command.argv,
        cwd=command.cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    if warmup_seconds > 0:
        time.sleep(warmup_seconds)

    if process.poll() is None:
        assert sample_output_path is not None
        sample_meta = run_sample_capture(
            command,
            process=process,
            sample_seconds=sample_seconds,
            sample_interval_ms=sample_interval_ms,
            sample_output_path=sample_output_path,
        )
    else:
        assert sample_output_path is not None
        sample_meta = record_sample_skip(sample_output_path, warmup_seconds)

    try:
        elapsed_before_wait = time.monotonic() - started
        remaining_timeout = max(timeout - elapsed_before_wait, 0.1)
        stdout, stderr = process.communicate(timeout=remaining_timeout)
        return (
            completed_result(
                command,
                started=started,
                returncode=process.returncode,
                stdout=stdout,
                stderr=stderr,
            ),
            sample_meta,
        )
    except subprocess.TimeoutExpired:
        process.kill()
        stdout, stderr = process.communicate()
        return timeout_result(
            command,
            started=started,
            timeout=timeout,
            stdout=stdout,
            stderr=stderr,
        ), sample_meta


def write_command_log(
    output_dir: Path,
    *,
    workers: int,
    build_command: CommandSpec,
    run_command: CommandSpec,
    sample_meta: dict[str, Any] | None,
) -> None:
    """Persist the command log for reproducible profiling runs."""
    lines = [
        f"workers: {workers}",
        f"build: {perf_harness.command_to_string(build_command.argv)}",
        f"build_cwd: {build_command.cwd}",
        f"run: {perf_harness.command_to_string(run_command.argv)}",
        f"run_cwd: {run_command.cwd}",
    ]
    if sample_meta is not None:
        sample_command = sample_meta.get("argv")
        lines.append(f"sample_status: {sample_meta.get('status', 'unknown')}")
        if sample_command:
            lines.append(f"sample: {perf_harness.command_to_string(sample_command)}")
        else:
            lines.append(f"sample: skipped ({sample_meta['stderr']})")
    (output_dir / "command.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_build_artifacts(output_dir: Path, build_result: CommandResult) -> tuple[str, str]:
    """Persist cargo build stdout/stderr for profiling workflow diagnostics."""
    build_stdout_path = output_dir / "build.stdout.txt"
    build_stderr_path = output_dir / "build.stderr.txt"
    build_stdout_path.write_text(build_result.stdout, encoding="utf-8")
    build_stderr_path.write_text(build_result.stderr, encoding="utf-8")
    return (
        perf_harness.repo_relative(build_stdout_path),
        perf_harness.repo_relative(build_stderr_path),
    )


def build_summary(
    spec: SpecInfo,
    *,
    workers: int,
    timestamp: str,
    timeout: int,
    extra_flags: str,
    cargo_profile: str,
    target_dir: Path,
    binary_path: Path,
    build_result: CommandResult,
    run_result: CommandResult,
    sample_meta: dict[str, Any] | None,
) -> dict[str, Any]:
    """Assemble the structured summary.json payload."""
    summary = perf_harness.parse_profiling_output(run_result.stdout, run_result.stderr)
    summary.update(
        {
            "spec_name": spec.name,
            "workers": workers,
            "tla_path": spec.tla_path,
            "cfg_path": spec.cfg_path,
            "category": spec.category,
            "expected_states": spec.expected_states,
            "timeout_used": timeout,
            "extra_flags": extra_flags if extra_flags else None,
            "timestamp": timestamp,
            "returncode": run_result.returncode,
            "cargo_profile": cargo_profile,
            "target_dir": perf_harness.repo_relative(target_dir),
            "binary_path": perf_harness.repo_relative(binary_path),
            "command": run_result.argv,
            "command_cwd": run_result.cwd,
            "build": {
                "command": build_result.argv,
                "cwd": build_result.cwd,
                "returncode": build_result.returncode,
                "elapsed_seconds": build_result.elapsed_seconds,
            },
            "sample": sample_meta,
        }
    )
    return summary


def show_run_header(config: RunConfig) -> None:
    """Print the resolved workflow inputs before the build starts."""
    write_line(f"Profiling: {config.spec.name}")
    write_line(f"  TLA: {config.spec.tla_path}")
    write_line(f"  Config: {config.spec.cfg_path}")
    write_line(f"  Timeout: {config.timeout}s")
    write_line(f"  Workers: {config.workers}")
    write_line(f"  Cargo profile: {config.cargo_profile}")
    write_line(f"  Target dir: {config.target_dir}")
    write_line(f"  Binary path: {config.binary_path}")
    write_line(f"  Output: {config.output_dir}")
    if config.sample_seconds is not None:
        write_line(
            "  Sample: "
            f"{config.sample_seconds}s at {config.sample_interval_ms}ms "
            f"(warmup {config.warmup_seconds:.3f}s)"
        )
    write_line()


def build_metadata(config: RunConfig, build_result: CommandResult) -> dict[str, Any]:
    """Build the `build.json` payload for one profiling run."""
    return {
        "workers": config.workers,
        "cargo_profile": config.cargo_profile,
        "target_dir": perf_harness.repo_relative(config.target_dir),
        "binary_path": perf_harness.repo_relative(config.binary_path),
        "build": {
            "command": build_result.argv,
            "cwd": build_result.cwd,
            "returncode": build_result.returncode,
            "elapsed_seconds": build_result.elapsed_seconds,
        },
        "run_command": config.run_command.argv,
        "run_cwd": str(config.run_command.cwd),
        "sample_seconds": config.sample_seconds,
        "sample_interval_ms": config.sample_interval_ms,
        "warmup_seconds": config.warmup_seconds,
    }


def persist_build_failure(
    config: RunConfig,
    *,
    build_result: CommandResult,
    build_json: dict[str, Any],
) -> int:
    """Write failure artifacts for a build that never reached checker execution."""
    if build_result.returncode == 0:
        build_json["error"] = f"built binary not found at {config.binary_path}"
    perf_harness.write_json(config.output_dir / "build.json", build_json)
    (config.output_dir / "stdout.txt").write_text("", encoding="utf-8")
    (config.output_dir / "stderr.txt").write_text(build_result.stderr, encoding="utf-8")
    write_command_log(
        config.output_dir,
        workers=config.workers,
        build_command=config.build_command,
        run_command=config.run_command,
        sample_meta=None,
    )
    if build_result.stderr:
        write_line(build_result.stderr, stderr=True)
    if build_result.returncode == 0:
        write_line(f"Error: built binary not found at {config.binary_path}", stderr=True)
        return 1
    return build_result.returncode


def persist_success(
    config: RunConfig,
    *,
    build_result: CommandResult,
    build_json: dict[str, Any],
    run_result: CommandResult,
    sample_meta: dict[str, Any] | None,
) -> dict[str, Any]:
    """Persist build/run artifacts and return the structured summary payload."""
    (config.output_dir / "stdout.txt").write_text(run_result.stdout, encoding="utf-8")
    (config.output_dir / "stderr.txt").write_text(run_result.stderr, encoding="utf-8")
    build_json["sample"] = sample_meta
    perf_harness.write_json(config.output_dir / "build.json", build_json)
    write_command_log(
        config.output_dir,
        workers=config.workers,
        build_command=config.build_command,
        run_command=config.run_command,
        sample_meta=sample_meta,
    )
    summary = build_summary(
        config.spec,
        workers=config.workers,
        timestamp=config.timestamp,
        timeout=config.timeout,
        extra_flags=config.extra_flags,
        cargo_profile=config.cargo_profile,
        target_dir=config.target_dir,
        binary_path=config.binary_path,
        build_result=build_result,
        run_result=run_result,
        sample_meta=sample_meta,
    )
    perf_harness.write_json(config.output_dir / "summary.json", summary)
    return summary


def show_summary(
    *,
    build_result: CommandResult,
    run_result: CommandResult,
    summary: dict[str, Any],
    sample_meta: dict[str, Any] | None,
    output_dir: Path,
) -> None:
    """Print the human-readable profiling summary."""
    write_line("=== Profiling Summary ===")
    write_line(f"  Return code: {run_result.returncode}")
    write_line(f"  Build time: {build_result.elapsed_seconds:.3f}s")
    write_line(f"  Checker time: {run_result.elapsed_seconds:.3f}s")
    if summary["states_found"] is not None:
        write_line(f"  States found: {summary['states_found']}")
    if summary["runtime_sec"] is not None:
        write_line(f"  Runtime: {summary['runtime_sec']:.3f}s")
    if sample_meta is not None:
        write_line(f"  Sample status: {sample_meta.get('status', 'unknown')}")
        write_line(f"  Sample artifact: {sample_meta['artifact']}")
        if sample_meta.get("status") != "succeeded" and sample_meta.get("stderr"):
            write_line(f"  Sample detail: {sample_meta['stderr'][:100]}")
    if summary["error"]:
        write_line(f"  Error: {summary['error'][:100]}...")
    write_line()
    write_line(f"Output saved to: {output_dir}")


def run_profile(config: RunConfig) -> int:
    """Execute one deterministic profiling run from a validated config."""
    show_run_header(config)
    write_line("Building profiling binary...")
    build_result = perf_harness.run_command(config.build_command)
    build_json = build_metadata(config, build_result)
    build_stdout_artifact, build_stderr_artifact = write_build_artifacts(config.output_dir, build_result)
    build_json["build"]["stdout_artifact"] = build_stdout_artifact
    build_json["build"]["stderr_artifact"] = build_stderr_artifact

    if build_result.returncode != 0 or not config.binary_path.exists():
        return persist_build_failure(config, build_result=build_result, build_json=build_json)

    write_line("Running checker...")
    sample_output_path = (
        config.output_dir / "sample.txt" if config.sample_seconds is not None else None
    )
    run_result, sample_meta = run_command_with_optional_sample(
        config.run_command,
        timeout=config.timeout,
        sample_seconds=config.sample_seconds,
        sample_interval_ms=config.sample_interval_ms,
        warmup_seconds=config.warmup_seconds,
        sample_output_path=sample_output_path,
    )
    summary = persist_success(
        config,
        build_result=build_result,
        build_json=build_json,
        run_result=run_result,
        sample_meta=sample_meta,
    )
    show_summary(
        build_result=build_result,
        run_result=run_result,
        summary=summary,
        sample_meta=sample_meta,
        output_dir=config.output_dir,
    )
    return run_result.returncode
