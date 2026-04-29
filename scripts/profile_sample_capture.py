#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Sample subprocess helpers for scripts/profile_spec.py."""

from __future__ import annotations

import subprocess
import time
from pathlib import Path
from typing import Any

import perf_harness
from perf_harness import CommandSpec


def build_sample_meta(
    sample_command: list[str] | None,
    *,
    status: str,
    sample_output_path: Path,
    elapsed_seconds: float,
    returncode: int | None,
    stdout: str,
    stderr: str,
) -> dict[str, Any]:
    """Normalize sample capture metadata for build.json and summary.json."""
    return {
        "status": status,
        "argv": sample_command,
        "returncode": returncode,
        "elapsed_seconds": elapsed_seconds,
        "stdout": stdout,
        "stderr": stderr,
        "artifact": perf_harness.repo_relative(sample_output_path),
        "artifact_bytes": sample_output_path.stat().st_size if sample_output_path.exists() else 0,
    }


def ensure_sample_artifact_text(sample_output_path: Path, message: str) -> None:
    """Write a diagnostic artifact when sample produced no usable output."""
    if sample_output_path.exists() and sample_output_path.stat().st_size > 0:
        return
    sample_output_path.write_text(f"{message.rstrip()}\n", encoding="utf-8")


def record_sample_skip(sample_output_path: Path, warmup_seconds: float) -> dict[str, Any]:
    """Persist and describe a skipped sample capture."""
    message = f"process exited before sampling after {warmup_seconds:.3f}s warmup"
    sample_output_path.write_text(f"{message}\n", encoding="utf-8")
    return build_sample_meta(
        None,
        status="skipped",
        sample_output_path=sample_output_path,
        elapsed_seconds=0.0,
        returncode=None,
        stdout="",
        stderr=message,
    )


def record_sample_timeout(
    sample_command: list[str],
    *,
    sample_output_path: Path,
    elapsed_seconds: float,
    timeout_seconds: int,
    stdout: str,
) -> dict[str, Any]:
    """Persist and describe a timed-out sample capture."""
    message = f"sample timed out after {timeout_seconds} seconds"
    ensure_sample_artifact_text(sample_output_path, message)
    return build_sample_meta(
        sample_command,
        status="timed_out",
        sample_output_path=sample_output_path,
        elapsed_seconds=elapsed_seconds,
        returncode=124,
        stdout=stdout,
        stderr=message,
    )


def record_completed_sample(
    sample_command: list[str],
    *,
    sample_output_path: Path,
    elapsed_seconds: float,
    sampled: subprocess.CompletedProcess[str],
) -> dict[str, Any]:
    """Normalize a completed sample subprocess into explicit artifact status."""
    artifact_bytes = sample_output_path.stat().st_size if sample_output_path.exists() else 0
    if sampled.returncode != 0:
        message = (
            sampled.stderr.strip()
            or sampled.stdout.strip()
            or f"sample exited with return code {sampled.returncode} without producing output"
        )
        ensure_sample_artifact_text(sample_output_path, message)
        return build_sample_meta(
            sample_command,
            status="failed",
            sample_output_path=sample_output_path,
            elapsed_seconds=elapsed_seconds,
            returncode=sampled.returncode,
            stdout=sampled.stdout,
            stderr=sampled.stderr or message,
        )
    if artifact_bytes == 0:
        message = sampled.stderr.strip() or sampled.stdout.strip() or "sample exited without producing output"
        ensure_sample_artifact_text(sample_output_path, message)
        return build_sample_meta(
            sample_command,
            status="empty_output",
            sample_output_path=sample_output_path,
            elapsed_seconds=elapsed_seconds,
            returncode=sampled.returncode,
            stdout=sampled.stdout,
            stderr=sampled.stderr or message,
        )
    return build_sample_meta(
        sample_command,
        status="succeeded",
        sample_output_path=sample_output_path,
        elapsed_seconds=elapsed_seconds,
        returncode=sampled.returncode,
        stdout=sampled.stdout,
        stderr=sampled.stderr,
    )


def run_sample_capture(
    command: CommandSpec,
    *,
    process: subprocess.Popen[str],
    sample_seconds: int,
    sample_interval_ms: int,
    sample_output_path: Path,
) -> dict[str, Any]:
    """Run macOS sample with a bounded wait and normalized artifact metadata."""
    sample_command = perf_harness.build_sample_command(
        process.pid,
        duration_seconds=sample_seconds,
        interval_ms=sample_interval_ms,
        output_path=sample_output_path,
    )
    sample_started = time.monotonic()
    sample_timeout = max(sample_seconds + 5, 10)
    try:
        sampled = subprocess.run(
            sample_command,
            cwd=command.cwd,
            capture_output=True,
            check=False,
            text=True,
            timeout=sample_timeout,
        )
    except subprocess.TimeoutExpired as exc:
        return record_sample_timeout(
            sample_command,
            sample_output_path=sample_output_path,
            elapsed_seconds=time.monotonic() - sample_started,
            timeout_seconds=sample_timeout,
            stdout=exc.stdout or "",
        )
    return record_completed_sample(
        sample_command,
        sample_output_path=sample_output_path,
        elapsed_seconds=time.monotonic() - sample_started,
        sampled=sampled,
    )
