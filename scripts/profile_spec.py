#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""
Profile a single spec from the spec catalog with a deterministic binary path.

Part of #3013.

Examples:
    python3 scripts/profile_spec.py MCBakery
    python3 scripts/profile_spec.py MCKVSSafetySmall --cargo-profile profiling --sample-seconds 15
    python3 scripts/profile_spec.py TransitiveClosure --target-dir target/profile_spec/manual

Output:
    reports/perf/<ISO-8601-timestamp>/<spec_name>/
        - command.txt: build/run/sample commands
        - build.json: cargo profile, target dir, binary path, command metadata
        - build.stdout.txt: captured cargo build stdout
        - build.stderr.txt: captured cargo build stderr
        - stdout.txt: captured checker stdout
        - stderr.txt: captured checker stderr
        - summary.json: structured profiling summary
        - sample.txt: symbolicated macOS sample output (when enabled)
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import perf_harness
from perf_harness import ALL_SPECS, CommandSpec, SpecInfo
from profile_spec_workflow import RunConfig, list_specs, run_profile, write_line


def parse_profiling_output(stdout: str, stderr: str) -> dict[str, Any]:
    """Backward-compatible wrapper for shared profiling output parsing."""
    return perf_harness.parse_profiling_output(stdout, stderr)


def build_commands(
    spec: SpecInfo,
    *,
    cargo_profile: str,
    target_dir: str | None,
    extra_flags: str,
    detailed: bool,
    workers: int,
) -> tuple[CommandSpec, CommandSpec, Path, Path]:
    """Build the deterministic cargo build and direct-binary run commands."""
    resolved_target_dir = perf_harness.resolve_target_dir(target_dir)
    binary_path = perf_harness.resolve_binary_path(resolved_target_dir, cargo_profile)
    build_command = perf_harness.build_cargo_build_command(cargo_profile, resolved_target_dir)
    run_command = perf_harness.build_tla2_check_command(
        spec,
        binary_path=binary_path,
        extra_flags=perf_harness.parse_extra_flags(extra_flags),
        profile_enum=True,
        profile_eval=True,
        profile_enum_detail=detailed,
        workers=workers,
        force=True,
    )
    return build_command, run_command, resolved_target_dir, binary_path


def build_summary(*args: Any, **kwargs: Any) -> dict[str, Any]:
    """Re-export summary assembly for the focused pytest coverage."""
    from profile_spec_workflow import build_summary as build_summary_impl

    return build_summary_impl(*args, **kwargs)


def extra_flags_override_workers(extra_flags: str) -> bool:
    """Reject worker overrides in extra flags so metadata stays unambiguous."""
    for token in perf_harness.parse_extra_flags(extra_flags):
        if token == "--workers" or token.startswith("--workers="):
            return True
        if token == "-w" or token.startswith("-w="):
            return True
        if token.startswith("-w") and token[2:].isdigit():
            return True
    return False


def create_parser() -> argparse.ArgumentParser:
    """Build the CLI parser for the profiling workflow."""
    parser = argparse.ArgumentParser(
        description="Profile a single spec from the spec catalog",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("spec_name", nargs="?", help="Spec name from spec_catalog.py (e.g., MCBakery)")
    parser.add_argument(
        "--timeout",
        type=int,
        default=None,
        help="Checker timeout in seconds (default: spec's timeout_seconds from catalog)",
    )
    parser.add_argument(
        "--extra-flags",
        default="",
        help="Additional flags to pass to tla2 check (e.g., '--max-states 100000')",
    )
    parser.add_argument(
        "--output-dir",
        default=None,
        help="Override output directory (default: reports/perf/<timestamp>/<spec_name>)",
    )
    parser.add_argument(
        "--target-dir",
        default=None,
        help="Explicit cargo target dir (default: target/profile_spec/<role-scope>)",
    )
    parser.add_argument(
        "--cargo-profile",
        default="release",
        help="Cargo profile used to build the profiling binary (default: release)",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=1,
        help="Worker count passed to `tla2 check` (default: 1)",
    )
    parser.add_argument(
        "--sample-seconds",
        type=int,
        default=None,
        help="Attach macOS `sample` for N seconds while the checker runs",
    )
    parser.add_argument(
        "--sample-interval-ms",
        type=int,
        default=1,
        help="Sampling interval in milliseconds for macOS `sample` (default: 1)",
    )
    parser.add_argument(
        "--warmup-seconds",
        type=float,
        default=0.0,
        help="Seconds to wait after launch before attaching `sample` (default: 0)",
    )
    parser.add_argument("--list", action="store_true", help="List all available spec names and exit")
    parser.add_argument(
        "--detailed",
        action="store_true",
        help="Enable detailed enumeration profiling (--profile-enum-detail)",
    )
    return parser


def validate_cli_args(args: argparse.Namespace, parser: argparse.ArgumentParser) -> None:
    """Reject invalid sampling-related arguments before any work starts."""
    if args.workers <= 0:
        parser.error("--workers must be positive")
    if extra_flags_override_workers(args.extra_flags):
        parser.error("pass worker count via --workers, not --extra-flags")
    if args.sample_seconds is not None and args.sample_seconds <= 0:
        parser.error("--sample-seconds must be positive")
    if args.sample_interval_ms <= 0:
        parser.error("--sample-interval-ms must be positive")
    if args.warmup_seconds < 0:
        parser.error("--warmup-seconds must be non-negative")


def resolve_run_config(args: argparse.Namespace) -> RunConfig:
    """Resolve CLI args into validated runtime configuration."""
    spec = perf_harness.find_spec(args.spec_name)
    if spec is None:
        raise KeyError(f"Spec '{args.spec_name}' not found in catalog")

    timeout = args.timeout if args.timeout else spec.timeout_seconds
    timestamp = perf_harness.current_timestamp()
    output_dir = (
        Path(args.output_dir)
        if args.output_dir
        else perf_harness.REPORTS_ROOT / timestamp / spec.name
    )
    perf_harness.ensure_output_dir(output_dir)
    build_command, run_command, target_dir, binary_path = build_commands(
        spec,
        cargo_profile=args.cargo_profile,
        target_dir=args.target_dir,
        extra_flags=args.extra_flags,
        detailed=args.detailed,
        workers=args.workers,
    )
    return RunConfig(
        spec=spec,
        workers=args.workers,
        timeout=timeout,
        extra_flags=args.extra_flags,
        cargo_profile=args.cargo_profile,
        output_dir=output_dir,
        target_dir=target_dir,
        binary_path=binary_path,
        build_command=build_command,
        run_command=run_command,
        sample_seconds=args.sample_seconds,
        sample_interval_ms=args.sample_interval_ms,
        warmup_seconds=args.warmup_seconds,
        timestamp=timestamp,
    )


def main() -> int:
    parser = create_parser()
    args = parser.parse_args()

    if args.list:
        return list_specs()
    if args.spec_name is None:
        parser.print_help()
        return 1

    validate_cli_args(args, parser)
    try:
        config = resolve_run_config(args)
    except (FileNotFoundError, KeyError) as exc:
        write_line(f"Error: {exc}", stderr=True)
        return 1
    return run_profile(config)


if __name__ == "__main__":
    sys.exit(main())
