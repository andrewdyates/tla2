#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Select baseline spec names for bounded `tla2 diagnose --spec-list` sweeps.

Examples:
    python3 scripts/select_diagnose_specs.py --tla2-status pass
    python3 scripts/select_diagnose_specs.py --tla2-status pass --max-timeout-seconds 120
    python3 scripts/select_diagnose_specs.py --tla2-status pass --output /tmp/pass_specs.txt
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE = REPO_ROOT / "tests" / "tlc_comparison" / "spec_baseline.json"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--baseline",
        type=Path,
        default=DEFAULT_BASELINE,
        help=f"Path to spec_baseline.json (default: {DEFAULT_BASELINE})",
    )
    parser.add_argument(
        "--tla2-status",
        action="append",
        dest="tla2_statuses",
        default=[],
        help="Keep only specs whose baseline tla2.status matches this value. Repeatable.",
    )
    parser.add_argument(
        "--tlc-status",
        action="append",
        dest="tlc_statuses",
        default=[],
        help="Keep only specs whose baseline tlc.status matches this value. Repeatable.",
    )
    parser.add_argument(
        "--category",
        action="append",
        dest="categories",
        default=[],
        help="Keep only specs in this category. Repeatable.",
    )
    parser.add_argument(
        "--verified-match",
        choices=("true", "false"),
        help="Keep only specs whose verified_match field equals this value.",
    )
    parser.add_argument(
        "--max-timeout-seconds",
        type=int,
        help="Keep only specs whose effective diagnose timeout is <= this value.",
    )
    parser.add_argument(
        "--min-timeout-seconds",
        type=int,
        help="Keep only specs whose effective diagnose timeout is >= this value.",
    )
    parser.add_argument(
        "--timeout-floor-seconds",
        type=int,
        default=120,
        help="CLI timeout floor used when diagnose_timeout_seconds is absent (default: 120).",
    )
    parser.add_argument(
        "--sort",
        choices=("name", "timeout"),
        default="name",
        help="Sort output by spec name or effective timeout (default: name).",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Emit at most this many specs after filtering/sorting.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Write the spec list to this file instead of stdout.",
    )
    return parser.parse_args()


def load_baseline(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def effective_timeout(spec: dict[str, Any], timeout_floor_seconds: int) -> int:
    override = spec.get("diagnose_timeout_seconds")
    if isinstance(override, int) and override > timeout_floor_seconds:
        return override
    return timeout_floor_seconds


def keep_spec(name: str, spec: dict[str, Any], args: argparse.Namespace) -> bool:
    if args.categories and spec.get("category") not in args.categories:
        return False

    tla2_status = spec.get("tla2", {}).get("status")
    if args.tla2_statuses and tla2_status not in args.tla2_statuses:
        return False

    tlc_status = spec.get("tlc", {}).get("status")
    if args.tlc_statuses and tlc_status not in args.tlc_statuses:
        return False

    if args.verified_match is not None:
        want = args.verified_match == "true"
        if bool(spec.get("verified_match")) != want:
            return False

    timeout_seconds = effective_timeout(spec, args.timeout_floor_seconds)
    if args.max_timeout_seconds is not None and timeout_seconds > args.max_timeout_seconds:
        return False
    if args.min_timeout_seconds is not None and timeout_seconds < args.min_timeout_seconds:
        return False

    source = spec.get("source") or {}
    if not source.get("tla_path") or not source.get("cfg_path"):
        return False

    return True


def sort_key(name: str, spec: dict[str, Any], args: argparse.Namespace) -> tuple[Any, ...]:
    timeout_seconds = effective_timeout(spec, args.timeout_floor_seconds)
    if args.sort == "timeout":
        return (timeout_seconds, name)
    return (name,)


def main() -> int:
    args = parse_args()
    baseline = load_baseline(args.baseline)
    specs = baseline.get("specs", {})
    selected = [
        (name, spec)
        for name, spec in specs.items()
        if keep_spec(name, spec, args)
    ]
    selected.sort(key=lambda item: sort_key(item[0], item[1], args))

    if args.limit is not None:
        selected = selected[: args.limit]

    output = "\n".join(name for name, _ in selected)
    if output:
        output += "\n"

    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
