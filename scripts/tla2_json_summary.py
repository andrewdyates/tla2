#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""
Summarize TLA2 `--output json` results for shell scripts.

This helper is intentionally forgiving:
- Missing/invalid JSON => prints a single line with `status=parse_error`.
- Missing fields default to empty strings / 0s.

TSV columns (8):
  status, error_type, error_code, violated_type, violated_name,
  states_found, states_distinct, has_counterexample
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def _sanitize_field(value: object) -> str:
    if value is None:
        return ""
    s = str(value)
    return s.replace("\t", " ").replace("\n", " ").strip()


def _summarize(obj: object) -> dict[str, object]:
    if not isinstance(obj, dict):
        return {
            "status": "parse_error",
            "error_type": "",
            "error_code": "",
            "violated_type": "",
            "violated_name": "",
            "states_found": 0,
            "states_distinct": 0,
            "has_counterexample": 0,
        }

    result = obj.get("result") if isinstance(obj.get("result"), dict) else {}
    stats = obj.get("statistics") if isinstance(obj.get("statistics"), dict) else {}
    violated = (
        result.get("violated_property")
        if isinstance(result.get("violated_property"), dict)
        else {}
    )

    status = result.get("status") or ""
    states_found = stats.get("states_found")
    states_distinct = stats.get("states_distinct")

    if not isinstance(states_found, int):
        states_found = 0
    if not isinstance(states_distinct, int):
        states_distinct = states_found

    has_counterexample = 1 if obj.get("counterexample") is not None else 0

    return {
        "status": status,
        "error_type": result.get("error_type") or "",
        "error_code": result.get("error_code") or "",
        "violated_type": violated.get("prop_type") or "",
        "violated_name": violated.get("name") or "",
        "states_found": states_found,
        "states_distinct": states_distinct,
        "has_counterexample": has_counterexample,
    }


def _read_json(path: str) -> object:
    if path == "-":
        return json.loads(sys.stdin.read())
    return json.loads(Path(path).read_text(encoding="utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", help="Path to JSON file, or '-' for stdin")
    parser.add_argument(
        "--format",
        choices=("tsv", "json"),
        default="tsv",
        help="Output format (default: tsv)",
    )
    args = parser.parse_args()

    try:
        obj = _read_json(args.path)
        summary = _summarize(obj)
    except Exception:
        summary = _summarize(None)

    if args.format == "json":
        sys.stdout.write(json.dumps(summary, sort_keys=True))
        sys.stdout.write("\n")
        return 0

    fields = [
        summary["status"],
        summary["error_type"],
        summary["error_code"],
        summary["violated_type"],
        summary["violated_name"],
        summary["states_found"],
        summary["states_distinct"],
        summary["has_counterexample"],
    ]
    sys.stdout.write("\t".join(_sanitize_field(f) for f in fields))
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

