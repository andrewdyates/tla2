#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Check repo-specific current-doc routing invariants.

Guards active `current` reports against drift where historical snapshots are
mistakenly routed as current-head guidance.

Usage:
    check_current_doc_routing.py
    check_current_doc_routing.py --json
    check_current_doc_routing.py --path /path/to/repo
"""

from __future__ import annotations

__all__ = [
    "DocTextGuard",
    "CURRENT_DOC_ROUTING_GUARDS",
    "normalize_whitespace",
    "check_guard_content",
    "check_doc_text_guards",
    "main",
]

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
import re
from typing import Sequence


@dataclass(frozen=True)
class DocTextGuard:
    path: str
    required_substrings: tuple[str, ...] = ()
    forbidden_patterns: tuple[str, ...] = ()


CURRENT_DOC_ROUTING_GUARDS = (
    DocTextGuard(
        path="reports/research/coverage-gap-decomposition-current.md",
        required_substrings=(
            "do not treat `MCBoulanger` as an active current timeout gap",
            "Category C calibration lane",
        ),
        forbidden_patterns=(
            r"^\| MCBoulanger \| 7,866,982 \| 136s \| timeout \| timeout \| Too large for 120s even at TLC parity \|$",
            r"^\*\*3 are genuinely too large\*\* \(dijkstra-mutex, SlushMedium, MCBoulanger\)",
        ),
    ),
    DocTextGuard(
        path="reports/research/2026-03-11-coverage-gap-audit-current.md",
        required_substrings=(
            "do not use `MCBoulanger` as an active current timeout canary",
            "Category C calibration lane",
        ),
        forbidden_patterns=(
            r"^\| MCBoulanger \| 136s \| 7,866,982 \| safety, CONSTRAINT \|$",
            r"^### TLC completes but needs >120s \(11 specs\)$",
        ),
    ),
    DocTextGuard(
        path="reports/research/vision-gap-analysis-current.md",
        required_substrings=("profile the Category C calibration lane",),
        forbidden_patterns=(r"profile Category C timeouts",),
    ),
)


def normalize_whitespace(text: str) -> str:
    """Collapse all runs of whitespace to single spaces."""
    return " ".join(text.split())


def check_guard_content(content: str, guard: DocTextGuard) -> list[str]:
    """Return failures for a single document's content."""
    failures: list[str] = []
    normalized_content = normalize_whitespace(content)

    for required in guard.required_substrings:
        if normalize_whitespace(required) not in normalized_content:
            failures.append(f"missing required text: {required!r}")

    for pattern in guard.forbidden_patterns:
        if re.search(pattern, content, re.MULTILINE):
            failures.append(f"matched forbidden pattern: {pattern}")

    return failures


def check_doc_text_guards(
    base_dir: Path, guards: Sequence[DocTextGuard] | None = None
) -> list[str]:
    """Check all configured doc guards and return failure messages."""
    active_guards = CURRENT_DOC_ROUTING_GUARDS if guards is None else tuple(guards)
    failures: list[str] = []

    for guard in active_guards:
        doc_path = base_dir / guard.path
        if not doc_path.is_file():
            failures.append(f"{guard.path}: file not found")
            continue

        try:
            content = doc_path.read_text(encoding="utf-8")
        except OSError as exc:
            failures.append(f"{guard.path}: read failed: {exc}")
            continue

        for failure in check_guard_content(content, guard):
            failures.append(f"{guard.path}: {failure}")

    return failures


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check repo-specific current-doc routing invariants",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output failures as JSON",
    )
    parser.add_argument(
        "--path",
        type=Path,
        default=None,
        help="Repo root to check (default: current working directory)",
    )
    parser.add_argument(
        "--help-short",
        "-H",
        action="store_true",
        help="Show short help",
    )
    args = parser.parse_args(argv)

    if args.help_short:
        print("check_current_doc_routing.py - Check current-doc routing invariants")
        print("Usage: check_current_doc_routing.py [--json] [--path=DIR]")
        return 0

    base_dir = args.path if args.path else Path.cwd()
    failures = check_doc_text_guards(base_dir)

    if args.json:
        print(json.dumps({"failures": failures, "total_failures": len(failures)}, indent=2))
    else:
        if failures:
            print("=== Current Doc Routing Failures ===")
            for failure in failures:
                print(f"  {failure}")
            print(f"\nTotal failures: {len(failures)}")
        else:
            print("Current doc routing guards passed.")

    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
