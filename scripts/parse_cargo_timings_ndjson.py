#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class ParseResult:
    timings: list[tuple[str, float]]
    skipped_non_json_lines: int


def _iter_lines(path: Path) -> Iterable[str]:
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                yield line


def parse_cargo_timings_ndjson(path: Path) -> ParseResult:
    timings: list[tuple[str, float]] = []
    skipped = 0

    for line in _iter_lines(path):
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            skipped += 1
            continue

        if obj.get("reason") != "timing-info":
            continue

        package_id = str(obj.get("package_id", "unknown"))
        package = package_id.split()[0] if package_id else "unknown"

        duration_raw = obj.get("duration", 0.0)
        try:
            duration = float(duration_raw)
        except (TypeError, ValueError):
            duration = 0.0

        timings.append((package, duration))

    timings.sort(key=lambda x: x[1], reverse=True)
    return ParseResult(timings=timings, skipped_non_json_lines=skipped)


def print_markdown_summary(result: ParseResult, top: int) -> None:
    if not result.timings:
        msg = "(no timing data)"
        if result.skipped_non_json_lines:
            msg += f" (skipped {result.skipped_non_json_lines} non-JSON lines)"
        print(msg)
        return

    total = sum(d for _, d in result.timings)
    print("| Package | Duration | % of Total |")
    print("|---------|----------|------------|")

    for pkg, dur in result.timings[:top]:
        pct = (dur / total * 100.0) if total > 0 else 0.0
        print(f"| {pkg[:30]} | {dur:.2f}s | {pct:.1f}% |")

    pct_total = 100.0 if total > 0 else 0.0
    print(f"| TOTAL | {total:.2f}s | {pct_total:.1f}% |")

    if result.skipped_non_json_lines:
        print(f"(skipped {result.skipped_non_json_lines} non-JSON lines)")


def _self_test() -> int:
    # Empty file
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp) / "empty.ndjson"
        p.write_text("", encoding="utf-8")
        r = parse_cargo_timings_ndjson(p)
        assert r.timings == []
        assert r.skipped_non_json_lines == 0

    # Malformed + non-timing JSON
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp) / "mixed.ndjson"
        p.write_text(
            "\n".join(
                [
                    "Compiling foo v0.1.0",
                    '{"reason":"compiler-artifact","duration":1.0}',
                    '{"reason":"timing-info","package_id":"p#0.1.0","duration":0.5}',
                    "{not json}",
                    '{"reason":"timing-info","package_id":"q#0.1.0","duration":"1.25"}',
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        r = parse_cargo_timings_ndjson(p)
        assert r.timings == [("q#0.1.0", 1.25), ("p#0.1.0", 0.5)]
        assert r.skipped_non_json_lines == 2

    print("self-test: ok")
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="Parse cargo --timings=json mixed output.")
    ap.add_argument("path", nargs="?", help="Path to captured cargo output (mixed text + JSON).")
    ap.add_argument("--top", type=int, default=5, help="Number of rows to print.")
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="Run basic parser self-tests and exit.",
    )
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    if not args.path:
        ap.error("path is required unless --self-test is provided")

    path = Path(args.path)
    try:
        result = parse_cargo_timings_ndjson(path)
    except FileNotFoundError:
        print("(no timing data)")
        return 0

    print_markdown_summary(result, top=args.top)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
