#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from parse_tlc_dot import parse_tlc_dot  # noqa: E402


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent
    fixture = repo_root / "test_data" / "tlc_dot" / "DieHard.dot"
    graph = parse_tlc_dot(fixture)

    if not graph.initial_states:
        raise AssertionError("expected at least 1 initial state (style=filled)")
    if not graph.transitions:
        raise AssertionError("expected non-empty edge list")

    missing = []
    for t in graph.transitions:
        if t.src_fp not in graph.states:
            missing.append(f"src missing: {t.src_fp}")
        if t.dst_fp not in graph.states:
            missing.append(f"dst missing: {t.dst_fp}")
        if missing and len(missing) >= 5:
            break
    if missing:
        raise AssertionError("edge endpoint(s) missing from nodes: " + ", ".join(missing))

    for fp in graph.initial_states:
        state = graph.states[fp]
        if state.depth != 0:
            raise AssertionError(f"expected initial state depth=0, got fp={fp} depth={state.depth}")

    print(
        "OK parse_tlc_dot_smoke:"
        f" states={len(graph.states)}"
        f" edges={len(graph.transitions)}"
        f" initials={len(graph.initial_states)}",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

