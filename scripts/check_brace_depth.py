#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
"""Check maximum brace nesting depth in a Rust source file.

Tracks '{' and '}' outside of strings, character literals, and comments
to report the maximum nesting depth and the line where it occurs.

Acceptance criteria: max depth <= 8.
"""

from dataclasses import dataclass
import sys
from typing import Optional


@dataclass
class DepthLine:
    line_number: int
    effective_depth: int
    line_text: str


@dataclass
class BraceScanResult:
    max_depth: int
    max_depth_line: int
    max_depth_text: str
    depth_lines: list[DepthLine]


def _consume_quoted_string(line: str, i: int) -> int:
    """Consume a normal quoted string starting at quote index `i`."""
    i += 1
    while i < len(line):
        if line[i] == '\\':
            i += 2
            continue
        if line[i] == '"':
            return i + 1
        i += 1
    return i


def _raw_string_start(line: str, i: int) -> Optional[tuple[int, int]]:
    """Return (next_index, hash_count) when a raw string starts at `i`."""
    if line[i] == 'r':
        r_idx = i
    elif line[i] == 'b' and i + 1 < len(line) and line[i + 1] == 'r':
        r_idx = i + 1
    else:
        return None

    j = r_idx + 1
    hashes = 0
    while j < len(line) and line[j] == '#':
        hashes += 1
        j += 1
    if j < len(line) and line[j] == '"':
        return j + 1, hashes
    return None


def scan_brace_depth(lines: list[str]) -> BraceScanResult:
    """Scan lines once and return max depth and per-line depth profile."""
    depth = 0
    max_depth = 0
    max_depth_line = 0
    max_depth_text = ""
    depth_lines: list[DepthLine] = []

    block_comment_depth = 0
    raw_string_hashes: Optional[int] = None

    for line_num, line in enumerate(lines, start=1):
        line_start_depth = depth
        i = 0

        while i < len(line):
            if raw_string_hashes is not None:
                closing = '"' + ('#' * raw_string_hashes)
                end_pos = line.find(closing, i)
                if end_pos == -1:
                    i = len(line)
                    continue
                raw_string_hashes = None
                i = end_pos + len(closing)
                continue

            ch = line[i]

            if block_comment_depth > 0:
                if ch == '/' and i + 1 < len(line) and line[i + 1] == '*':
                    block_comment_depth += 1
                    i += 2
                    continue
                if ch == '*' and i + 1 < len(line) and line[i + 1] == '/':
                    block_comment_depth -= 1
                    i += 2
                    continue
                i += 1
                continue

            if ch == '/' and i + 1 < len(line):
                next_ch = line[i + 1]
                if next_ch == '/':
                    break
                if next_ch == '*':
                    block_comment_depth += 1
                    i += 2
                    continue

            raw_start = _raw_string_start(line, i)
            if raw_start is not None:
                i, raw_string_hashes = raw_start
                continue

            if ch == '"' or (ch == 'b' and i + 1 < len(line) and line[i + 1] == '"'):
                quote_idx = i if ch == '"' else i + 1
                i = _consume_quoted_string(line, quote_idx)
                continue

            # Keep character-literal handling simple and local to one line.
            if ch == "'":
                i += 1
                if i < len(line) and line[i] == '\\':
                    i += 1
                if i < len(line):
                    i += 1
                if i < len(line) and line[i] == "'":
                    i += 1
                continue

            if ch == '{':
                depth += 1
                if depth > max_depth:
                    max_depth = depth
                    max_depth_line = line_num
                    max_depth_text = line.rstrip()
            elif ch == '}':
                depth = max(0, depth - 1)

            i += 1

        effective_depth = max(line_start_depth, depth)
        depth_lines.append(DepthLine(line_num, effective_depth, line.rstrip()))

    return BraceScanResult(max_depth, max_depth_line, max_depth_text, depth_lines)


def check_brace_depth(filepath: str) -> tuple[int, int, str]:
    """Return (max_depth, line_number, line_text) for the deepest brace nesting."""
    with open(filepath, "r", encoding="utf-8") as f:
        result = scan_brace_depth(f.readlines())
    return result.max_depth, result.max_depth_line, result.max_depth_text


def main() -> None:
    if len(sys.argv) < 2:
        filepath = "crates/tla-check/src/enumerate/symbolic_assignments.rs"
    else:
        filepath = sys.argv[1]

    with open(filepath, "r", encoding="utf-8") as f:
        scan_result = scan_brace_depth(f.readlines())

    print(f"File: {filepath}")
    print(f"Maximum brace nesting depth: {scan_result.max_depth}")
    print(
        f"Deepest nesting at line {scan_result.max_depth_line}: "
        f"{scan_result.max_depth_text}"
    )
    print()

    print("Lines at depth >= 6:")
    print("-" * 80)
    for depth_line in scan_result.depth_lines:
        if depth_line.effective_depth >= 6 and depth_line.line_text.strip():
            print(
                f"  L{depth_line.line_number:4d} "
                f"[depth {depth_line.effective_depth:2d}]: {depth_line.line_text}"
            )

    print("-" * 80)
    threshold = 8
    if scan_result.max_depth <= threshold:
        print(f"PASS: max depth {scan_result.max_depth} <= {threshold}")
    else:
        print(f"FAIL: max depth {scan_result.max_depth} > {threshold}")
        sys.exit(1)


if __name__ == "__main__":
    main()
