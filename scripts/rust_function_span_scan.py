#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Scan Rust files and report function spans.

This scanner tracks braces while ignoring comments and string literals so
function lengths are not inflated by brace-like characters in non-code text.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class _PendingFunction:
    name: str
    start_line: int
    start_depth: int


@dataclass(frozen=True)
class FunctionSpan:
    file: Path
    start_line: int
    name: str
    lines: int


def _is_ident_start(ch: str) -> bool:
    return ch == "_" or ch.isalpha()


def _is_ident_continue(ch: str) -> bool:
    return ch == "_" or ch.isalnum()


def _is_hex_digit(ch: str) -> bool:
    return ch in "0123456789abcdefABCDEF"


def _consume_identifier(source: str, start: int) -> tuple[str, int] | None:
    """Return (identifier, next_index) for normal and raw identifiers."""
    if start >= len(source):
        return None
    ch = source[start]
    if ch == "r" and start + 2 < len(source) and source[start + 1] == "#":
        if not _is_ident_start(source[start + 2]):
            return None
        j = start + 3
        while j < len(source) and _is_ident_continue(source[j]):
            j += 1
        return (source[start:j], j)
    if not _is_ident_start(ch):
        return None
    j = start + 1
    while j < len(source) and _is_ident_continue(source[j]):
        j += 1
    return (source[start:j], j)


def _raw_string_prefix(source: str, start: int) -> tuple[int, int] | None:
    """Return (prefix_len, hash_count) if a raw string starts at `start`."""
    i = start
    if i >= len(source):
        return None
    if source[i] == "b":
        if i + 1 >= len(source) or source[i + 1] != "r":
            return None
        i += 2
    elif source[i] == "r":
        i += 1
    else:
        return None

    hash_count = 0
    while i < len(source) and source[i] == "#":
        hash_count += 1
        i += 1
    if i < len(source) and source[i] == '"':
        return (i - start + 1, hash_count)
    return None


def _char_literal_len(source: str, start: int) -> int:
    """Return char literal length starting at `start`, or 0 if not a char literal."""
    if start + 2 >= len(source) or source[start] != "'":
        return 0
    i = start + 1
    if source[i] == "\\":
        i += 1
        if i >= len(source):
            return 0
        esc = source[i]
        if esc == "x":
            if i + 2 >= len(source):
                return 0
            if not (_is_hex_digit(source[i + 1]) and _is_hex_digit(source[i + 2])):
                return 0
            i += 3
        elif esc == "u":
            i += 1
            if i >= len(source) or source[i] != "{":
                return 0
            i += 1
            hex_digits = 0
            while i < len(source) and _is_hex_digit(source[i]):
                hex_digits += 1
                i += 1
            if hex_digits == 0 or i >= len(source) or source[i] != "}":
                return 0
            i += 1
        else:
            i += 1
    else:
        if source[i] in {"'", "\n", "\r"}:
            return 0
        i += 1
    if i < len(source) and source[i] == "'":
        return i - start + 1
    return 0


def scan_file(path: Path) -> list[FunctionSpan]:
    source = path.read_text(encoding="utf-8")

    spans: list[FunctionSpan] = []
    pending: _PendingFunction | None = None
    active: list[_PendingFunction] = []

    depth = 0
    line = 1
    i = 0
    n = len(source)

    in_line_comment = False
    block_comment_depth = 0
    in_string = False
    in_raw_string = False
    raw_hashes = 0

    expect_fn_name = False
    fn_keyword_line = 0
    pending_signature_nesting = 0

    while i < n:
        ch = source[i]

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                line += 1
            i += 1
            continue

        if block_comment_depth > 0:
            if source.startswith("/*", i):
                block_comment_depth += 1
                i += 2
                continue
            if source.startswith("*/", i):
                block_comment_depth -= 1
                i += 2
                continue
            if ch == "\n":
                line += 1
            i += 1
            continue

        if in_string:
            if ch == "\\":
                if i + 1 < n and source[i + 1] == "\n":
                    line += 1
                i += 2
                continue
            if ch == '"':
                in_string = False
                i += 1
                continue
            if ch == "\n":
                line += 1
            i += 1
            continue

        if in_raw_string:
            if ch == "\n":
                line += 1
                i += 1
                continue
            if ch == '"' and source.startswith("#" * raw_hashes, i + 1):
                i += 1 + raw_hashes
                in_raw_string = False
                continue
            i += 1
            continue

        if source.startswith("//", i):
            in_line_comment = True
            i += 2
            continue

        if source.startswith("/*", i):
            block_comment_depth = 1
            i += 2
            continue

        raw_prefix = _raw_string_prefix(source, i)
        if raw_prefix is not None:
            prefix_len, raw_hashes = raw_prefix
            in_raw_string = True
            i += prefix_len
            continue

        if ch == '"' or (ch == "b" and i + 1 < n and source[i + 1] == '"'):
            if ch == "b":
                i += 1
            in_string = True
            i += 1
            continue

        if ch == "'":
            literal_len = _char_literal_len(source, i)
            if literal_len:
                i += literal_len
                continue

        if ch == "{":
            is_body_start = (
                pending is not None
                and pending_signature_nesting == 0
                and depth == pending.start_depth
            )
            depth += 1
            if is_body_start:
                active.append(pending)
                pending = None
                pending_signature_nesting = 0
            elif pending is not None:
                pending_signature_nesting += 1
            i += 1
            continue

        if ch == "}":
            if pending is not None and pending_signature_nesting > 0:
                pending_signature_nesting -= 1
            if depth > 0:
                depth -= 1
            while active and depth <= active[-1].start_depth:
                fn = active.pop()
                spans.append(
                    FunctionSpan(
                        file=path,
                        start_line=fn.start_line,
                        name=fn.name,
                        lines=line - fn.start_line + 1,
                    )
                )
            i += 1
            continue

        if ch == ";":
            if pending is not None and pending_signature_nesting > 0:
                i += 1
                continue
            pending = None
            expect_fn_name = False
            pending_signature_nesting = 0
            i += 1
            continue

        if pending is not None:
            if ch in "([<":
                pending_signature_nesting += 1
                i += 1
                continue
            if ch in ")]>" and pending_signature_nesting > 0:
                pending_signature_nesting -= 1
                i += 1
                continue

        identifier = _consume_identifier(source, i)
        if identifier is not None:
            token_line = line
            token, j = identifier
            if token == "fn":
                if pending is None and not expect_fn_name:
                    expect_fn_name = True
                    fn_keyword_line = token_line
            elif expect_fn_name:
                pending = _PendingFunction(
                    name=token,
                    start_line=fn_keyword_line,
                    start_depth=depth,
                )
                expect_fn_name = False
                pending_signature_nesting = 0
            i = j
            continue

        if expect_fn_name and ch not in {" ", "\t", "\r", "\n"}:
            expect_fn_name = False

        if ch == "\n":
            line += 1
        i += 1

    return spans


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Report Rust functions that exceed a configured line limit."
    )
    parser.add_argument("--limit", type=int, required=True, help="Function length limit")
    parser.add_argument("files", nargs="+", help="Rust source files to scan")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    limit = args.limit

    for file_name in args.files:
        path = Path(file_name)
        for span in scan_file(path):
            if span.lines > limit:
                print(f"{span.file}:{span.start_line}: fn {span.name} ({span.lines} lines)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
