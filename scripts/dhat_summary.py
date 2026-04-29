#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Summarize dhat heap profiles by allocation family and hot stack.

Part of #3337.

Examples:
    python3 scripts/dhat_summary.py reports/perf/.../dhat-4w.json
    python3 scripts/dhat_summary.py reports/perf/.../dhat-8w.json --top 5
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

WORKSPACE_PREFIXES = (
    "tla_",
    "tla2",
)

RUNTIME_PREFIXES = (
    "[root]",
    "0x",
    "__",
    "<alloc::",
    "<core::",
    "<std::",
    "alloc::",
    "core::",
    "std::",
    "dhat::",
    "mimalloc::",
)


@dataclass(frozen=True)
class StackSample:
    tbk: int
    tb: int
    frames: tuple[str, ...]
    family: str


@dataclass(frozen=True)
class FamilySummary:
    family: str
    tbk: int
    tb: int
    samples: int
    exemplar: tuple[str, ...]


@dataclass(frozen=True)
class ProfileSummary:
    command: str
    total_blocks: int
    total_bytes: int
    total_samples: int
    top_families: tuple[FamilySummary, ...]
    top_stacks: tuple[StackSample, ...]


def normalize_frame(frame: str) -> str:
    """Drop the dhat address prefix while preserving symbol and location."""
    if frame == "[root]":
        return frame
    if frame.startswith("0x") and ": " in frame:
        _address, remainder = frame.split(": ", 1)
        return remainder
    return frame


def frame_symbol(frame: str) -> str:
    """Extract the demangled symbol from a dhat frame entry."""
    normalized = normalize_frame(frame)
    if normalized == "[root]":
        return normalized
    symbol, _separator, _location = normalized.partition(" (")
    return symbol


def is_workspace_symbol(symbol: str) -> bool:
    """Return whether the frame belongs to a workspace crate."""
    return symbol.startswith(WORKSPACE_PREFIXES)


def is_runtime_symbol(symbol: str) -> bool:
    """Return whether the frame is allocator/runtime scaffolding."""
    return symbol.startswith(RUNTIME_PREFIXES)


def classify_family(frames: tuple[str, ...]) -> str:
    """Choose a stable family label from the stack's most relevant frame."""
    symbols = tuple(frame_symbol(frame) for frame in frames)
    for symbol in symbols:
        if is_workspace_symbol(symbol):
            return symbol
    for symbol in symbols:
        if not is_runtime_symbol(symbol):
            return symbol
    return symbols[0] if symbols else "[no frames]"


def stack_from_pp(pp: dict[str, Any], ftbl: list[str]) -> StackSample:
    """Resolve a dhat program point into concrete frames and its family."""
    frames = tuple(ftbl[index] for index in pp.get("fs", []) if 0 <= index < len(ftbl))
    return StackSample(
        tbk=int(pp.get("tbk", 0)),
        tb=int(pp.get("tb", 0)),
        frames=frames,
        family=classify_family(frames),
    )


def summarize_profile(data: dict[str, Any], *, top: int = 10) -> ProfileSummary:
    """Aggregate dhat JSON into top families and exact hot stacks."""
    ftbl = list(data.get("ftbl", []))
    samples = [stack_from_pp(pp, ftbl) for pp in data.get("pps", [])]
    family_totals: dict[str, dict[str, Any]] = {}
    for sample in samples:
        family_entry = family_totals.setdefault(
            sample.family,
            {
                "tbk": 0,
                "tb": 0,
                "samples": 0,
                "exemplar": sample.frames,
                "best_tbk": -1,
            },
        )
        family_entry["tbk"] += sample.tbk
        family_entry["tb"] += sample.tb
        family_entry["samples"] += 1
        if sample.tbk > family_entry["best_tbk"]:
            family_entry["exemplar"] = sample.frames
            family_entry["best_tbk"] = sample.tbk

    top_families = sorted(
        (
            FamilySummary(
                family=family,
                tbk=entry["tbk"],
                tb=entry["tb"],
                samples=entry["samples"],
                exemplar=entry["exemplar"],
            )
            for family, entry in family_totals.items()
        ),
        key=lambda entry: (-entry.tbk, -entry.tb, entry.family),
    )[:top]
    top_stacks = tuple(sorted(samples, key=lambda entry: (-entry.tbk, -entry.tb))[:top])
    return ProfileSummary(
        command=str(data.get("cmd", "")),
        total_blocks=sum(sample.tbk for sample in samples),
        total_bytes=sum(sample.tb for sample in samples),
        total_samples=len(samples),
        top_families=tuple(top_families),
        top_stacks=top_stacks,
    )


def trim_stack(
    frames: tuple[str, ...],
    *,
    limit: int,
    focus_symbol: str | None = None,
) -> tuple[str, ...]:
    """Drop unhelpful prefixes and keep a bounded stack slice for display."""
    symbols = [frame_symbol(frame) for frame in frames]
    first_relevant = 0
    if focus_symbol is not None:
        for index, symbol in enumerate(symbols):
            if symbol == focus_symbol:
                first_relevant = index
                break
        else:
            for index, symbol in enumerate(symbols):
                if not is_runtime_symbol(symbol):
                    first_relevant = index
                    break
    else:
        for index, symbol in enumerate(symbols):
            if not is_runtime_symbol(symbol):
                first_relevant = index
                break
    trimmed = tuple(symbols[first_relevant:])
    if limit <= 0 or len(trimmed) <= limit:
        return trimmed
    return trimmed[:limit]


def render_summary(summary: ProfileSummary, *, stack_limit: int) -> str:
    """Render the summary as stable plain text for reports and issue comments."""
    lines = [
        f"Command: {summary.command}",
        (
            "Totals: "
            f"{summary.total_blocks:,} blocks, "
            f"{summary.total_bytes:,} bytes, "
            f"{summary.total_samples:,} program points"
        ),
        "",
        "Top families by allocation blocks:",
    ]
    for index, family in enumerate(summary.top_families, start=1):
        stack_text = " -> ".join(
            trim_stack(
                family.exemplar,
                limit=stack_limit,
                focus_symbol=family.family,
            )
        )
        lines.append(
            f"{index}. {family.family} | blocks={family.tbk:,} bytes={family.tb:,} samples={family.samples}"
        )
        if stack_text:
            lines.append(f"   stack: {stack_text}")
    lines.append("")
    lines.append("Top exact stacks by allocation blocks:")
    for index, stack in enumerate(summary.top_stacks, start=1):
        stack_text = " -> ".join(
            trim_stack(
                stack.frames,
                limit=stack_limit,
                focus_symbol=stack.family,
            )
        )
        lines.append(f"{index}. blocks={stack.tbk:,} bytes={stack.tb:,} family={stack.family}")
        if stack_text:
            lines.append(f"   stack: {stack_text}")
    return "\n".join(lines)


def create_parser() -> argparse.ArgumentParser:
    """Build the CLI parser."""
    parser = argparse.ArgumentParser(description="Summarize a dhat heap profile")
    parser.add_argument("profile", type=Path, help="Path to dhat-heap.json")
    parser.add_argument("--top", type=int, default=10, help="Number of families/stacks to show")
    parser.add_argument(
        "--stack-limit",
        type=int,
        default=6,
        help="Maximum number of frames to print per exemplar stack",
    )
    return parser


def main() -> int:
    parser = create_parser()
    args = parser.parse_args()
    if args.top <= 0:
        parser.error("--top must be positive")
    if args.stack_limit < 0:
        parser.error("--stack-limit must be non-negative")

    data = json.loads(args.profile.read_text(encoding="utf-8"))
    summary = summarize_profile(data, top=args.top)
    print(render_summary(summary, stack_limit=args.stack_limit))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
