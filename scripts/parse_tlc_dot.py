#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import re
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class TLCState:
    fingerprint: int
    label: str
    is_initial: bool
    depth: int | None


@dataclass(frozen=True)
class TLCTransition:
    src_fp: int
    dst_fp: int
    action: str | None


@dataclass(frozen=True)
class TLCStateGraph:
    states: dict[int, TLCState]
    transitions: list[TLCTransition]
    depth_groups: dict[int, set[int]]
    initial_states: set[int]


_NODE_RE = re.compile(r"^(-?\d+)\s+\[(.+)\];?$")
_EDGE_WITH_ATTRS_RE = re.compile(r"^(-?\d+)\s+->\s+(-?\d+)\s+\[(.+)\];?$")
_EDGE_NO_ATTRS_RE = re.compile(r"^(-?\d+)\s+->\s+(-?\d+)\s*;?$")
_RANK_RE = re.compile(r"^\{rank\s*=\s*same;\s*(.+)\}$")


def _extract_quoted_attr(attrs: str, key: str) -> str:
    # TLC emits attributes like:
    #   label="/\\ big = 0\\n/\\ small = 0",style = filled
    #   tooltip="/\\ big = 0\\n/\\ small = 0"
    #   label="FillSmallJug",color="black",fontcolor="black"
    #
    # We intentionally avoid a complex regex for the value because TLC labels
    # routinely contain backslashes (e.g. `/\\`) and escapes (e.g. `\\n`).
    m = re.search(rf"{re.escape(key)}\s*=", attrs)
    if not m:
        raise ValueError(f"Missing {key}= in attrs: {attrs}")

    i = m.end()
    while i < len(attrs) and attrs[i].isspace():
        i += 1
    if i >= len(attrs) or attrs[i] != '"':
        raise ValueError(f"Expected {key} to be a quoted string in attrs: {attrs}")
    i += 1

    raw: list[str] = []
    while i < len(attrs):
        ch = attrs[i]
        if ch == '"':
            return _tlc_dot_unescape("".join(raw))
        if ch == "\\":
            # Preserve escape sequences; they will be decoded by _tlc_dot_unescape.
            if i + 1 >= len(attrs):
                raw.append("\\")
                i += 1
            else:
                raw.append("\\")
                raw.append(attrs[i + 1])
                i += 2
            continue
        raw.append(ch)
        i += 1

    raise ValueError(f"Unterminated quoted string for {key}= in attrs: {attrs}")


def _tlc_dot_unescape(s: str) -> str:
    out: list[str] = []
    i = 0
    while i < len(s):
        ch = s[i]
        if ch != "\\":
            out.append(ch)
            i += 1
            continue

        if i + 1 >= len(s):
            out.append("\\")
            break

        nxt = s[i + 1]
        if nxt == "n":
            out.append("\n")
            i += 2
        elif nxt == "\\":
            out.append("\\")
            i += 2
        elif nxt == '"':
            out.append('"')
            i += 2
        else:
            out.append("\\")
            out.append(nxt)
            i += 2
    return "".join(out)


def _compute_depths(
    initial_states: set[int],
    transitions: list[TLCTransition],
    states: dict[int, TLCState],
) -> tuple[dict[int, int], dict[int, set[int]]]:
    adj: dict[int, list[int]] = defaultdict(list)
    for t in transitions:
        adj[t.src_fp].append(t.dst_fp)

    depth: dict[int, int] = {}
    q: deque[int] = deque()
    for fp in sorted(initial_states):
        if fp in depth:
            continue
        depth[fp] = 0
        q.append(fp)

    while q:
        cur = q.popleft()
        cur_depth = depth[cur]
        for nxt in adj.get(cur, []):
            if nxt in depth:
                continue
            depth[nxt] = cur_depth + 1
            q.append(nxt)

    groups: dict[int, set[int]] = defaultdict(set)
    for fp, d in depth.items():
        groups[d].add(fp)

    return depth, groups


def parse_tlc_dot(path: Path) -> TLCStateGraph:
    """
    Parse TLC DOT output (from `-dump dot` / `-dump dot,actionlabels`) into an
    in-memory state graph.

    This parser is intentionally line-oriented and recognizes only the subset
    of DOT emitted by TLC's DotStateWriter.
    """
    states: dict[int, TLCState] = {}
    transitions: list[TLCTransition] = []
    initial_states: set[int] = set()

    for raw_line in path.read_text().splitlines():
        line = raw_line.strip()
        if not line:
            continue

        if _RANK_RE.match(line):
            continue

        if m := _NODE_RE.match(line):
            fp = int(m.group(1))
            attrs = m.group(2)
            label = _extract_quoted_attr(attrs, "label")
            is_initial = (
                ("style = filled" in attrs or "style=filled" in attrs)
                and "fillcolor" not in attrs
            )
            if is_initial:
                initial_states.add(fp)
            states[fp] = TLCState(fp, label, is_initial, None)
            continue

        if m := _EDGE_WITH_ATTRS_RE.match(line):
            src = int(m.group(1))
            dst = int(m.group(2))
            attrs = m.group(3)
            action = None
            if "label=" in attrs:
                action = _extract_quoted_attr(attrs, "label")
            transitions.append(TLCTransition(src, dst, action))
            continue

        if m := _EDGE_NO_ATTRS_RE.match(line):
            src = int(m.group(1))
            dst = int(m.group(2))
            transitions.append(TLCTransition(src, dst, None))
            continue

    depth_map, depth_groups = _compute_depths(initial_states, transitions, states)
    states_with_depth: dict[int, TLCState] = {}
    for fp, state in states.items():
        states_with_depth[fp] = TLCState(
            fingerprint=state.fingerprint,
            label=state.label,
            is_initial=state.is_initial,
            depth=depth_map.get(fp),
        )

    return TLCStateGraph(
        states=states_with_depth,
        transitions=transitions,
        depth_groups=depth_groups,
        initial_states=initial_states,
    )
