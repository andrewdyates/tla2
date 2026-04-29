#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Core data types, parsers, and classifiers for liveness verdict comparison.

Extracted from liveness_verdict_matrix.py for #1518.
"""

from __future__ import annotations

import hashlib
import os
import re
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class SpecTarget:
    name: str
    source: str
    spec_path: Path
    cfg_path: Path
    temporal_markers: tuple[str, ...]


@dataclass(frozen=True)
class TraceInfo:
    state_count: int
    has_stuttering: bool
    signature: str | None


def prepend_to_tla_path(env: dict[str, str], extra_path: Path) -> None:
    extra = str(extra_path)
    if not extra:
        return
    existing = env.get("TLA_PATH")
    if not existing:
        env["TLA_PATH"] = extra
        return
    entries = [entry for entry in existing.split(os.pathsep) if entry]
    if extra not in entries:
        env["TLA_PATH"] = os.pathsep.join([extra, *entries])
    else:
        env["TLA_PATH"] = os.pathsep.join([extra, *[entry for entry in entries if entry != extra]])


def config_has_property(cfg_path: Path) -> bool:
    if not cfg_path.exists():
        return False
    text = cfg_path.read_text(encoding="utf-8", errors="replace")
    return re.search(r"(?m)^\s*PROPERTY(?:\s|$)", text) is not None


def module_has_fairness(spec_path: Path) -> bool:
    if not spec_path.exists():
        return False
    text = spec_path.read_text(encoding="utf-8", errors="replace")
    return re.search(r"\b(?:WF_|SF_)", text) is not None


def temporal_markers(spec_path: Path, cfg_path: Path) -> tuple[str, ...]:
    markers: list[str] = []
    if config_has_property(cfg_path):
        markers.append("PROPERTY")
    if module_has_fairness(spec_path):
        markers.append("WF_/SF_")
    return tuple(markers)


def resolve_test_spec_path(cfg_path: Path) -> Path | None:
    direct = cfg_path.with_suffix(".tla")
    if direct.exists():
        return direct

    stem = cfg_path.stem
    prefixes: list[str] = []
    if "_" in stem:
        parts = stem.split("_")
        for idx in range(len(parts) - 1, 0, -1):
            prefixes.append("_".join(parts[:idx]))
    if "-" in stem:
        parts = stem.split("-")
        for idx in range(len(parts) - 1, 0, -1):
            prefixes.append("-".join(parts[:idx]))

    prefixes.append(stem)
    seen: set[str] = set()
    for prefix in prefixes:
        if prefix in seen:
            continue
        seen.add(prefix)
        candidate = cfg_path.with_name(f"{prefix}.tla")
        if candidate.exists():
            return candidate

    tla_files = sorted(cfg_path.parent.glob("*.tla"))
    if len(tla_files) == 1:
        return tla_files[0]

    return None


def parse_tlc_states(output: str) -> int | None:
    # Use findall and take the LAST match: TLC progress lines also contain
    # "N distinct states found" with intermediate counts.  The final summary
    # line is always the last occurrence.
    matches = re.findall(r"([0-9,]+)\s+distinct states found", output)
    if not matches:
        return None
    return int(matches[-1].replace(",", ""))


def parse_tla2_states(output: str) -> int | None:
    match = re.search(r"States found:\s*([0-9,]+)", output)
    if match is None:
        return None
    return int(match.group(1).replace(",", ""))


def classify_tlc_status(output: str, return_code: int) -> str:
    lower = output.lower()
    if return_code == 124:
        return "timeout"
    if "temporal properties were violated" in lower:
        return "liveness"
    if "invariant" in lower and "violated" in lower:
        return "invariant"
    if "deadlock reached" in lower:
        return "deadlock"
    if "model checking completed. no error has been found" in lower:
        return "success"
    if parse_tlc_states(output) is not None and "error:" not in lower and return_code == 0:
        return "success"
    if return_code != 0:
        return "error"
    if "error:" in lower:
        return "error"
    return "unknown"


def classify_tla2_status(output: str, return_code: int) -> str:
    lower = output.lower()
    if return_code == 124:
        return "timeout"
    if "liveness" in lower and "violated" in lower:
        return "liveness"
    if "invariant" in lower and "violated" in lower:
        return "invariant"
    if "deadlock" in lower:
        return "deadlock"
    if "model checking complete" in lower and "no errors found" in lower and return_code == 0:
        return "success"
    if return_code != 0:
        return "error"
    if "error:" in lower:
        return "error"
    return "unknown"


def normalize_assignment_line(line: str) -> str:
    cleaned = line.strip()
    if cleaned.startswith("/\\"):
        cleaned = cleaned[2:].strip()
    return cleaned


def parse_trace_info(output: str, tool: str) -> TraceInfo:
    if tool == "tlc":
        state_header = re.compile(r"^State\s+([0-9]+):")
        assignment_predicate = lambda line: line.startswith("/\\") or line.startswith(" ")
    else:
        state_header = re.compile(r"^State\s+([0-9]+)[ :]")
        assignment_predicate = lambda line: line.startswith(" ")

    states: list[int] = []
    assignments: list[tuple[int, str]] = []
    current_state: int | None = None
    for raw_line in output.splitlines():
        match = state_header.match(raw_line)
        if match is not None:
            current_state = int(match.group(1))
            states.append(current_state)
            continue

        if current_state is None:
            continue
        if assignment_predicate(raw_line):
            cleaned = normalize_assignment_line(raw_line)
            if cleaned:
                assignments.append((current_state, cleaned))
            continue
        if raw_line.strip() == "":
            continue
        current_state = None

    signature: str | None = None
    if assignments:
        payload = "\n".join(
            f"{idx}\t{text}"
            for idx, text in sorted(assignments, key=lambda item: (item[0], item[1]))
        )
        signature = hashlib.sha256(payload.encode("utf-8")).hexdigest()

    return TraceInfo(
        state_count=len(states),
        has_stuttering="stuttering" in output.lower(),
        signature=signature,
    )
