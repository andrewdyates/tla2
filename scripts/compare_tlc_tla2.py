#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""
Compare TLC DOT state graph against TLA2 successor debug output.

Usage:
    java -jar tla2tools.jar -dump dot,actionlabels /tmp/tlc.dot SPEC.tla

    TLA2_DEBUG_SUCCESSORS=1 TLA2_DEBUG_SUCCESSORS_TLCFP=1 \
      cargo run --bin tla2 -- check SPEC.tla 2>&1 > /tmp/tla2_debug.txt

    # Write matching config provenance sidecars for both artifacts.
    ./scripts/compare_tlc_tla2.py \
      --write-provenance \
      --spec-path SPEC.tla \
      --cfg-path SPEC.cfg \
      /tmp/tlc.dot /tmp/tla2_debug.txt

    ./scripts/compare_tlc_tla2.py /tmp/tlc.dot /tmp/tla2_debug.txt

Part of #597, #562
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

# Import the DOT parser
sys.path.insert(0, str(Path(__file__).parent))
from parse_tlc_dot import parse_tlc_dot, TLCStateGraph

LOG = logging.getLogger(__name__)


@dataclass(frozen=True)
class TLA2State:
    fingerprint: int  # Signed 64-bit (converted from hex u64)
    depth: int
    label: str | None


@dataclass(frozen=True)
class TLA2Successor:
    src_fp: int
    dst_fp: int
    action: str | None


@dataclass
class TLA2DebugOutput:
    states: dict[int, TLA2State]  # fp -> state
    successors: list[TLA2Successor]
    initial_states: set[int]
    depth_groups: dict[int, set[int]]


@dataclass(frozen=True)
class ConfigProvenance:
    spec_path: str
    cfg_path: str
    cfg_sha256: str


def hex_u64_to_signed_i64(hex_str: str) -> int:
    """Convert a hex u64 string to signed i64 (Java long).

    TLA2 outputs fingerprints as hex u64 (with or without 0x prefix).
    TLC DOT uses signed decimal long.
    Java long is two's complement: if value >= 2^63, subtract 2^64.
    """
    # int(hex_str, 16) handles both "0x1234" and "1234" formats
    val = int(hex_str, 16)
    if val >= (1 << 63):
        val -= (1 << 64)
    return val


# Regex patterns for TLA2 debug output
# Format: STATE <internal_fp> tlc=<tlc_fp_hex> depth=<d> -> N successors ...
# Example: STATE 9dc3d08535a15415 tlc=0b9ed133720eec70 depth=0 -> 3 successors (diff/parallel)
_STATE_RE = re.compile(r"^STATE\s+[0-9a-fA-F]+\s+tlc=([0-9a-fA-F]+)\s+depth=(\d+)")
# Successor line (when detailed output enabled):
#   succ internal=<internal_fp> tlc=<tlc_fp> changes=N action=Name
_SUCC_RE = re.compile(r"^\s*succ\s+internal=[0-9a-fA-F]+\s+tlc=([0-9a-fA-F]+)(?:\s+changes=\d+)?(?:\s+action=(\S+))?")
# Alternate successor format: succ <id> tlc=0x<hex> (action=Name)
_SUCC_ALT_RE = re.compile(r"^\s*succ\s+\d+\s+tlc=(0x[0-9a-fA-F]+|[0-9a-fA-F]+)(?:\s+\(action=([^)]+)\))?")
# Current state being explored (older format): from_state <id> tlc=0x...
_FROM_STATE_RE = re.compile(r"^from_state\s+\d+\s+tlc=([0-9a-fA-F]+|0x[0-9a-fA-F]+)")


def parse_tla2_debug(path: Path) -> TLA2DebugOutput:
    """Parse TLA2 successor debug output.

    Expected format (from TLA2_DEBUG_SUCCESSORS=1 TLA2_DEBUG_SUCCESSORS_TLCFP=1):
        STATE <internal_fp> tlc=<tlc_fp_hex> depth=<d> -> N successors ...

    With detailed output:
        STATE <internal_fp> tlc=<tlc_fp_hex> depth=<d> -> N successors ...
          succ internal=<internal_fp> tlc=<tlc_fp> changes=N action=Name
    """
    states: dict[int, TLA2State] = {}
    successors: list[TLA2Successor] = []
    initial_states: set[int] = set()
    depth_groups: dict[int, set[int]] = defaultdict(set)

    current_src_fp: int | None = None

    for line in path.read_text().splitlines():
        # Try STATE line first
        if m := _STATE_RE.match(line):
            fp = hex_u64_to_signed_i64(m.group(1))
            depth = int(m.group(2))
            states[fp] = TLA2State(fp, depth, None)
            depth_groups[depth].add(fp)
            if depth == 0:
                initial_states.add(fp)
            # Set current source for any following successor lines
            current_src_fp = fp
            continue

        # Check for from_state (current source for successors)
        if m := _FROM_STATE_RE.match(line):
            current_src_fp = hex_u64_to_signed_i64(m.group(1))
            continue

        # Check for successor (detailed format)
        if m := _SUCC_RE.match(line):
            if current_src_fp is None:
                continue
            dst_fp = hex_u64_to_signed_i64(m.group(1))
            action = m.group(2)
            successors.append(TLA2Successor(current_src_fp, dst_fp, action))
            continue

        # Check for successor (alternate format)
        if m := _SUCC_ALT_RE.match(line):
            if current_src_fp is None:
                continue
            dst_fp = hex_u64_to_signed_i64(m.group(1))
            action = m.group(2)
            successors.append(TLA2Successor(current_src_fp, dst_fp, action))
            continue

    return TLA2DebugOutput(
        states=states,
        successors=successors,
        initial_states=initial_states,
        depth_groups=depth_groups,
    )


def default_provenance_path(artifact_path: Path) -> Path:
    return artifact_path.with_suffix(f"{artifact_path.suffix}.provenance.json")


def _read_cfg_sha256(cfg_path: str) -> str:
    cfg_file = Path(cfg_path)
    if not cfg_file.exists():
        raise FileNotFoundError(
            f"Cannot compute cfg_sha256: cfg file does not exist: {cfg_file}"
        )
    return hashlib.sha256(cfg_file.read_bytes()).hexdigest()


def write_config_provenance(path: Path, provenance: ConfigProvenance) -> None:
    payload = {
        "schema_version": 1,
        "source": {
            "spec_path": provenance.spec_path,
            "cfg_path": provenance.cfg_path,
            "cfg_sha256": provenance.cfg_sha256,
        },
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def load_config_provenance(path: Path, *, kind: str) -> ConfigProvenance:
    if not path.exists():
        raise FileNotFoundError(
            f"{kind} provenance sidecar not found: {path}\n"
            "Create it with --write-provenance --spec-path ... --cfg-path ..."
        )

    try:
        payload = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise ValueError(f"{kind} provenance sidecar is not valid JSON: {path}: {exc}") from exc

    source = payload.get("source", payload)
    required_fields = ("spec_path", "cfg_path", "cfg_sha256")
    missing = [field for field in required_fields if not isinstance(source.get(field), str) or not source.get(field)]
    if missing:
        raise ValueError(
            f"{kind} provenance missing required fields {missing}: {path}"
        )

    return ConfigProvenance(
        spec_path=source["spec_path"],
        cfg_path=source["cfg_path"],
        cfg_sha256=source["cfg_sha256"],
    )


def assert_same_config_provenance(tlc: ConfigProvenance, tla2: ConfigProvenance) -> None:
    mismatches: list[str] = []
    if tlc.spec_path != tla2.spec_path:
        mismatches.append(f"spec_path: TLC={tlc.spec_path!r} TLA2={tla2.spec_path!r}")
    if tlc.cfg_path != tla2.cfg_path:
        mismatches.append(f"cfg_path: TLC={tlc.cfg_path!r} TLA2={tla2.cfg_path!r}")
    if tlc.cfg_sha256 != tla2.cfg_sha256:
        mismatches.append(
            f"cfg_sha256: TLC={tlc.cfg_sha256!r} TLA2={tla2.cfg_sha256!r}"
        )
    if mismatches:
        detail = "; ".join(mismatches)
        raise ValueError(f"Config provenance mismatch: {detail}")


_PROVENANCE_ARGS = [
    (("--tlc-provenance",), {"type": Path, "default": None, "help": "Provenance sidecar path for TLC artifact"}),
    (("--tla2-provenance",), {"type": Path, "default": None, "help": "Provenance sidecar path for TLA2 artifact"}),
    (("--allow-missing-provenance",), {"action": "store_true", "help": "Allow compare without provenance sidecars"}),
    (("--write-provenance",), {"action": "store_true", "help": "Write provenance sidecars for both artifacts"}),
    (("--spec-path",), {"type": str, "default": None, "help": "Spec path for sidecars (required with --write-provenance)"}),
    (("--cfg-path",), {"type": str, "default": None, "help": "Config path for sidecars (required with --write-provenance)"}),
    (("--cfg-sha256",), {"type": str, "default": None, "help": "Config sha256 for sidecars; otherwise computed from --cfg-path"}),
]


def compare_graphs(tlc: TLCStateGraph, tla2: TLA2DebugOutput, verbose: bool = False) -> int:
    """Compare TLC and TLA2 state graphs. Returns exit code (0=match, 1=mismatch)."""

    tlc_fps = set(tlc.states.keys())
    tla2_fps = set(tla2.states.keys())

    print("State Graph Comparison")
    print("=" * 40)
    print()
    print(f"TLC States:  {len(tlc_fps):,}")
    print(f"TLA2 States: {len(tla2_fps):,}")
    print()

    # Set comparison
    common = tlc_fps & tla2_fps
    tlc_only = tlc_fps - tla2_fps
    tla2_only = tla2_fps - tlc_fps

    print("Fingerprint Analysis:")
    print(f"  Common:    {len(common):,}")
    print(f"  TLC-only:  {len(tlc_only):,}")
    print(f"  TLA2-only: {len(tla2_only):,}")
    print()

    if len(tlc_only) == 0 and len(tla2_only) == 0:
        print("MATCH: Both tools found identical state sets.")
        # Also check transitions
        tlc_edges = set((t.src_fp, t.dst_fp) for t in tlc.transitions)
        tla2_edges = set((s.src_fp, s.dst_fp) for s in tla2.successors)

        common_edges = tlc_edges & tla2_edges
        tlc_only_edges = tlc_edges - tla2_edges
        tla2_only_edges = tla2_edges - tlc_edges

        print()
        print("Transition Analysis:")
        print(f"  TLC transitions:  {len(tlc_edges):,}")
        print(f"  TLA2 transitions: {len(tla2_edges):,}")
        print(f"  Common:           {len(common_edges):,}")
        print(f"  TLC-only:         {len(tlc_only_edges):,}")
        print(f"  TLA2-only:        {len(tla2_only_edges):,}")

        if len(tlc_only_edges) == 0 and len(tla2_only_edges) == 0:
            print()
            print("PERFECT MATCH: State sets AND transitions are identical.")
            return 0
        else:
            print()
            print("WARNING: State sets match but transitions differ.")
            return 1

    # Find first divergence by depth
    print("Per-Depth Analysis:")
    max_depth = max(
        max(tlc.depth_groups.keys()) if tlc.depth_groups else 0,
        max(tla2.depth_groups.keys()) if tla2.depth_groups else 0,
    )

    first_diverge_depth = None
    for depth in range(max_depth + 1):
        tlc_at_depth = tlc.depth_groups.get(depth, set())
        tla2_at_depth = tla2.depth_groups.get(depth, set())

        tlc_count = len(tlc_at_depth)
        tla2_count = len(tla2_at_depth)

        if tlc_count == tla2_count and tlc_at_depth == tla2_at_depth:
            status = "MATCH"
        else:
            status = "DIVERGE"
            if first_diverge_depth is None:
                first_diverge_depth = depth

        print(f"  Depth {depth}: TLC={tlc_count:,}, TLA2={tla2_count:,} ({status})")

    print()

    if first_diverge_depth is not None:
        print(f"First Divergence: Depth {first_diverge_depth}")
        print()

        # Find example states that differ
        tlc_at_div = tlc.depth_groups.get(first_diverge_depth, set())
        tla2_at_div = tla2.depth_groups.get(first_diverge_depth, set())

        missing_in_tla2 = tlc_at_div - tla2_at_div
        missing_in_tlc = tla2_at_div - tlc_at_div

        if missing_in_tla2:
            print("Example states in TLC but not TLA2:")
            for fp in sorted(missing_in_tla2)[:5]:  # Show up to 5
                state = tlc.states.get(fp)
                if state:
                    label_preview = state.label[:80] if state.label else "(no label)"
                    print(f"  FP: {fp}")
                    print(f"      {label_preview}")

                    # Find predecessor
                    for t in tlc.transitions:
                        if t.dst_fp == fp:
                            action_str = f" via {t.action}" if t.action else ""
                            print(f"      Predecessor: {t.src_fp}{action_str}")
                            break
                    print()

        if missing_in_tlc and verbose:
            print("Example states in TLA2 but not TLC:")
            for fp in sorted(missing_in_tlc)[:5]:
                print(f"  FP: {fp}")
            print()

    # Analyze actions at divergence point
    if first_diverge_depth is not None and first_diverge_depth > 0:
        parent_depth = first_diverge_depth - 1
        tlc_parents = tlc.depth_groups.get(parent_depth, set())
        tla2_parents = tla2.depth_groups.get(parent_depth, set())
        common_parents = tlc_parents & tla2_parents

        if common_parents:
            print("Action Analysis at Divergence:")

            # Build successor maps
            tlc_succ_map: dict[int, dict[int, str | None]] = defaultdict(dict)
            for t in tlc.transitions:
                tlc_succ_map[t.src_fp][t.dst_fp] = t.action

            tla2_succ_map: dict[int, dict[int, str | None]] = defaultdict(dict)
            for s in tla2.successors:
                tla2_succ_map[s.src_fp][s.dst_fp] = s.action

            # Find parent with different successors
            for parent_fp in sorted(common_parents)[:3]:
                tlc_succs = set(tlc_succ_map.get(parent_fp, {}).keys())
                tla2_succs = set(tla2_succ_map.get(parent_fp, {}).keys())

                if tlc_succs != tla2_succs:
                    missing_succs = tlc_succs - tla2_succs
                    extra_succs = tla2_succs - tlc_succs

                    print(f"  From state {parent_fp}:")
                    print(f"    TLC successors:  {len(tlc_succs)}")
                    print(f"    TLA2 successors: {len(tla2_succs)}")

                    if missing_succs:
                        print(f"    Missing in TLA2: {len(missing_succs)}")
                        for dst in sorted(missing_succs)[:3]:
                            action = tlc_succ_map[parent_fp].get(dst)
                            action_str = f" ({action})" if action else ""
                            print(f"      -> {dst}{action_str}")

                    if extra_succs:
                        print(f"    Extra in TLA2: {len(extra_succs)}")
                        for dst in sorted(extra_succs)[:3]:
                            action = tla2_succ_map[parent_fp].get(dst)
                            action_str = f" ({action})" if action else ""
                            print(f"      -> {dst}{action_str}")
                    print()
                    break

    return 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Compare TLC DOT graph against TLA2 successor debug output"
    )
    parser.add_argument("tlc_dot", type=Path, help="TLC DOT file from -dump dot,actionlabels")
    parser.add_argument("tla2_debug", type=Path, help="TLA2 debug output file")
    parser.add_argument("-v", "--verbose", action="store_true", help="Verbose output")
    for flags, kwargs in _PROVENANCE_ARGS:
        parser.add_argument(*flags, **kwargs)
    args = parser.parse_args(argv)

    if not args.tlc_dot.exists():
        print(f"Error: TLC DOT file not found: {args.tlc_dot}", file=sys.stderr)
        return 1

    if not args.tla2_debug.exists():
        print(f"Error: TLA2 debug file not found: {args.tla2_debug}", file=sys.stderr)
        return 1

    tlc_prov_path = args.tlc_provenance or default_provenance_path(args.tlc_dot)
    tla2_prov_path = args.tla2_provenance or default_provenance_path(args.tla2_debug)

    if args.write_provenance:
        if not args.spec_path or not args.cfg_path:
            sys.stderr.write("Error: --write-provenance requires --spec-path and --cfg-path\n")
            return 1
        try:
            cfg_sha256 = args.cfg_sha256 or _read_cfg_sha256(args.cfg_path)
            provenance = ConfigProvenance(
                spec_path=args.spec_path,
                cfg_path=args.cfg_path,
                cfg_sha256=cfg_sha256,
            )
            write_config_provenance(tlc_prov_path, provenance)
            write_config_provenance(tla2_prov_path, provenance)
            LOG.info("Wrote TLC provenance: %s", tlc_prov_path)
            LOG.info("Wrote TLA2 provenance: %s", tla2_prov_path)
        except (FileNotFoundError, ValueError, OSError) as exc:
            sys.stderr.write(f"Error: failed to write provenance sidecars: {exc}\n")
            return 1

    try:
        tlc_provenance = load_config_provenance(tlc_prov_path, kind="TLC")
        tla2_provenance = load_config_provenance(tla2_prov_path, kind="TLA2")
        assert_same_config_provenance(tlc_provenance, tla2_provenance)
    except FileNotFoundError as exc:
        if args.allow_missing_provenance:
            sys.stderr.write(f"Warning: {exc}\n")
            sys.stderr.write("Warning: skipping provenance identity check\n")
        else:
            sys.stderr.write(f"Error: {exc}\n")
            return 1
    except ValueError as exc:
        sys.stderr.write(f"Error: {exc}\n")
        return 1

    print(f"Loading TLC DOT: {args.tlc_dot}")
    tlc_graph = parse_tlc_dot(args.tlc_dot)
    print(f"  Loaded {len(tlc_graph.states):,} states, {len(tlc_graph.transitions):,} transitions")
    print()

    print(f"Loading TLA2 debug: {args.tla2_debug}")
    tla2_output = parse_tla2_debug(args.tla2_debug)
    print(f"  Loaded {len(tla2_output.states):,} states, {len(tla2_output.successors):,} transitions")
    print()

    return compare_graphs(tlc_graph, tla2_output, args.verbose)


if __name__ == "__main__":
    sys.exit(main())
