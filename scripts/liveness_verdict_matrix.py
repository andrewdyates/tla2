#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Generate liveness verdict parity matrix for issue #1518.

This script discovers temporal specs from:
- TLC baseline entries (`tests/tlc_comparison/spec_baseline.json`)
- local `test_specs/` configs

Temporal discovery rule:
- `.cfg` contains `PROPERTY`, or
- `.tla` contains `WF_`/`SF_`

For each discovered spec/config pair, it runs TLC and TLA2, then compares:
- verdict class parity (`success`, `liveness`, etc.)
- state-count parity for successful runs
- trace structure parity for error runs
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import re
import subprocess
import sys
import tempfile
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from liveness_verdict_lib import (
    SpecTarget,
    TraceInfo,
    classify_tlc_status,
    classify_tla2_status,
    parse_tlc_states,
    parse_tla2_states,
    parse_trace_info,
    prepend_to_tla_path,
    resolve_test_spec_path,
    temporal_markers,
)

logger = logging.getLogger(__name__)


REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_BASELINE = REPO_ROOT / "tests" / "tlc_comparison" / "spec_baseline.json"
EXAMPLES_DIR = Path.home() / "tlaplus-examples" / "specifications"
TEST_SPECS_DIR = REPO_ROOT / "test_specs"
TLA2_BIN = REPO_ROOT / "target" / "release" / "tla"
TLA_LIBRARY = REPO_ROOT / "test_specs" / "tla_library"
TLC_JAR = Path.home() / "tlaplus" / "tla2tools.jar"
COMMUNITY_MODULES = Path.home() / "tlaplus" / "CommunityModules.jar"
DEFAULT_JSON_OUTPUT = REPO_ROOT / "reports" / "research" / "issue-1518-liveness-verdict-matrix-current.json"
DEFAULT_MD_OUTPUT = REPO_ROOT / "reports" / "research" / "issue-1518-liveness-verdict-matrix-current.md"
DEFAULT_TIMEOUT_SECONDS = 120


def discover_baseline_targets() -> list[SpecTarget]:
    if not SPEC_BASELINE.exists():
        return []

    data = json.loads(SPEC_BASELINE.read_text(encoding="utf-8"))
    specs = data.get("specs", {})
    targets: list[SpecTarget] = []
    for spec_name, payload in specs.items():
        source = payload.get("source")
        if not isinstance(source, dict):
            continue
        tla_rel = source.get("tla_path")
        cfg_rel = source.get("cfg_path")
        if not isinstance(tla_rel, str) or not isinstance(cfg_rel, str):
            continue
        spec_path = EXAMPLES_DIR / tla_rel
        cfg_path = EXAMPLES_DIR / cfg_rel
        if not spec_path.exists() or not cfg_path.exists():
            continue
        markers = temporal_markers(spec_path, cfg_path)
        if not markers:
            continue
        targets.append(
            SpecTarget(
                name=spec_name,
                source="baseline",
                spec_path=spec_path.resolve(),
                cfg_path=cfg_path.resolve(),
                temporal_markers=markers,
            )
        )
    return targets


def discover_test_targets() -> list[SpecTarget]:
    if not TEST_SPECS_DIR.exists():
        return []

    targets: list[SpecTarget] = []
    for cfg_path in sorted(TEST_SPECS_DIR.rglob("*.cfg")):
        spec_path = resolve_test_spec_path(cfg_path)
        if spec_path is None:
            continue
        markers = temporal_markers(spec_path, cfg_path)
        if not markers:
            continue
        rel_cfg = cfg_path.relative_to(REPO_ROOT)
        targets.append(
            SpecTarget(
                name=str(rel_cfg.with_suffix("")),
                source="tests",
                spec_path=spec_path.resolve(),
                cfg_path=cfg_path.resolve(),
                temporal_markers=markers,
            )
        )
    return targets


def dedupe_targets(targets: list[SpecTarget]) -> list[SpecTarget]:
    seen: set[tuple[str, str]] = set()
    unique: list[SpecTarget] = []
    for target in targets:
        key = (str(target.spec_path), str(target.cfg_path))
        if key in seen:
            continue
        seen.add(key)
        unique.append(target)
    unique.sort(key=lambda item: (item.source, item.name))
    return unique


def run_command(
    args: list[str],
    *,
    timeout_seconds: int,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> tuple[int, str, float]:
    started = time.monotonic()
    try:
        result = subprocess.run(
            args,
            cwd=str(cwd) if cwd else None,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
        elapsed = round(time.monotonic() - started, 3)
        return result.returncode, (result.stdout or "") + (result.stderr or ""), elapsed
    except subprocess.TimeoutExpired as exc:
        elapsed = round(time.monotonic() - started, 3)
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="replace")
        timeout_note = f"\n[TIMEOUT] after {timeout_seconds}s: {' '.join(args)}\n"
        return 124, f"{stdout}{stderr}{timeout_note}", elapsed


def build_env_for_spec(spec_path: Path) -> dict[str, str]:
    env = os.environ.copy()
    prepend_to_tla_path(env, TLA_LIBRARY)
    prepend_to_tla_path(env, spec_path.parent)
    return env


def run_tlc(target: SpecTarget, timeout_seconds: int) -> dict[str, Any]:
    classpath = str(TLC_JAR)
    if COMMUNITY_MODULES.exists():
        classpath = f"{classpath}{os.pathsep}{COMMUNITY_MODULES}"

    metadir_root = REPO_ROOT / "target" / "tlc_metadir"
    metadir_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=metadir_root) as metadir:
        args = [
            "java",
            f"-DTLA-Library={TLA_LIBRARY}",
            "-cp",
            classpath,
            "tlc2.TLC",
            "-metadir",
            metadir,
            "-workers",
            "1",
            "-config",
            str(target.cfg_path),
            str(target.spec_path),
        ]
        return_code, output, elapsed = run_command(
            args,
            timeout_seconds=timeout_seconds,
            cwd=target.spec_path.parent,
            env=build_env_for_spec(target.spec_path),
        )

    return {
        "cmd": " ".join(args),
        "rc": return_code,
        "elapsed_seconds": elapsed,
        "status": classify_tlc_status(output, return_code),
        "states": parse_tlc_states(output),
        "trace": parse_trace_info(output, "tlc"),
        "output": output,
    }


def run_tla2(target: SpecTarget, timeout_seconds: int) -> dict[str, Any]:
    args = [
        str(TLA2_BIN),
        "check",
        str(target.spec_path),
        "--config",
        str(target.cfg_path),
        "--workers",
        "1",
    ]
    return_code, output, elapsed = run_command(
        args,
        timeout_seconds=timeout_seconds,
        cwd=REPO_ROOT,
        env=build_env_for_spec(target.spec_path),
    )
    return {
        "cmd": " ".join(args),
        "rc": return_code,
        "elapsed_seconds": elapsed,
        "status": classify_tla2_status(output, return_code),
        "states": parse_tla2_states(output),
        "trace": parse_trace_info(output, "tla2"),
        "output": output,
    }


def build_record(target: SpecTarget, tlc: dict[str, Any], tla2: dict[str, Any]) -> dict[str, Any]:
    tlc_trace: TraceInfo = tlc["trace"]
    tla2_trace: TraceInfo = tla2["trace"]
    verdict_match = tlc["status"] == tla2["status"]
    state_match = None
    if tlc["status"] == "success" and tla2["status"] == "success":
        if tlc["states"] is not None and tla2["states"] is not None:
            state_match = tlc["states"] == tla2["states"]
        else:
            state_match = False

    trace_structure_match = None
    if tlc["status"] != "success" and tla2["status"] != "success":
        if tlc_trace.state_count > 0 or tla2_trace.state_count > 0:
            trace_structure_match = (
                tlc_trace.state_count == tla2_trace.state_count
                and tlc_trace.has_stuttering == tla2_trace.has_stuttering
            )

    overall_match = False
    if tlc["status"] == "success" and tla2["status"] == "success":
        overall_match = state_match is True
    elif tlc["status"] == "liveness" and tla2["status"] == "liveness":
        overall_match = trace_structure_match is not False

    return {
        "name": target.name,
        "source": target.source,
        "spec": str(target.spec_path),
        "config": str(target.cfg_path),
        "temporal_markers": list(target.temporal_markers),
        "tlc_cmd": tlc["cmd"],
        "tla2_cmd": tla2["cmd"],
        "tlc_rc": tlc["rc"],
        "tla2_rc": tla2["rc"],
        "tlc_status": tlc["status"],
        "tla2_status": tla2["status"],
        "tlc_states": tlc["states"],
        "tla2_states": tla2["states"],
        "verdict_match": verdict_match,
        "state_match": state_match,
        "trace_structure_match": trace_structure_match,
        "tlc_trace_states": tlc_trace.state_count,
        "tla2_trace_states": tla2_trace.state_count,
        "tlc_trace_stuttering": tlc_trace.has_stuttering,
        "tla2_trace_stuttering": tla2_trace.has_stuttering,
        "tlc_trace_signature": tlc_trace.signature,
        "tla2_trace_signature": tla2_trace.signature,
        "overall_match": overall_match,
        "tlc_elapsed_seconds": tlc["elapsed_seconds"],
        "tla2_elapsed_seconds": tla2["elapsed_seconds"],
    }


def render_markdown(records: list[dict[str, Any]], generated_at: str, summary: dict[str, Any]) -> str:
    lines = [
        "# Issue #1518 Liveness Verdict Matrix",
        "",
        f"- Generated at: `{generated_at}`",
        f"- Temporal specs discovered: `{summary['total_specs']}`",
        f"- Baseline temporal specs: `{summary['baseline_specs']}`",
        f"- Test-spec temporal specs: `{summary['test_specs']}`",
        f"- Overall parity matches: `{summary['overall_match_count']}/{summary['total_specs']}`",
        f"- Verdict mismatches: `{summary['verdict_mismatch_count']}`",
        "",
        "## Matrix",
        "",
        "| Name | Source | Markers | TLC | TLA2 | States (TLC/TLA2) | Trace states (TLC/TLA2) | Overall |",
        "|---|---|---|---:|---:|---:|---:|---:|",
    ]

    for record in records:
        markers = ",".join(record["temporal_markers"])
        states = f"{record['tlc_states']}/{record['tla2_states']}"
        trace_states = f"{record['tlc_trace_states']}/{record['tla2_trace_states']}"
        overall = "yes" if record["overall_match"] else "NO"
        lines.append(
            f"| {record['name']} | {record['source']} | {markers} | {record['tlc_status']} | "
            f"{record['tla2_status']} | {states} | {trace_states} | {overall} |"
        )

    lines.extend(
        [
            "",
            "## Notes",
            "",
            "- `overall=yes` means: success runs matched state counts, or liveness violations matched trace structure.",
            "- Trace structure comparison uses state-count parity and stuttering-marker parity when both tools report errors.",
            "",
        ]
    )
    return "\n".join(lines)


def summarize_records(records: list[dict[str, Any]], targets: list[SpecTarget]) -> dict[str, Any]:
    baseline_specs = len([target for target in targets if target.source == "baseline"])
    test_specs = len([target for target in targets if target.source == "tests"])
    overall_match_count = len([record for record in records if record["overall_match"]])
    verdict_mismatch_count = len([record for record in records if not record["verdict_match"]])
    return {
        "total_specs": len(targets),
        "baseline_specs": baseline_specs,
        "test_specs": test_specs,
        "overall_match_count": overall_match_count,
        "verdict_mismatch_count": verdict_mismatch_count,
    }


def ensure_prerequisites() -> None:
    missing: list[str] = []
    if not TLA2_BIN.exists():
        missing.append(f"missing TLA2 binary: {TLA2_BIN}")
    if not TLC_JAR.exists():
        missing.append(f"missing TLC jar: {TLC_JAR}")
    if missing:
        raise RuntimeError("; ".join(missing))


def filter_targets(
    targets: list[SpecTarget],
    *,
    source: str,
    name_regex: str | None,
    limit: int | None,
) -> list[SpecTarget]:
    filtered = targets
    if source != "all":
        filtered = [target for target in filtered if target.source == source]
    if name_regex:
        matcher = re.compile(name_regex)
        filtered = [target for target in filtered if matcher.search(target.name)]
    if limit is not None:
        filtered = filtered[:limit]
    return filtered


def run_matrix(targets: list[SpecTarget], timeout_seconds: int) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for idx, target in enumerate(targets, start=1):
        logger.info("[%d/%d] %s", idx, len(targets), target.name)
        tlc = run_tlc(target, timeout_seconds)
        tla2 = run_tla2(target, timeout_seconds)
        records.append(build_record(target, tlc, tla2))
    return records


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate liveness verdict parity matrix for #1518.")
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT_SECONDS, help="Timeout per tool per spec.")
    parser.add_argument(
        "--source",
        choices=["all", "baseline", "tests"],
        default="all",
        help="Spec source filter.",
    )
    parser.add_argument("--name-regex", help="Regex filter against discovered spec names.")
    parser.add_argument("--limit", type=int, help="Limit number of discovered specs.")
    parser.add_argument("--dry-run", action="store_true", help="Only print discovered specs; do not run tools.")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_JSON_OUTPUT)
    parser.add_argument("--md-output", type=Path, default=DEFAULT_MD_OUTPUT)
    return parser.parse_args()


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s", stream=sys.stderr)
    args = parse_args()
    ensure_prerequisites()

    discovered = dedupe_targets([*discover_baseline_targets(), *discover_test_targets()])
    targets = filter_targets(discovered, source=args.source, name_regex=args.name_regex, limit=args.limit)

    if args.dry_run:
        for target in targets:
            markers = ",".join(target.temporal_markers)
            sys.stdout.write(f"{target.source}\t{target.name}\t{markers}\t{target.spec_path}\t{target.cfg_path}\n")
        return 0

    records = run_matrix(targets, timeout_seconds=args.timeout)
    generated_at = datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")
    summary = summarize_records(records, targets)
    payload = {
        "generated_at": generated_at,
        "criteria": {
            "temporal_spec": "cfg has PROPERTY or spec contains WF_/SF_",
            "verdict_match": "tlc_status == tla2_status",
            "trace_structure_match": "trace state-count parity + stuttering parity when both runs are errors",
        },
        "summary": summary,
        "records": records,
    }

    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.md_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.md_output.write_text(render_markdown(records, generated_at, summary) + "\n", encoding="utf-8")
    logger.info("Wrote %s", args.json_output)
    logger.info("Wrote %s", args.md_output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
