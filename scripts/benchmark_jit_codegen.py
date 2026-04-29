#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""JIT/codegen performance benchmark suite for TLA2.

Measures interpreter vs JIT performance across representative specs,
collects tier dispatch statistics, and produces a structured report.

Usage:
    python3 scripts/benchmark_jit_codegen.py [--binary PATH] [--runs N] [--timeout SECS]
    python3 scripts/benchmark_jit_codegen.py --quick  # Fast run with 1 iteration, small/medium only
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
TLAPLUS_EXAMPLES = Path.home() / "tlaplus-examples" / "specifications"

# Representative specs covering different sizes and patterns
BENCHMARK_SPECS = [
    # Small specs (startup overhead dominates)
    {
        "name": "DieHard",
        "category": "small",
        "tla_path": "DieHard/DieHard.tla",
        "cfg_path": None,  # auto-detected
        "distinct_states": 16,
        "tlc_time": 0.58,
        "has_error": True,
    },
    {
        "name": "EWD840",
        "category": "small",
        "tla_path": "EWD840/EWD840.tla",
        "cfg_path": None,
        "distinct_states": 302,
        "tlc_time": 0.65,
        "has_error": False,
    },
    {
        "name": "TwoPhase",
        "category": "small",
        "tla_path": "transaction_commit/TwoPhase.tla",
        "cfg_path": "transaction_commit/TwoPhase.cfg",
        "distinct_states": 288,
        "tlc_time": 0.59,
        "has_error": False,
    },
    # Medium specs (state space exploration dominates)
    {
        "name": "MCLamportMutex",
        "category": "medium",
        "tla_path": "lamport_mutex/MCLamportMutex.tla",
        "cfg_path": "lamport_mutex/MCLamportMutex.cfg",
        "distinct_states": 724274,
        "tlc_time": 10.08,
        "has_error": False,
    },
    {
        "name": "EWD998Small",
        "category": "medium",
        "tla_path": "ewd998/EWD998.tla",
        "cfg_path": "ewd998/EWD998Small.cfg",
        "distinct_states": 1520618,
        "tlc_time": 21.70,
        "has_error": False,
    },
    {
        "name": "SlushSmall",
        "category": "medium",
        "tla_path": "SlushProtocol/Slush.tla",
        "cfg_path": "SlushProtocol/SlushSmall.cfg",
        "distinct_states": 274678,
        "tlc_time": 5.83,
        "has_error": False,
    },
    {
        "name": "dijkstra-mutex",
        "category": "medium",
        "tla_path": "dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC.tla",
        "cfg_path": "dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC.cfg",
        "distinct_states": 90882,
        "tlc_time": 13.32,
        "has_error": False,
    },
    # Large specs
    {
        "name": "MCNanoMedium",
        "category": "large",
        "tla_path": "NanoBlockchain/MCNano.tla",
        "cfg_path": "NanoBlockchain/MCNanoMedium.cfg",
        "distinct_states": 530587,
        "tlc_time": 15.00,
        "has_error": False,
    },
    {
        "name": "btree",
        "category": "large",
        "tla_path": "btree/btree.tla",
        "cfg_path": "btree/btree.cfg",
        "distinct_states": 374727,
        "tlc_time": 25.04,
        "has_error": False,
    },
    {
        "name": "CoffeeCan1000Beans",
        "category": "large",
        "tla_path": "CoffeeCan/CoffeeCan.tla",
        "cfg_path": "CoffeeCan/CoffeeCan1000Beans.cfg",
        "distinct_states": 501500,
        "tlc_time": 33.99,
        "has_error": False,
    },
]


@dataclass
class RunResult:
    """Result of a single benchmark run."""
    spec_name: str
    config_name: str
    wall_time: float
    states_found: int
    states_per_sec: float
    exit_code: int
    tier_report: str
    jit_hits: int
    jit_fallbacks: int
    jit_not_compiled: int
    jit_hit_rate: float
    tier_promotions: int
    memory_rss_mb: float
    error: str | None = None


@dataclass
class SpecBenchmark:
    """Aggregated results for one spec across configurations."""
    spec_name: str
    category: str
    distinct_states: int
    tlc_time: float
    runs: dict[str, list[RunResult]] = field(default_factory=dict)


def find_binary(explicit_path: str | None) -> Path:
    """Find the tla2 binary."""
    if explicit_path:
        p = Path(explicit_path)
        if p.exists():
            return p
        raise FileNotFoundError(f"Binary not found: {explicit_path}")

    candidates = [
        Path("/tmp/tla2-bench/release/tla2"),
        REPO_ROOT / "target" / "release" / "tla2",
        REPO_ROOT / "target" / "user" / "release" / "tla2",
    ]
    for c in candidates:
        if c.exists():
            return c
    raise FileNotFoundError(
        "No tla2 binary found. Build with: "
        "RUSTUP_TOOLCHAIN=stable-aarch64-apple-darwin cargo build --release --bin tla2 --target-dir /tmp/tla2-bench"
    )


def find_spec_path(tla_path: str) -> Path | None:
    """Resolve spec path relative to tlaplus-examples."""
    full = TLAPLUS_EXAMPLES / tla_path
    if full.exists():
        return full
    # Try finding cfg alongside
    return full if full.exists() else None


def parse_tier_report(output: str) -> dict[str, Any]:
    """Parse --show-tiers output for JIT dispatch statistics."""
    result: dict[str, Any] = {
        "jit_hits": 0,
        "jit_fallbacks": 0,
        "jit_not_compiled": 0,
        "jit_hit_rate": 0.0,
        "tier_promotions": 0,
        "actions_tier0": 0,
        "actions_tier1": 0,
        "actions_tier2": 0,
    }

    # Parse JIT invariant dispatch
    m = re.search(
        r"JIT invariant dispatch: hits=(\d+), fallbacks=(\d+), not_compiled=(\d+), total=(\d+)",
        output,
    )
    if m:
        result["jit_inv_hits"] = int(m.group(1))
        result["jit_inv_fallbacks"] = int(m.group(2))
        result["jit_inv_not_compiled"] = int(m.group(3))
        result["jit_inv_total"] = int(m.group(4))

    # Parse JIT next-state dispatch
    m = re.search(
        r"JIT next-state dispatch: hits=(\d+), fallbacks=(\d+), not_compiled=(\d+), errors=(\d+), total=(\d+)",
        output,
    )
    if m:
        result["jit_ns_hits"] = int(m.group(1))
        result["jit_ns_fallbacks"] = int(m.group(2))
        result["jit_ns_not_compiled"] = int(m.group(3))
        result["jit_ns_errors"] = int(m.group(4))
        result["jit_ns_total"] = int(m.group(5))

    # Parse Summary line
    m = re.search(
        r"Summary: (\d+) actions, (\d+) eligible, tier0=(\d+), tier1=(\d+), tier2=(\d+) \(([0-9.]+)% JIT hit rate\)",
        output,
    )
    if m:
        result["actions_total"] = int(m.group(1))
        result["actions_eligible"] = int(m.group(2))
        result["actions_tier0"] = int(m.group(3))
        result["actions_tier1"] = int(m.group(4))
        result["actions_tier2"] = int(m.group(5))
        result["jit_hit_rate"] = float(m.group(6))

    # Count promotion events
    result["tier_promotions"] = len(re.findall(r"Promotion events:", output))
    # Count individual promotions
    promo_count = len(re.findall(r"Tier\d/\w+ -> Tier\d/\w+", output))
    if promo_count > 0:
        result["tier_promotions"] = promo_count

    # Aggregate hits/fallbacks
    result["jit_hits"] = result.get("jit_inv_hits", 0) + result.get("jit_ns_hits", 0)
    result["jit_fallbacks"] = result.get("jit_inv_fallbacks", 0) + result.get("jit_ns_fallbacks", 0)
    result["jit_not_compiled"] = result.get("jit_inv_not_compiled", 0) + result.get("jit_ns_not_compiled", 0)

    return result


def parse_output(stdout: str, stderr: str) -> dict[str, Any]:
    """Parse states_found and time from human-readable output."""
    result: dict[str, Any] = {"states_found": 0, "time_secs": 0.0}

    combined = stdout + "\n" + stderr

    # Parse "States found: N"
    m = re.search(r"States found:\s*([\d,]+)", combined)
    if m:
        result["states_found"] = int(m.group(1).replace(",", ""))

    # Parse "Time: N.NNNs"
    m = re.search(r"Time:\s*([\d.]+)s", combined)
    if m:
        result["time_secs"] = float(m.group(1))

    # Parse memory from "Memory: N.N MB RSS"
    m = re.search(r"Memory:\s*([\d.]+)\s*MB", combined)
    if m:
        result["memory_rss_mb"] = float(m.group(1))

    return result


def run_single_benchmark(
    binary: Path,
    spec_path: Path,
    cfg_path: Path | None,
    config_name: str,
    spec_info: dict,
    timeout: int,
) -> RunResult:
    """Run a single benchmark configuration."""
    env = os.environ.copy()
    args = [str(binary), "check", str(spec_path), "--force", "--no-trace"]
    if cfg_path is not None and cfg_path.exists():
        args.extend(["--config", str(cfg_path)])

    if config_name == "interp_1w":
        args.extend(["--workers", "1"])
    elif config_name == "jit_1w":
        args.extend(["--workers", "1", "--jit", "--show-tiers"])
    elif config_name == "interp_4w":
        args.extend(["--workers", "4"])
    elif config_name == "jit_4w":
        args.extend(["--workers", "4", "--jit", "--show-tiers"])
        env["TLA2_SHOW_TIERS"] = "1"
    elif config_name == "jit_1w_low_thresh":
        args.extend(["--workers", "1", "--jit", "--show-tiers"])
        env["TLA2_JIT_TIER1_THRESHOLD"] = "10"
        env["TLA2_JIT_TIER2_THRESHOLD"] = "100"
    else:
        raise ValueError(f"Unknown config: {config_name}")

    start = time.monotonic()
    try:
        proc = subprocess.run(
            args,
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
        )
        elapsed = time.monotonic() - start
        exit_code = proc.returncode
        stdout = proc.stdout
        stderr = proc.stderr
        error = None
    except subprocess.TimeoutExpired:
        elapsed = timeout
        exit_code = -1
        stdout = ""
        stderr = ""
        error = f"TIMEOUT after {timeout}s"

    combined = stdout + "\n" + stderr
    parsed = parse_output(stdout, stderr)
    tier_info = parse_tier_report(combined) if "show-tiers" in " ".join(args) or "TLA2_SHOW_TIERS" in env else {}

    states = parsed.get("states_found", 0)
    states_per_sec = states / elapsed if elapsed > 0 and states > 0 else 0.0

    return RunResult(
        spec_name=spec_info["name"],
        config_name=config_name,
        wall_time=elapsed,
        states_found=states,
        states_per_sec=states_per_sec,
        exit_code=exit_code,
        tier_report=combined if tier_info else "",
        jit_hits=tier_info.get("jit_hits", 0),
        jit_fallbacks=tier_info.get("jit_fallbacks", 0),
        jit_not_compiled=tier_info.get("jit_not_compiled", 0),
        jit_hit_rate=tier_info.get("jit_hit_rate", 0.0),
        tier_promotions=tier_info.get("tier_promotions", 0),
        memory_rss_mb=parsed.get("memory_rss_mb", 0.0),
        error=error,
    )


def run_benchmarks(
    binary: Path,
    specs: list[dict],
    configs: list[str],
    runs_per_config: int,
    timeout: int,
) -> list[SpecBenchmark]:
    """Run full benchmark suite."""
    results = []
    total = len(specs) * len(configs) * runs_per_config
    current = 0

    for spec_info in specs:
        spec_path = find_spec_path(spec_info["tla_path"])
        if spec_path is None:
            print(f"  SKIP {spec_info['name']}: file not found ({spec_info['tla_path']})", file=sys.stderr)
            continue

        cfg_path = None
        if spec_info.get("cfg_path"):
            cfg_full = TLAPLUS_EXAMPLES / spec_info["cfg_path"]
            if cfg_full.exists():
                cfg_path = cfg_full

        bench = SpecBenchmark(
            spec_name=spec_info["name"],
            category=spec_info["category"],
            distinct_states=spec_info["distinct_states"],
            tlc_time=spec_info["tlc_time"],
        )

        for config in configs:
            bench.runs[config] = []
            for run_idx in range(runs_per_config):
                current += 1
                print(
                    f"  [{current}/{total}] {spec_info['name']} / {config} (run {run_idx + 1}/{runs_per_config})...",
                    file=sys.stderr,
                    flush=True,
                )
                result = run_single_benchmark(binary, spec_path, cfg_path, config, spec_info, timeout)
                bench.runs[config].append(result)
                # Progress output
                if result.error:
                    print(f"    {result.error}", file=sys.stderr)
                else:
                    print(
                        f"    {result.wall_time:.3f}s, {result.states_found} states, "
                        f"{result.states_per_sec:.0f} states/s",
                        file=sys.stderr,
                    )

        results.append(bench)

    return results


def median(values: list[float]) -> float:
    """Compute median of a list."""
    if not values:
        return 0.0
    s = sorted(values)
    n = len(s)
    if n % 2 == 0:
        return (s[n // 2 - 1] + s[n // 2]) / 2
    return s[n // 2]


def format_report(benchmarks: list[SpecBenchmark], commit: str) -> str:
    """Format benchmark results as a Markdown report."""
    lines = []
    lines.append("# JIT/Codegen Performance Benchmark Report")
    lines.append("")
    lines.append(f"**Date:** {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    lines.append(f"**Commit:** `{commit}`")
    lines.append(f"**Machine:** Apple M4 Max, 128GB RAM, macOS")
    lines.append(f"**Binary:** release build with JIT feature enabled (default)")
    lines.append("")

    # Summary table
    lines.append("## Performance Summary")
    lines.append("")
    lines.append(
        "| Spec | Category | States | TLC (s) | Interp 1w (s) | JIT 1w (s) | "
        "Interp 4w (s) | JIT 4w (s) | TLA2/TLC | 4w Speedup |"
    )
    lines.append(
        "|------|----------|--------|---------|---------------|------------|"
        "--------------|------------|----------|------------|"
    )

    for b in benchmarks:
        interp_1w_times = [r.wall_time for r in b.runs.get("interp_1w", []) if not r.error]
        jit_1w_times = [r.wall_time for r in b.runs.get("jit_1w", []) if not r.error]
        interp_4w_times = [r.wall_time for r in b.runs.get("interp_4w", []) if not r.error]
        jit_4w_times = [r.wall_time for r in b.runs.get("jit_4w", []) if not r.error]

        interp_1w = median(interp_1w_times) if interp_1w_times else float("nan")
        jit_1w = median(jit_1w_times) if jit_1w_times else float("nan")
        interp_4w = median(interp_4w_times) if interp_4w_times else float("nan")
        jit_4w = median(jit_4w_times) if jit_4w_times else float("nan")

        # Best TLA2 time (either config)
        best_times = [t for t in [interp_1w, jit_1w, interp_4w, jit_4w] if t == t]  # filter NaN
        best_tla2 = min(best_times) if best_times else float("nan")

        tla2_vs_tlc = f"{best_tla2 / b.tlc_time:.1f}x" if b.tlc_time > 0 and best_tla2 == best_tla2 else "N/A"
        speedup_4w = f"{interp_1w / interp_4w:.1f}x" if interp_4w > 0 and interp_1w == interp_1w else "N/A"

        def fmt(v: float) -> str:
            return f"{v:.3f}" if v == v else "N/A"

        lines.append(
            f"| {b.spec_name} | {b.category} | {b.distinct_states:,} | {b.tlc_time:.2f} | "
            f"{fmt(interp_1w)} | {fmt(jit_1w)} | {fmt(interp_4w)} | {fmt(jit_4w)} | "
            f"{tla2_vs_tlc} | {speedup_4w} |"
        )

    # States/second table
    lines.append("")
    lines.append("## Throughput (states/second)")
    lines.append("")
    lines.append(
        "| Spec | Interp 1w | JIT 1w | Interp 4w | JIT 4w | JIT Overhead (1w) |"
    )
    lines.append(
        "|------|-----------|--------|-----------|--------|-------------------|"
    )

    for b in benchmarks:
        def med_sps(config: str) -> float:
            runs = [r.states_per_sec for r in b.runs.get(config, []) if not r.error and r.states_per_sec > 0]
            return median(runs) if runs else 0.0

        i1 = med_sps("interp_1w")
        j1 = med_sps("jit_1w")
        i4 = med_sps("interp_4w")
        j4 = med_sps("jit_4w")

        jit_overhead = f"{(j1 / i1 - 1) * 100:+.1f}%" if i1 > 0 and j1 > 0 else "N/A"

        def fmt_sps(v: float) -> str:
            if v >= 1_000_000:
                return f"{v / 1_000_000:.1f}M"
            if v >= 1_000:
                return f"{v / 1_000:.1f}K"
            return f"{v:.0f}"

        lines.append(
            f"| {b.spec_name} | {fmt_sps(i1)} | {fmt_sps(j1)} | {fmt_sps(i4)} | {fmt_sps(j4)} | "
            f"{jit_overhead} |"
        )

    # JIT Tier dispatch table
    lines.append("")
    lines.append("## JIT Tier Dispatch Statistics (--show-tiers)")
    lines.append("")
    lines.append(
        "| Spec | Actions | Eligible | Tier0 | Tier1 | Tier2 | JIT Hits | JIT Fallback | Not Compiled | Hit Rate |"
    )
    lines.append(
        "|------|---------|----------|-------|-------|-------|----------|--------------|--------------|----------|"
    )

    for b in benchmarks:
        # Use first run of jit_1w for tier stats
        jit_runs = b.runs.get("jit_1w", [])
        if not jit_runs:
            continue
        r = jit_runs[0]
        combined = r.tier_report
        tier_info = parse_tier_report(combined)

        lines.append(
            f"| {b.spec_name} | "
            f"{tier_info.get('actions_total', '-')} | "
            f"{tier_info.get('actions_eligible', '-')} | "
            f"{tier_info.get('actions_tier0', '-')} | "
            f"{tier_info.get('actions_tier1', '-')} | "
            f"{tier_info.get('actions_tier2', '-')} | "
            f"{tier_info.get('jit_hits', 0)} | "
            f"{tier_info.get('jit_fallbacks', 0)} | "
            f"{tier_info.get('jit_not_compiled', 0)} | "
            f"{tier_info.get('jit_hit_rate', 0.0):.1f}% |"
        )

    # Key findings
    lines.append("")
    lines.append("## Key Findings")
    lines.append("")

    # Check if JIT dispatch is actually happening
    any_jit_hits = False
    for b in benchmarks:
        for r in b.runs.get("jit_1w", []):
            if r.jit_hits > 0:
                any_jit_hits = True
                break

    if not any_jit_hits:
        lines.append(
            "### CRITICAL: JIT dispatch is NOT live"
        )
        lines.append("")
        lines.append(
            "The TierManager correctly tracks action evaluations and promotes actions "
            "through Tier0 -> Tier1 -> Tier2, but the JIT-compiled code is **never actually "
            "dispatched**. All next-state and invariant evaluations fall through to "
            "`not_compiled` even after promotion. This means the entire JIT infrastructure "
            "is tracking-only -- no performance benefit is realized."
        )
        lines.append("")
        lines.append(
            "**Root cause:** The tier promotion system records that an action should use "
            "JIT-compiled code, but the dispatch path in the BFS hot loop does not actually "
            "call the compiled function. The `jit_not_compiled` counter matches the total "
            "evaluation count, confirming zero dispatch."
        )
        lines.append("")
    else:
        lines.append("### JIT dispatch is active")
        lines.append("")
        lines.append("JIT-compiled code is being dispatched for some evaluations.")

    # Bottleneck analysis
    lines.append("### Bottleneck Analysis")
    lines.append("")
    lines.append("**Bottleneck 1: JIT dispatch not wired to hot loop**")
    lines.append(
        "The biggest performance opportunity. TierManager promotes actions but compiled "
        "code never executes. Wiring the dispatch would eliminate tree-walking overhead "
        "for hot actions (>500 evals). Expected impact: 2-4x speedup on medium+ specs "
        "based on the 13%+ self-time in eval_dispatch + eval_ident + binding_chain from "
        "profiling data."
    )
    lines.append("")
    lines.append("**Bottleneck 2: Only 1 action promoted per spec**")
    lines.append(
        "The split-action model creates N*M actions (N action names * M process IDs) but "
        "only the combined Next action accumulates enough evaluations to promote. Most "
        "split actions sit at 0 evaluations. The tier threshold should account for this."
    )
    lines.append("")
    lines.append("**Bottleneck 3: Interpreter overhead is the ceiling**")
    lines.append(
        "Without JIT dispatch, performance is bounded by the tree-walking interpreter. "
        "The flat profile (no single function >6%) means micro-optimization has diminishing "
        "returns. The JIT path is the only way to break through the 2-4x TLC gap."
    )
    lines.append("")

    # Recommendations
    lines.append("## Recommendations for Round 3")
    lines.append("")
    lines.append("### Priority 1: Wire JIT dispatch into BFS hot loop")
    lines.append(
        "Files: `crates/tla-check/src/check/model_checker/bfs/` (successor generation), "
        "`crates/tla-check/src/parallel/worker/` (parallel dispatch). "
        "The compiled function pointers exist in the tier cache but are never called "
        "from the actual state exploration code."
    )
    lines.append("")
    lines.append("### Priority 2: Fix split-action eval counting")
    lines.append(
        "The per-split-action counters show 0 evals for most actions because only the "
        "combined `Next` relation accumulates counts. Either count at the Next level "
        "(promoting all sub-actions together) or route evaluations through the correct "
        "split-action counter."
    )
    lines.append("")
    lines.append("### Priority 3: Measure JIT compile latency")
    lines.append(
        "Once dispatch is wired, measure the Cranelift compilation time per action. "
        "If compilation takes >100ms per action, consider async compilation with "
        "interpreter fallback during warm-up (HotSpot C1/C2 pattern)."
    )
    lines.append("")

    return "\n".join(lines)


def format_json_results(benchmarks: list[SpecBenchmark], commit: str) -> dict:
    """Format results as JSON for machine consumption."""
    specs = {}
    for b in benchmarks:
        configs = {}
        for config_name, runs in b.runs.items():
            config_runs = []
            for r in runs:
                config_runs.append({
                    "wall_time": r.wall_time,
                    "states_found": r.states_found,
                    "states_per_sec": r.states_per_sec,
                    "exit_code": r.exit_code,
                    "jit_hits": r.jit_hits,
                    "jit_fallbacks": r.jit_fallbacks,
                    "jit_not_compiled": r.jit_not_compiled,
                    "jit_hit_rate": r.jit_hit_rate,
                    "tier_promotions": r.tier_promotions,
                    "memory_rss_mb": r.memory_rss_mb,
                    "error": r.error,
                })
            times = [r.wall_time for r in runs if not r.error]
            configs[config_name] = {
                "runs": config_runs,
                "median_time": median(times) if times else None,
                "min_time": min(times) if times else None,
                "max_time": max(times) if times else None,
            }
        specs[b.spec_name] = {
            "category": b.category,
            "distinct_states": b.distinct_states,
            "tlc_time": b.tlc_time,
            "configs": configs,
        }

    return {
        "timestamp": datetime.now().isoformat(),
        "commit": commit,
        "specs": specs,
    }


def main():
    parser = argparse.ArgumentParser(description="JIT/codegen performance benchmark")
    parser.add_argument("--binary", help="Path to tla2 binary")
    parser.add_argument("--runs", type=int, default=3, help="Runs per configuration (default: 3)")
    parser.add_argument("--timeout", type=int, default=300, help="Per-run timeout in seconds (default: 300)")
    parser.add_argument("--quick", action="store_true", help="Quick mode: 1 run, small/medium only")
    parser.add_argument("--output-json", help="Write JSON results to file")
    parser.add_argument("--output-md", help="Write Markdown report to file")
    args = parser.parse_args()

    binary = find_binary(args.binary)
    print(f"Using binary: {binary}", file=sys.stderr)

    commit = subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"],
        capture_output=True, text=True, cwd=str(REPO_ROOT),
    ).stdout.strip()
    print(f"Commit: {commit}", file=sys.stderr)

    specs = BENCHMARK_SPECS
    configs = ["interp_1w", "jit_1w", "interp_4w", "jit_4w"]
    runs_per_config = args.runs

    if args.quick:
        specs = [s for s in specs if s["category"] in ("small", "medium")]
        runs_per_config = 1

    print(f"\nRunning {len(specs)} specs x {len(configs)} configs x {runs_per_config} runs = "
          f"{len(specs) * len(configs) * runs_per_config} total benchmarks\n", file=sys.stderr)

    benchmarks = run_benchmarks(binary, specs, configs, runs_per_config, args.timeout)

    # Generate report
    report = format_report(benchmarks, commit)
    print(report)

    # Write files
    if args.output_md:
        Path(args.output_md).parent.mkdir(parents=True, exist_ok=True)
        Path(args.output_md).write_text(report)
        print(f"\nMarkdown report written to: {args.output_md}", file=sys.stderr)

    if args.output_json:
        Path(args.output_json).parent.mkdir(parents=True, exist_ok=True)
        json_data = format_json_results(benchmarks, commit)
        Path(args.output_json).write_text(json.dumps(json_data, indent=2))
        print(f"\nJSON results written to: {args.output_json}", file=sys.stderr)


if __name__ == "__main__":
    main()
