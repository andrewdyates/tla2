#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""
TLC Expected Results Generator

Runs TLC on all specs and caches results to expected_results.json.
This eliminates the need to run TLC during normal test execution.

Usage:
    python generate_expected_results.py                    # Run all runnable specs
    python generate_expected_results.py --spec DieHard    # Run specific spec
    python generate_expected_results.py --runs 3          # Multiple runs for stats
    python generate_expected_results.py --fast            # Fast specs only (<30s)
    python generate_expected_results.py --update          # Update existing cache
"""

import argparse
import json
import os
import platform
import re
import statistics
import subprocess
import time
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional, List, Dict, Any

# Import from conftest/spec_catalog
from spec_catalog import (
    ALL_SPECS,
    LARGE_SPECS,
    TLA2_LIMITATIONS,
    TLA2_BUGS,
    get_fast_specs,
    SpecInfo,
)


@dataclass
class RunResult:
    """Result of a single TLC run."""
    runtime_seconds: float
    timestamp: str
    load_average: List[float]
    memory_used_mb: int


@dataclass
class RuntimeStats:
    """Statistics from multiple TLC runs."""
    min_seconds: float
    max_seconds: float
    mean_seconds: float
    median_seconds: float
    stddev_seconds: float
    runs_count: int


@dataclass
class SpecResult:
    """Complete result for a spec."""
    states: int
    distinct_states: int
    has_error: bool
    error_type: Optional[str]
    runs: List[RunResult]
    runtime_stats: RuntimeStats
    skip_reason: Optional[str] = None


def get_tlc_version() -> str:
    """Get TLC version string."""
    tlc_jar = Path.home() / "tlaplus" / "tla2tools.jar"
    if not tlc_jar.exists():
        return "unknown"
    try:
        result = subprocess.run(
            ["java", "-jar", str(tlc_jar), "-version"],
            capture_output=True,
            text=True,
            timeout=10
        )
        # Parse "TLC2 Version X.Y.Z ..."
        output = result.stdout + result.stderr
        match = re.search(r'TLC2?\s+[Vv]ersion\s+(\d+\.\d+\.\d+)', output)
        if match:
            return match.group(1)
        # Try another pattern
        match = re.search(r'(\d+\.\d+\.\d+)', output)
        if match:
            return match.group(1)
        return output.strip()[:50] or "unknown"
    except Exception:
        return "unknown"


def get_java_version() -> str:
    """Get Java version string."""
    try:
        result = subprocess.run(
            ["java", "-version"],
            capture_output=True,
            text=True,
            timeout=10
        )
        output = result.stderr + result.stdout
        match = re.search(r'version\s+"([^"]+)"', output)
        if match:
            return match.group(1)
        return output.split('\n')[0].strip()[:50] or "unknown"
    except Exception:
        return "unknown"


def get_tlaplus_commit() -> str:
    """Get tlaplus repo commit hash."""
    tlaplus_dir = Path.home() / "tlaplus"
    if not tlaplus_dir.exists():
        return "unknown"
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True,
            text=True,
            timeout=10,
            cwd=tlaplus_dir
        )
        return result.stdout.strip() or "unknown"
    except Exception:
        return "unknown"


def get_machine_info() -> Dict[str, Any]:
    """Get machine information for reproducibility."""
    info = {
        "hostname": platform.node(),
        "cpu": platform.processor() or "unknown",
        "cores_physical": os.cpu_count() or 0,
        "cores_logical": os.cpu_count() or 0,
        "memory_gb": 0,
        "os": platform.system(),
        "os_version": platform.release(),
        "arch": platform.machine(),
    }

    # Try to get better CPU info on macOS
    if platform.system() == "Darwin":
        try:
            cpu_brand = subprocess.getoutput("sysctl -n machdep.cpu.brand_string").strip()
            if cpu_brand:
                info["cpu"] = cpu_brand
            # Physical cores
            phys = subprocess.getoutput("sysctl -n hw.physicalcpu").strip()
            if phys.isdigit():
                info["cores_physical"] = int(phys)
            # CPU frequency
            freq = subprocess.getoutput("sysctl -n hw.cpufrequency 2>/dev/null").strip()
            if freq.isdigit() and int(freq) > 0:
                info["cpu_freq_mhz"] = int(freq) // 1_000_000
        except Exception:
            pass

    # Memory
    try:
        page_size = os.sysconf('SC_PAGE_SIZE')
        pages = os.sysconf('SC_PHYS_PAGES')
        info["memory_gb"] = (page_size * pages) // (1024**3)
    except Exception:
        pass

    return info


def get_load_average() -> List[float]:
    """Get system load average."""
    try:
        return [round(x, 2) for x in os.getloadavg()]
    except Exception:
        return [0.0, 0.0, 0.0]


def get_memory_usage_mb() -> int:
    """Get current memory usage."""
    try:
        import resource
        usage = resource.getrusage(resource.RUSAGE_SELF)
        return int(usage.ru_maxrss / 1024)  # Convert to MB on macOS
    except Exception:
        return 0


def parse_tlc_output(output: str) -> tuple[int, int, bool, Optional[str]]:
    """Parse TLC output to extract state count and error info."""
    # Find the FINAL summary line
    match = re.search(
        r'^\s*([0-9,]+) states generated, ([0-9,]+) distinct states found, ([0-9,]+) states left',
        output,
        re.MULTILINE
    )
    if match:
        generated = int(match.group(1).replace(",", ""))
        distinct = int(match.group(2).replace(",", ""))
    else:
        match = re.search(r'([0-9,]+) distinct states found', output)
        distinct = int(match.group(1).replace(",", "")) if match else 0
        match = re.search(r'([0-9,]+) states generated', output)
        generated = int(match.group(1).replace(",", "")) if match else 0

    # Check for errors
    has_error = False
    error_type = None

    if re.search(r'Error:', output):
        has_error = True
        out_lower = output.lower()
        if 'cannot handle the temporal formula' in out_lower:
            error_type = 'unsupported'
        elif 'invariant' in out_lower and 'violated' in out_lower:
            error_type = 'invariant'
        elif 'deadlock' in out_lower:
            error_type = 'deadlock'
        elif 'parsing or semantic analysis failed' in out_lower:
            error_type = 'parse'
        elif 'temporal' in out_lower or 'liveness' in out_lower:
            error_type = 'liveness'
        else:
            error_type = 'unknown'

    return generated, distinct, has_error, error_type


def run_tlc_once(
    spec_path: Path,
    config_path: Path,
    timeout: int
) -> tuple[Optional[tuple[int, int, bool, Optional[str]]], float, str]:
    """Run TLC once and return (parsed_result, runtime, raw_output)."""
    tlc_jar = Path.home() / "tlaplus" / "tla2tools.jar"
    if not tlc_jar.exists():
        raise RuntimeError(f"TLC not found at {tlc_jar}")

    cmd = [
        "java", "-XX:+UseParallelGC", "-Xmx4g",
        "-jar", str(tlc_jar),
        "-workers", "1"
    ]

    if config_path.exists():
        cmd.extend(["-config", str(config_path)])
    cmd.append(str(spec_path))

    start = time.time()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=spec_path.parent
        )
        elapsed = time.time() - start
        output = result.stdout + result.stderr
        parsed = parse_tlc_output(output)
        return parsed, elapsed, output
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start
        return None, elapsed, f"Timeout after {timeout}s"


def run_tlc_multiple(
    spec: SpecInfo,
    examples_dir: Path,
    runs: int = 1,
    timeout: int = 120
) -> SpecResult:
    """Run TLC multiple times and collect statistics."""
    spec_path = examples_dir / spec.tla_path
    config_path = examples_dir / spec.cfg_path

    if not spec_path.exists():
        return SpecResult(
            states=0,
            distinct_states=0,
            has_error=False,
            error_type=None,
            runs=[],
            runtime_stats=RuntimeStats(0, 0, 0, 0, 0, 0),
            skip_reason=f"Spec not found: {spec_path}"
        )

    if not config_path.exists():
        return SpecResult(
            states=0,
            distinct_states=0,
            has_error=False,
            error_type=None,
            runs=[],
            runtime_stats=RuntimeStats(0, 0, 0, 0, 0, 0),
            skip_reason=f"Config not found: {config_path}"
        )

    # Get timeout from LARGE_SPECS if available
    spec_timeout = LARGE_SPECS.get(spec.name, timeout)

    run_results: List[RunResult] = []
    last_parsed = None
    last_output = ""

    for i in range(runs):
        if i > 0:
            time.sleep(5)  # Cool down between runs

        parsed, elapsed, output = run_tlc_once(spec_path, config_path, spec_timeout)

        if parsed is None:
            # Timeout
            return SpecResult(
                states=0,
                distinct_states=0,
                has_error=True,
                error_type="timeout",
                runs=run_results,
                runtime_stats=RuntimeStats(0, 0, 0, 0, 0, len(run_results)),
                skip_reason=f"TLC timeout after {spec_timeout}s"
            )

        last_parsed = parsed
        last_output = output

        run_results.append(RunResult(
            runtime_seconds=round(elapsed, 2),
            timestamp=datetime.now(timezone.utc).isoformat(),
            load_average=get_load_average(),
            memory_used_mb=get_memory_usage_mb()
        ))

    # Compute statistics
    times = [r.runtime_seconds for r in run_results]
    stats = RuntimeStats(
        min_seconds=round(min(times), 2),
        max_seconds=round(max(times), 2),
        mean_seconds=round(statistics.mean(times), 2),
        median_seconds=round(statistics.median(times), 2),
        stddev_seconds=round(statistics.stdev(times), 2) if len(times) > 1 else 0,
        runs_count=len(times)
    )

    generated, distinct, has_error, error_type = last_parsed

    return SpecResult(
        states=generated,
        distinct_states=distinct,
        has_error=has_error,
        error_type=error_type,
        runs=run_results,
        runtime_stats=stats
    )


def generate_expected_results(
    specs: List[SpecInfo],
    examples_dir: Path,
    runs: int = 1,
    existing: Optional[Dict] = None
) -> Dict[str, Any]:
    """Generate expected results for all specs."""
    results = {
        "_metadata": {
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "generator_version": "1.0.0",
            "tlc_version": get_tlc_version(),
            "java_version": get_java_version(),
            "tlaplus_commit": get_tlaplus_commit(),
            "machine": get_machine_info()
        },
        "specs": existing.get("specs", {}) if existing else {}
    }

    total = len(specs)
    for i, spec in enumerate(specs, 1):
        print(f"[{i}/{total}] Processing {spec.name}...", end=" ", flush=True)

        # Run TLC
        result = run_tlc_multiple(spec, examples_dir, runs=runs)

        if result.skip_reason:
            print(f"SKIPPED: {result.skip_reason}")
        elif result.has_error:
            print(f"ERROR ({result.error_type}): {result.distinct_states} states in {result.runtime_stats.mean_seconds}s")
        else:
            print(f"OK: {result.distinct_states} states in {result.runtime_stats.mean_seconds}s")

        # Convert to dict
        spec_dict = {
            "states": result.states,
            "distinct_states": result.distinct_states,
            "has_error": result.has_error,
            "error_type": result.error_type,
            "runs": [asdict(r) for r in result.runs],
            "runtime_stats": asdict(result.runtime_stats) if result.runtime_stats else {}
        }
        if result.skip_reason:
            spec_dict["skip_reason"] = result.skip_reason

        results["specs"][spec.name] = spec_dict

    return results


def main():
    parser = argparse.ArgumentParser(description="Generate TLC expected results cache")
    parser.add_argument("--spec", help="Run specific spec by name")
    parser.add_argument("--runs", type=int, default=1, help="Number of runs per spec (default: 1)")
    parser.add_argument("--fast", action="store_true", help="Fast specs only")
    parser.add_argument("--update", action="store_true", help="Update existing cache (don't overwrite all)")
    parser.add_argument("--output", default="expected_results.json", help="Output file")
    parser.add_argument("--timeout", type=int, default=120, help="Default timeout in seconds")
    args = parser.parse_args()

    # Find examples directory
    examples_dir = Path.home() / "tlaplus-examples" / "specifications"
    if not examples_dir.exists():
        print(f"ERROR: Examples directory not found: {examples_dir}")
        print("Please clone https://github.com/tlaplus/Examples to ~/tlaplus-examples")
        return 1

    # Check TLC exists
    tlc_jar = Path.home() / "tlaplus" / "tla2tools.jar"
    if not tlc_jar.exists():
        print(f"ERROR: TLC not found at {tlc_jar}")
        return 1

    # Determine which specs to run
    if args.spec:
        specs = [s for s in ALL_SPECS if s.name == args.spec]
        if not specs:
            print(f"ERROR: Spec '{args.spec}' not found")
            return 1
    elif args.fast:
        specs = get_fast_specs()
    else:
        specs = list(ALL_SPECS)  # Run all specs

    # Load existing results if updating
    output_path = Path(__file__).parent / args.output
    existing = None
    if args.update and output_path.exists():
        with open(output_path) as f:
            existing = json.load(f)
        print(f"Loaded existing results from {output_path}")

    print(f"Processing {len(specs)} specs with {args.runs} run(s) each...")
    print(f"Machine: {get_machine_info()['cpu']}")
    print(f"TLC: {get_tlc_version()}, Java: {get_java_version()}")
    print()

    results = generate_expected_results(specs, examples_dir, runs=args.runs, existing=existing)

    # Write results
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2)

    print()
    print(f"Results written to {output_path}")

    # Summary
    specs_data = results["specs"]
    total = len(specs_data)
    skipped = sum(1 for s in specs_data.values() if s.get("skip_reason"))
    errors = sum(1 for s in specs_data.values() if s.get("has_error") and not s.get("skip_reason"))
    ok = total - skipped - errors
    print(f"Summary: {ok} OK, {errors} errors, {skipped} skipped")

    return 0


if __name__ == "__main__":
    exit(main())
