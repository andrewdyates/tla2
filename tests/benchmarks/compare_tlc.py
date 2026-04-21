#!/usr/bin/env python3
"""
TLA2 vs TLC Benchmark Comparison Suite

Runs key specs on both TLA2 and TLC, comparing:
- Execution time
- States found
- States per second

Results are saved to JSON for historical tracking.
"""

import json
import os
import subprocess
import sys
import time
import re
from datetime import datetime
from pathlib import Path

# Configuration
TLA2_BIN = "./target/release/tla"
TLC_JAR = os.path.expanduser("~/tlaplus/tla2tools.jar")
RESULTS_DIR = Path("tests/benchmarks/results")
TEST_SPECS_DIR = Path("test_specs")

# Benchmark specs: (name, spec_path, config_path)
# Note: Some specs (MCBakery) excluded due to TLAPS dependency not supported by TLC
BENCHMARK_SPECS = [
    # Core benchmarks - safety and liveness
    ("TokenRing", "test_specs/TokenRing.tla", "test_specs/TokenRing.cfg"),
    ("SimpleCounter_large", "test_specs/SimpleCounter.tla", "test_specs/SimpleCounter_large.cfg"),
    ("SimpleCounter_perf", "test_specs/SimpleCounter.tla", "test_specs/SimpleCounter_perf.cfg"),
    ("bcastFolklore", "test_specs/bcastFolklore.tla", "test_specs/bcastFolklore_bench.cfg"),
]

def run_tla2(spec: str, config: str, timeout: int = 300) -> dict:
    """Run TLA2 model checker and extract metrics."""
    cmd = [TLA2_BIN, "check", spec, "--config", config, "--workers", "1"]
    try:
        start = time.time()
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        elapsed = time.time() - start

        output = result.stdout + result.stderr
        states = 0
        if match := re.search(r"States found: (\d+)", output):
            states = int(match.group(1))

        return {
            "success": result.returncode == 0,
            "time": round(elapsed, 3),
            "states": states,
            "states_per_sec": round(states / elapsed) if elapsed > 0 else 0,
            "error": None if result.returncode == 0 else result.stderr[:200]
        }
    except subprocess.TimeoutExpired:
        return {"success": False, "time": timeout, "states": 0, "error": "timeout"}
    except Exception as e:
        return {"success": False, "time": 0, "states": 0, "error": str(e)}

def run_tlc(spec: str, config: str, timeout: int = 300) -> dict:
    """Run TLC model checker and extract metrics."""
    cmd = ["java", "-jar", TLC_JAR, "-config", config, spec]
    try:
        start = time.time()
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        elapsed = time.time() - start

        output = result.stdout + result.stderr

        # Check for TLC-specific errors
        if "Cannot find source file for module" in output:
            return {"success": False, "time": 0, "states": 0, "error": "missing module"}
        if "Error:" in output and "Model checking completed" not in output:
            return {"success": False, "time": elapsed, "states": 0, "error": "error"}

        states = 0
        # Match final state count line: "N states generated, M distinct states found, 0 states left"
        if match := re.search(r"([\d,]+) distinct states found, 0 states left", output):
            states = int(match.group(1).replace(",", ""))

        return {
            "success": "Model checking completed" in output,
            "time": round(elapsed, 3),
            "states": states,
            "states_per_sec": round(states / elapsed) if elapsed > 0 else 0,
            "error": None
        }
    except subprocess.TimeoutExpired:
        return {"success": False, "time": timeout, "states": 0, "error": "timeout"}
    except Exception as e:
        return {"success": False, "time": 0, "states": 0, "error": str(e)}

def main():
    # Ensure TLA2 binary exists
    if not Path(TLA2_BIN).exists():
        print("Building TLA2...")
        subprocess.run(["cargo", "build", "--release", "-p", "tla-cli"], check=True)

    # Create results directory
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    results = {
        "timestamp": datetime.now().isoformat(),
        "git_commit": subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True
        ).stdout.strip(),
        "benchmarks": []
    }

    print("=" * 70)
    print("TLA2 vs TLC Benchmark Comparison")
    print("=" * 70)
    print()

    for name, spec, config in BENCHMARK_SPECS:
        print(f"Running: {name}")
        print(f"  Spec: {spec}")
        print(f"  Config: {config}")

        if not Path(spec).exists():
            print(f"  SKIP: spec not found")
            continue
        if not Path(config).exists():
            print(f"  SKIP: config not found")
            continue

        tla2_result = run_tla2(spec, config)
        tlc_result = run_tlc(spec, config)

        # Calculate ratio (TLA2/TLC, <1 means TLA2 is faster)
        if tlc_result["time"] > 0 and tla2_result["time"] > 0:
            ratio = round(tla2_result["time"] / tlc_result["time"], 2)
        else:
            ratio = None

        benchmark = {
            "name": name,
            "spec": spec,
            "config": config,
            "tla2": tla2_result,
            "tlc": tlc_result,
            "ratio": ratio,
            "within_2x": ratio is not None and ratio <= 2.0
        }
        results["benchmarks"].append(benchmark)

        print(f"  TLA2: {tla2_result['time']}s, {tla2_result['states']} states")
        print(f"  TLC:  {tlc_result['time']}s, {tlc_result['states']} states")
        if ratio:
            status = "PASS" if ratio <= 2.0 else "FAIL"
            print(f"  Ratio: {ratio}x ({status})")
        print()

    # Save results
    result_file = RESULTS_DIR / f"benchmark_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(result_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Results saved to: {result_file}")

    # Print summary table
    print()
    print("=" * 70)
    print("Summary")
    print("=" * 70)
    print(f"{'Spec':<25} {'TLA2':>10} {'TLC':>10} {'Ratio':>8} {'Status':>8}")
    print("-" * 70)
    for b in results["benchmarks"]:
        tla2_time = f"{b['tla2']['time']}s" if b['tla2']['success'] else "ERR"
        tlc_time = f"{b['tlc']['time']}s" if b['tlc']['success'] else "ERR"
        ratio_str = f"{b['ratio']}x" if b['ratio'] else "N/A"
        status = "PASS" if b.get('within_2x') else "FAIL"
        print(f"{b['name']:<25} {tla2_time:>10} {tlc_time:>10} {ratio_str:>8} {status:>8}")

    # Return exit code based on whether all benchmarks passed
    all_pass = all(b.get('within_2x', False) for b in results["benchmarks"] if b['tla2']['success'] and b['tlc']['success'])
    return 0 if all_pass else 1

if __name__ == "__main__":
    sys.exit(main())
