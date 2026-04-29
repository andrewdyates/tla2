#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Migrate spec_baseline.json from v2 to v3 schema and populate TLA2 results.

Part of P0 #568 - Fix misleading baseline status.

v3 schema namespaces TLC results and adds TLA2 results:
- tlc.status: TLC's outcome
- tlc.states: TLC state count
- tla2.status: TLA2's outcome (pass/mismatch/fail/untested)
- tla2.states: TLA2 state count
- verified_match: True only if TLA2 matches TLC
- issue: Link to tracking issue if mismatch

Usage:
    python scripts/migrate_baseline_v3.py           # Populate TLA2 results + write (default)
    python scripts/migrate_baseline_v3.py --dry-run # Show what would happen without writing
    python scripts/migrate_baseline_v3.py --skip-untested-only  # Only run on untested specs
"""

import argparse
import json
import subprocess
import sys
import os
from datetime import datetime
from pathlib import Path

BASELINE_PATH = Path(__file__).parent.parent / "tests" / "tlc_comparison" / "spec_baseline.json"
TLA2_BIN = Path(__file__).parent.parent / "target" / "release" / "tla2"
TLA_LIBRARY = Path(__file__).parent.parent / "test_specs" / "tla_library"
EXAMPLES_DIR = Path.home() / "tlaplus-examples" / "specifications"

# Add tests directory to path for spec_catalog
sys.path.insert(0, str(Path(__file__).parent.parent / "tests" / "tlc_comparison"))
from spec_catalog import ALL_SPECS

# Known issues for mismatch specs (from P0 #568 analysis)
KNOWN_ISSUES = {
    "btree": 562,
    "SimTokenRing": 563,
    "MultiPaxos_MC_small": 564,
    "EWD998ChanTrace": 565,
    "N-Queens_FourQueens": 566,
    "ACP_NB_WRONG_TLC": 567,
}


def run_tla2(spec_path: Path, cfg_path: Path, timeout: int = 60) -> tuple:
    """Run TLA2 on a spec and return (states, error_type)."""
    if not TLA2_BIN.exists():
        return None, "binary_missing"

    try:
        env = os.environ.copy()
        env["TLA_PATH"] = str(TLA_LIBRARY)
        result = subprocess.run(
            [str(TLA2_BIN), "check", str(spec_path), "--config", str(cfg_path), "--workers", "1"],
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
        )
        output = result.stdout + result.stderr

        # Parse state count
        for line in output.split("\n"):
            if "States found:" in line:
                try:
                    states = int(line.split(":")[-1].strip())
                    return states, None
                except ValueError:
                    pass

        # Check for errors
        if "error" in output.lower() or result.returncode != 0:
            if "Module" in output and "not found" in output:
                return None, "missing_module"
            if "Unsupported" in output:
                return None, "unsupported"
            if "parse" in output.lower() or "Parse" in output:
                return None, "parse"
            return None, "other"

        return None, "unknown"
    except subprocess.TimeoutExpired:
        return None, "timeout"
    except Exception as e:
        return None, f"error: {e}"


def get_spec_paths(spec_name: str) -> tuple:
    """Get (spec_path, cfg_path) for a spec name."""
    # ALL_SPECS is a list of SpecInfo namedtuples
    spec_info = None
    for s in ALL_SPECS:
        if s.name == spec_name:
            spec_info = s
            break

    if not spec_info:
        return None, None

    spec_path = EXAMPLES_DIR / spec_info.tla_path
    cfg_path = EXAMPLES_DIR / spec_info.cfg_path

    return spec_path, cfg_path


def migrate_v2_to_v3(v2_data: dict, run_tla2_flag: bool = False, verbose: bool = False) -> dict:
    """Convert v2 baseline to v3 schema."""
    v3_data = {
        "schema_version": 3,
        "generated": datetime.now().isoformat(),
        "migrated_from": {
            "schema_version": v2_data.get("schema_version", 2),
            "generated": v2_data.get("generated"),
        },
        "collector": v2_data.get("collector", {}),
        "tlc": v2_data.get("tlc", {}),
        "inputs": v2_data.get("inputs", {}),
        "seed": v2_data.get("seed", {}),
        "tlc_timeout_seconds": v2_data.get("tlc_timeout_seconds", 600),
        "total_specs": v2_data.get("total_specs", 0),
        "specs_jcs_sha256": v2_data.get("specs_jcs_sha256"),
        "stats": {
            "tlc_pass": 0,
            "tlc_error": 0,
            "tlc_timeout": 0,
            "tla2_match": 0,
            "tla2_mismatch": 0,
            "tla2_fail": 0,
            "tla2_untested": 0,
        },
        "categories": v2_data.get("categories", {}),
        "specs": {},
    }

    git_commit = None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        if result.returncode == 0:
            git_commit = result.stdout.strip()
    except Exception:
        pass

    today = datetime.now().strftime("%Y-%m-%d")

    for spec_name, v2_spec in v2_data.get("specs", {}).items():
        # Namespace TLC results
        tlc_data = {
            "status": v2_spec.get("status"),
            "states": v2_spec.get("expected_states"),
            "runtime_seconds": v2_spec.get("tlc_runtime_seconds"),
            "error_type": v2_spec.get("error_type"),
        }

        # TLA2 results - initially mark as untested
        tla2_status = "untested"
        tla2_states = None
        tla2_error_type = None

        if run_tla2_flag:
            spec_path, cfg_path = get_spec_paths(spec_name)
            if spec_path and cfg_path and spec_path.exists() and cfg_path.exists():
                if verbose:
                    print(f"Running TLA2 on {spec_name}...", file=sys.stderr)
                tla2_states, tla2_error_type = run_tla2(spec_path, cfg_path)

                if tla2_states is not None:
                    tlc_states = tlc_data.get("states")
                    if tlc_states is not None and tla2_states == tlc_states:
                        tla2_status = "pass"
                    elif tlc_states is not None:
                        tla2_status = "mismatch"
                    else:
                        tla2_status = "pass"  # No TLC baseline to compare
                elif tla2_error_type:
                    tla2_status = "fail"
            else:
                tla2_status = "untested"
                if verbose and spec_path:
                    print(f"Skipping {spec_name}: files not found", file=sys.stderr)

        tla2_data = {
            "status": tla2_status,
            "states": tla2_states,
            "error_type": tla2_error_type,
            "last_run": today if run_tla2_flag else None,
            "git_commit": git_commit if run_tla2_flag else None,
        }

        # Compute verified_match
        verified_match = (
            tla2_status == "pass"
            and tla2_states is not None
            and tlc_data.get("states") is not None
            and tla2_states == tlc_data.get("states")
        )

        # Link to known issue if mismatch
        issue = KNOWN_ISSUES.get(spec_name)

        v3_spec = {
            "tlc": tlc_data,
            "tla2": tla2_data,
            "verified_match": verified_match,
            "category": v2_spec.get("category"),
        }

        if issue:
            v3_spec["issue"] = issue

        v3_data["specs"][spec_name] = v3_spec

        # Update stats
        tlc_status = tlc_data.get("status")
        if tlc_status == "pass":
            v3_data["stats"]["tlc_pass"] += 1
        elif tlc_status == "error":
            v3_data["stats"]["tlc_error"] += 1
        elif tlc_status == "timeout":
            v3_data["stats"]["tlc_timeout"] += 1

        if tla2_status == "pass" and verified_match:
            v3_data["stats"]["tla2_match"] += 1
        elif tla2_status == "mismatch":
            v3_data["stats"]["tla2_mismatch"] += 1
        elif tla2_status == "fail":
            v3_data["stats"]["tla2_fail"] += 1
        else:
            v3_data["stats"]["tla2_untested"] += 1

    return v3_data


def update_v3_with_tla2_results(v3_data: dict, verbose: bool = False, untested_only: bool = False) -> dict:
    """Update existing v3 baseline with TLA2 results."""
    git_commit = None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        if result.returncode == 0:
            git_commit = result.stdout.strip()
    except Exception:
        pass

    today = datetime.now().strftime("%Y-%m-%d")

    # Reset stats
    v3_data["stats"] = {
        "tlc_pass": 0,
        "tlc_error": 0,
        "tlc_timeout": 0,
        "tla2_match": 0,
        "tla2_mismatch": 0,
        "tla2_fail": 0,
        "tla2_untested": 0,
    }

    total = len(v3_data.get("specs", {}))
    for i, (spec_name, spec_data) in enumerate(v3_data.get("specs", {}).items(), 1):
        tla2_data = spec_data.get("tla2", {})
        tlc_data = spec_data.get("tlc", {})

        # Skip if untested_only and already has results
        if untested_only and tla2_data.get("status") != "untested" and tla2_data.get("states") is not None:
            # Just update stats
            pass
        else:
            # Run TLA2 on this spec
            spec_path, cfg_path = get_spec_paths(spec_name)
            if spec_path and cfg_path and spec_path.exists() and cfg_path.exists():
                if verbose:
                    print(f"[{i}/{total}] Running TLA2 on {spec_name}...", file=sys.stderr)
                tla2_states, tla2_error_type = run_tla2(spec_path, cfg_path)

                if tla2_states is not None:
                    tlc_states = tlc_data.get("states")
                    if tlc_states is not None and tla2_states == tlc_states:
                        tla2_status = "pass"
                    elif tlc_states is not None:
                        tla2_status = "mismatch"
                    else:
                        tla2_status = "pass"
                elif tla2_error_type:
                    tla2_status = "fail"
                    tla2_states = None
                else:
                    tla2_status = "fail"
                    tla2_states = None

                tla2_data = {
                    "status": tla2_status,
                    "states": tla2_states,
                    "error_type": tla2_error_type,
                    "last_run": today,
                    "git_commit": git_commit,
                }
                spec_data["tla2"] = tla2_data
            else:
                if verbose:
                    print(f"[{i}/{total}] Skipping {spec_name}: files not found", file=sys.stderr)

        # Compute verified_match
        tla2_states = tla2_data.get("states")
        tlc_states = tlc_data.get("states")
        verified_match = (
            tla2_data.get("status") == "pass"
            and tla2_states is not None
            and tlc_states is not None
            and tla2_states == tlc_states
        )
        spec_data["verified_match"] = verified_match

        # Update stats
        tlc_status = tlc_data.get("status")
        if tlc_status == "pass":
            v3_data["stats"]["tlc_pass"] += 1
        elif tlc_status == "error":
            v3_data["stats"]["tlc_error"] += 1
        elif tlc_status == "timeout":
            v3_data["stats"]["tlc_timeout"] += 1

        tla2_status = tla2_data.get("status")
        if tla2_status == "pass" and verified_match:
            v3_data["stats"]["tla2_match"] += 1
        elif tla2_status == "mismatch":
            v3_data["stats"]["tla2_mismatch"] += 1
        elif tla2_status == "fail":
            v3_data["stats"]["tla2_fail"] += 1
        else:
            v3_data["stats"]["tla2_untested"] += 1

    v3_data["generated"] = datetime.now().isoformat()
    return v3_data


def main():
    parser = argparse.ArgumentParser(description="Populate TLA2 results in spec_baseline.json")
    parser.add_argument("--dry-run", action="store_true", help="Show results without writing")
    parser.add_argument("--untested-only", action="store_true", help="Only run on specs with status=untested")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--output", "-o", help="Output file (default: overwrite baseline)")
    # Legacy flags for compatibility
    parser.add_argument("--write", action="store_true", help="(deprecated, now default)")
    parser.add_argument("--run-tla2", action="store_true", help="(deprecated, now default)")
    args = parser.parse_args()

    if not BASELINE_PATH.exists():
        print(f"Error: Baseline not found: {BASELINE_PATH}", file=sys.stderr)
        sys.exit(1)

    with open(BASELINE_PATH) as f:
        data = json.load(f)

    # If v2, migrate first
    if data.get("schema_version", 0) < 3:
        print("Migrating v2 → v3...", file=sys.stderr)
        data = migrate_v2_to_v3(data, run_tla2_flag=False, verbose=args.verbose)

    # Always populate TLA2 results
    print("Populating TLA2 results...", file=sys.stderr)
    data = update_v3_with_tla2_results(data, verbose=args.verbose, untested_only=args.untested_only)

    output_path = Path(args.output) if args.output else BASELINE_PATH

    if not args.dry_run:
        with open(output_path, "w") as f:
            json.dump(data, f, indent=2)
        print(f"Wrote baseline to {output_path}")

    # Print summary
    stats = data["stats"]
    print(f"\nSummary:", file=sys.stderr)
    print(f"  TLC: {stats['tlc_pass']} pass, {stats['tlc_error']} error, {stats['tlc_timeout']} timeout", file=sys.stderr)
    print(f"  TLA2: {stats['tla2_match']} match, {stats['tla2_mismatch']} mismatch, {stats['tla2_fail']} fail, {stats['tla2_untested']} untested", file=sys.stderr)

    coverage = stats['tla2_match'] / (stats['tla2_match'] + stats['tla2_mismatch'] + stats['tla2_fail'] + stats['tla2_untested']) * 100 if (stats['tla2_match'] + stats['tla2_mismatch'] + stats['tla2_fail'] + stats['tla2_untested']) > 0 else 0
    print(f"  Coverage: {coverage:.1f}%", file=sys.stderr)


if __name__ == "__main__":
    main()
