#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""
Compare test results between commits to identify regressions.

Usage:
    python compare_test_results.py                    # Compare last 2 runs
    python compare_test_results.py abc123 def456     # Compare specific commits
    python compare_test_results.py --baseline        # Compare against baseline
"""

import sys
import json
from pathlib import Path

HISTORY_FILE = Path(__file__).parent.parent / "tests" / "tlc_comparison" / "tla2_results_history.json"
BASELINE_FILE = Path(__file__).parent.parent / "tests" / "tlc_comparison" / "spec_baseline.json"


def load_history() -> list:
    """Load test history."""
    if not HISTORY_FILE.exists():
        print(f"No history file: {HISTORY_FILE}")
        return []
    with open(HISTORY_FILE) as f:
        return json.load(f)


def load_baseline() -> dict:
    """Load TLC baseline."""
    if not BASELINE_FILE.exists():
        print(f"No baseline file: {BASELINE_FILE}")
        return {}
    with open(BASELINE_FILE) as f:
        return json.load(f)


def find_run_by_commit(history: list, commit: str) -> dict:
    """Find a run by commit hash (prefix match)."""
    for entry in reversed(history):
        if entry.get("git", {}).get("commit", "").startswith(commit):
            return entry
        if entry.get("git", {}).get("short", "") == commit:
            return entry
    return None


def compare_runs(old: dict, new: dict, old_label: str, new_label: str):
    """Compare two runs and print differences."""
    old_results = old.get("results", {})
    new_results = new.get("results", {})

    regressions = []
    improvements = []
    new_failures = []
    new_passes = []

    all_specs = set(old_results.keys()) | set(new_results.keys())

    for name in sorted(all_specs):
        old_r = old_results.get(name, {})
        new_r = new_results.get(name, {})

        old_states = old_r.get("states") or old_r.get("expected_states")
        new_states = new_r.get("states")
        old_status = old_r.get("status", "unknown")
        new_status = new_r.get("status", "unknown")

        # State count changes
        if old_states is not None and new_states is not None:
            if old_states != new_states:
                regressions.append((name, old_states, new_states))

        # Status changes
        if old_status == "pass" and new_status != "pass":
            new_failures.append((name, old_status, new_status))
        elif old_status != "pass" and new_status == "pass":
            new_passes.append((name, old_status, new_status))

    # Print report
    print("=" * 70)
    print(f"COMPARISON: {old_label} -> {new_label}")
    print("=" * 70)
    print()

    if regressions:
        print(f"STATE COUNT REGRESSIONS ({len(regressions)}):")
        for name, old_s, new_s in regressions:
            diff = new_s - old_s
            pct = (diff / old_s * 100) if old_s else 0
            print(f"  {name}: {old_s} -> {new_s} ({diff:+d}, {pct:+.1f}%)")
        print()

    if new_failures:
        print(f"NEW FAILURES ({len(new_failures)}):")
        for name, old_s, new_s in new_failures:
            print(f"  {name}: {old_s} -> {new_s}")
        print()

    if new_passes:
        print(f"NEW PASSES ({len(new_passes)}):")
        for name, old_s, new_s in new_passes:
            print(f"  {name}: {old_s} -> {new_s}")
        print()

    if improvements:
        print(f"IMPROVEMENTS ({len(improvements)}):")
        for name, old_s, new_s in improvements:
            print(f"  {name}: {old_s} -> {new_s}")
        print()

    # Summary
    old_pass = sum(1 for r in old_results.values() if r.get("status") == "pass")
    new_pass = sum(1 for r in new_results.values() if r.get("status") == "pass")

    print("SUMMARY:")
    print(f"  {old_label}: {old_pass} passing")
    print(f"  {new_label}: {new_pass} passing")
    print(f"  Change: {new_pass - old_pass:+d}")

    if regressions:
        print(f"\n  ** {len(regressions)} STATE COUNT REGRESSIONS - INVESTIGATE **")


def main():
    args = sys.argv[1:]

    if "--baseline" in args:
        # Compare latest run against TLC baseline
        history = load_history()
        baseline = load_baseline()
        if not history:
            print("No test history to compare")
            return
        if not baseline:
            print("No baseline to compare against")
            return

        latest = history[-1]
        # Convert baseline format to match history format
        baseline_run = {
            "results": baseline.get("specs", {}),
            "git": {"short": "TLC-baseline"},
        }
        compare_runs(baseline_run, latest, "TLC-baseline", latest.get("git", {}).get("short", "latest"))

    elif len(args) == 2:
        # Compare two specific commits
        history = load_history()
        old = find_run_by_commit(history, args[0])
        new = find_run_by_commit(history, args[1])
        if not old:
            print(f"No run found for commit: {args[0]}")
            return
        if not new:
            print(f"No run found for commit: {args[1]}")
            return
        compare_runs(old, new, args[0], args[1])

    else:
        # Compare last two runs
        history = load_history()
        if len(history) < 2:
            print("Need at least 2 runs to compare")
            if history:
                print(f"Only have {len(history)} run(s)")
            return

        old = history[-2]
        new = history[-1]
        old_label = old.get("git", {}).get("short", "previous")
        new_label = new.get("git", {}).get("short", "latest")
        compare_runs(old, new, old_label, new_label)


if __name__ == "__main__":
    main()
