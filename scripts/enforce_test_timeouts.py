#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Enforce test timeout policy: every #[test] must have #[timeout].

This script scans Rust test files and enforces the andrewdyates rule:
"Test timeouts (formula: 3-10x expected runtime)"

Usage:
    python3 scripts/enforce_test_timeouts.py          # Check all tests
    python3 scripts/enforce_test_timeouts.py --fix    # Add missing timeouts (default 10s)
    python3 scripts/enforce_test_timeouts.py --report # Generate violations report

Exit codes:
    0 - All tests have timeouts
    1 - Violations found (tests without timeouts)
    2 - Script error

The test registry (test_expectations.json) tracks expected runtimes.
Tests not in registry get default timeout; registry should be populated
with actual measured runtimes over time.
"""

import json
import re
import sys
from pathlib import Path

# Default timeout for tests not in registry (10 seconds)
# Most unit tests should complete in <1s. 10s is generous upper bound.
# Slow tests requiring more time must be in registry with explicit justification.
DEFAULT_TIMEOUT_MS = 10_000

# Multiplier for expected runtime -> timeout
TIMEOUT_MULTIPLIER = 10  # 10x expected runtime

# Paths
REPO_ROOT = Path(__file__).parent.parent
TEST_REGISTRY = REPO_ROOT / "test_expectations.json"
CRATES_DIR = REPO_ROOT / "crates"

# Patterns
TEST_ATTR_PATTERN = re.compile(r"#\[test\]")
# Code generation patterns that output #[test] as string literals
# Matches formatting macros (write!, writeln!, format!, print!, println!, eprint!, eprintln!)
# Also matches #[test] inside string literals (preceded by quote on same line)
CODEGEN_PATTERN = re.compile(r'(writeln!|write!|format!|print!|println!|eprint!|eprintln!)\s*\(.*#\[test\]|"[^"]*#\[test\]')
# Match #[timeout(N)], #[ntest::timeout(N)], and #[cfg_attr(test, ntest::timeout(N))]
# Note: \d[\d_]* handles Rust numeric literals with underscore separators (e.g., 30_000)
TIMEOUT_ATTR_PATTERN = re.compile(r"#\[(?:cfg_attr\s*\(\s*test\s*,\s*)?(?:ntest::)?timeout\s*\(\s*(\d[\d_]*)\s*\)")
FN_PATTERN = re.compile(r"fn\s+(\w+)\s*\(")
NTEST_USE_PATTERN = re.compile(r"use\s+ntest::timeout")


def load_registry() -> dict:
    """Load test expectations registry."""
    if TEST_REGISTRY.exists():
        return json.loads(TEST_REGISTRY.read_text())
    return {}


def save_registry(registry: dict) -> None:
    """Save test expectations registry."""
    TEST_REGISTRY.write_text(json.dumps(registry, indent=2, sort_keys=True) + "\n")


def get_timeout_for_test(test_name: str, registry: dict) -> int:
    """Get timeout in ms for a test based on registry or default."""
    if test_name in registry:
        expected_ms = registry[test_name].get("expected_ms", DEFAULT_TIMEOUT_MS // TIMEOUT_MULTIPLIER)
        return expected_ms * TIMEOUT_MULTIPLIER
    return DEFAULT_TIMEOUT_MS


def find_test_files() -> list[Path]:
    """Find all Rust test files."""
    test_files = []
    for crate_dir in CRATES_DIR.iterdir():
        if not crate_dir.is_dir():
            continue
        # Look in tests/ directory and src/ for inline tests
        for pattern in ["tests/**/*.rs", "src/**/*.rs"]:
            test_files.extend(crate_dir.glob(pattern))
    return test_files


def analyze_file(path: Path) -> list[dict]:
    """Analyze a file for test functions and their timeout status.

    Returns list of dicts with keys: name, line, has_timeout, timeout_ms
    """
    content = path.read_text()
    lines = content.split("\n")
    tests = []

    i = 0
    while i < len(lines):
        line = lines[i]

        # Look for #[test] attribute (skip code generation patterns)
        if TEST_ATTR_PATTERN.search(line) and not CODEGEN_PATTERN.search(line):
            # Scan backwards and forwards for #[timeout]
            has_timeout = False
            timeout_ms = None

            # Check up to 5 lines before and after for timeout
            start = max(0, i - 5)
            end = min(len(lines), i + 10)
            context = "\n".join(lines[start:end])

            timeout_match = TIMEOUT_ATTR_PATTERN.search(context)
            if timeout_match:
                has_timeout = True
                timeout_ms = int(timeout_match.group(1))

            # Find the function name
            for j in range(i, min(i + 5, len(lines))):
                fn_match = FN_PATTERN.search(lines[j])
                if fn_match:
                    test_name = fn_match.group(1)
                    tests.append({
                        "name": test_name,
                        "line": i + 1,
                        "has_timeout": has_timeout,
                        "timeout_ms": timeout_ms,
                    })
                    break
        i += 1

    return tests


def fix_file(path: Path, tests: list[dict], registry: dict) -> int:
    """Add missing timeouts to a file. Returns count of fixes.

    Uses full path #[cfg_attr(test, ntest::timeout(N))] to avoid import issues
    with inline test modules. The cfg_attr ensures it only applies in test builds
    (ntest is a dev-dependency).
    """
    content = path.read_text()
    lines = content.split("\n")
    fixes = 0

    # Add timeout attributes (process in reverse to preserve line numbers)
    for test in sorted(tests, key=lambda t: t["line"], reverse=True):
        if test["has_timeout"]:
            continue

        timeout_ms = get_timeout_for_test(test["name"], registry)
        line_idx = test["line"] - 1

        # Find the #[test] line
        for j in range(line_idx, max(0, line_idx - 5), -1):
            if "#[test]" in lines[j]:
                # Insert timeout before #[test] using cfg_attr to only apply in test builds
                indent = len(lines[j]) - len(lines[j].lstrip())
                timeout_line = " " * indent + f"#[cfg_attr(test, ntest::timeout({timeout_ms}))]"
                lines.insert(j, timeout_line)
                fixes += 1
                break

    if fixes > 0:
        path.write_text("\n".join(lines))

    return fixes


def main() -> int:
    args = sys.argv[1:]
    fix_mode = "--fix" in args
    report_mode = "--report" in args

    registry = load_registry()
    test_files = find_test_files()

    all_violations = []
    all_tests = []

    for path in test_files:
        try:
            tests = analyze_file(path)
            if not tests:
                continue

            for test in tests:
                test["file"] = str(path.relative_to(REPO_ROOT))
                all_tests.append(test)

                if not test["has_timeout"]:
                    all_violations.append(test)
        except Exception as e:
            print(f"Error analyzing {path}: {e}", file=sys.stderr)

    if report_mode:
        print(f"# Test Timeout Report")
        print(f"Total tests: {len(all_tests)}")
        print(f"With timeout: {len(all_tests) - len(all_violations)}")
        print(f"Missing timeout: {len(all_violations)}")
        print()

        if all_violations:
            print("## Violations")
            for v in all_violations:
                timeout = get_timeout_for_test(v["name"], registry)
                print(f"- {v['file']}:{v['line']} `{v['name']}` (suggested: {timeout}ms)")

        # Show registry coverage
        print()
        print("## Registry Coverage")
        registered = sum(1 for t in all_tests if t["name"] in registry)
        print(f"In registry: {registered}/{len(all_tests)}")

        return 0 if not all_violations else 1

    if fix_mode:
        total_fixes = 0
        files_fixed = set()

        # Group violations by file
        by_file = {}
        for v in all_violations:
            path = REPO_ROOT / v["file"]
            if path not in by_file:
                by_file[path] = []
            by_file[path].append(v)

        for path, tests in by_file.items():
            fixes = fix_file(path, tests, registry)
            if fixes > 0:
                total_fixes += fixes
                files_fixed.add(path)
                print(f"Fixed {fixes} test(s) in {path.relative_to(REPO_ROOT)}")

        print(f"\nTotal: {total_fixes} timeout(s) added to {len(files_fixed)} file(s)")
        return 0

    # Check mode (default)
    if all_violations:
        print(f"ERROR: {len(all_violations)} test(s) missing #[timeout]", file=sys.stderr)
        print(file=sys.stderr)
        for v in all_violations:
            timeout = get_timeout_for_test(v["name"], registry)
            print(f"  {v['file']}:{v['line']} {v['name']} (add #[timeout({timeout})])", file=sys.stderr)
        print(file=sys.stderr)
        print("Run with --fix to add default timeouts, or --report for details", file=sys.stderr)
        return 1

    print(f"OK: {len(all_tests)} test(s) all have timeouts")
    return 0


if __name__ == "__main__":
    sys.exit(main())
