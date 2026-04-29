#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Static guard: detect silent error coercion in model checker production code.

Part of #1433 (Step 5): prevents new error-swallowing sites from being
introduced in checker/enumerate/liveness paths without using the approved
error_policy.rs API.

Banned patterns in production modules:
  - `if let Ok(...) = eval_entry(` — direct eval with silent error dropping
  - `if let Ok(...) = eval(` — same pattern, short form
  - `eval_entry(...).ok()` — silently converting eval error to None
  - `eval_entry(...).unwrap_or(` — silently converting eval error to default
  - `Err(_) => continue` near eval calls — catch-all error ignoring
  - `.unwrap_or(false)` near eval calls — silent boolean coercion

Approved alternatives (from error_policy.rs):
  - eval_required() — fatal on any error
  - eval_bool_required() — fatal on error or non-boolean
  - eval_speculative() — fallback only for named FallbackClass variants
  - eval_bool_speculative() — same, boolean variant

Lines with `Part of #1433:` annotation are exempt (already audited).
Lines in doc comments (`///` or `//!`) and string literals are exempt.
Test files and test modules are exempt.

Exit code: number of violations found (0 = clean).
"""

import logging
import re
import sys
from pathlib import Path

log = logging.getLogger(__name__)

# Production source directories to scan
SCAN_PATHS = [
    "crates/tla-check/src/check",
    "crates/tla-check/src/enumerate",
    "crates/tla-check/src/liveness",
    "crates/tla-check/src/parallel",
    "crates/tla-check/src/compiled_guard",
    "crates/tla-check/src/adaptive.rs",
    "crates/tla-check/src/error_policy.rs",
]

# Patterns that indicate silent error coercion on eval results.
# Each entry: (compiled_regex, description)
BANNED_PATTERNS = [
    (
        re.compile(r'if\s+let\s+Ok\(.+\)\s*=\s*(?:eval_entry|eval\s*\(|crate::eval::eval)'),
        "if let Ok(...) = eval — use eval_required() or eval_speculative()",
    ),
    (
        re.compile(r'eval_entry\s*\([^)]*\)\s*\.ok\(\)'),
        "eval_entry().ok() — use eval_speculative() with explicit FallbackClass",
    ),
    (
        re.compile(r'eval_entry\s*\([^)]*\)\s*\.unwrap_or\b'),
        "eval_entry().unwrap_or() — use eval_speculative() with explicit FallbackClass",
    ),
    (
        re.compile(r'eval_entry\s*\([^)]*\)\s*\.unwrap_or_default\b'),
        "eval_entry().unwrap_or_default() — use eval_speculative()",
    ),
]

# Exemption markers — lines containing these are already audited
EXEMPTION_MARKERS = [
    "Part of #1433",
    "error_policy",
    "eval_required",
    "eval_speculative",
    "eval_bool_required",
    "eval_bool_speculative",
]


def is_test_file(path: Path) -> bool:
    """Returns True for test files that are exempt from the guard."""
    name = path.name
    return (
        name.endswith("_tests.rs")
        or name == "tests.rs"
        or "tests/" in str(path)
        or "/tests" in str(path)
        or name.startswith("test_")
    )


def is_exempt_line(line: str) -> bool:
    """Returns True if the line is exempt from checking."""
    stripped = line.strip()
    # Doc comments and module-level comments
    if stripped.startswith("///") or stripped.startswith("//!"):
        return True
    # Lines already audited
    for marker in EXEMPTION_MARKERS:
        if marker in line:
            return True
    # String literals (inside quotes) — crude check for doc examples
    if stripped.startswith('"') or stripped.startswith("r#"):
        return True
    # Comment-only lines with the pattern in documentation
    if stripped.startswith("//") and "```" not in stripped:
        return True
    return False


def scan_file(path: Path) -> list[tuple[int, str, str]]:
    """Scan a single file for banned patterns.

    Returns list of (line_number, line_content, violation_description).
    """
    violations = []
    try:
        content = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return violations

    lines = content.split("\n")

    # Track if we're inside a #[cfg(test)] module
    in_test_module = False
    brace_depth = 0

    for i, line in enumerate(lines, start=1):
        # Crude test module detection
        if "#[cfg(test)]" in line:
            in_test_module = True
            brace_depth = 0
        if in_test_module:
            brace_depth += line.count("{") - line.count("}")
            if brace_depth < 0:
                in_test_module = False
                brace_depth = 0
            continue

        if is_exempt_line(line):
            continue

        # Check context: is the previous or next line an exemption?
        prev_line = lines[i - 2] if i >= 2 else ""
        next_line = lines[i] if i < len(lines) else ""
        if any(m in prev_line for m in EXEMPTION_MARKERS) or any(
            m in next_line for m in EXEMPTION_MARKERS
        ):
            continue

        for pattern, description in BANNED_PATTERNS:
            if pattern.search(line):
                violations.append((i, line.rstrip(), description))
                break  # One violation per line

    return violations


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s")

    root = Path(".")
    total_violations = 0
    all_violations: dict[str, list[tuple[int, str, str]]] = {}

    for scan_path in SCAN_PATHS:
        p = root / scan_path
        if p.is_file():
            files = [p]
        elif p.is_dir():
            files = sorted(p.rglob("*.rs"))
        else:
            continue

        for f in files:
            if is_test_file(f):
                continue
            violations = scan_file(f)
            if violations:
                rel = str(f)
                all_violations[rel] = violations
                total_violations += len(violations)

    if total_violations == 0:
        log.info("PASS: No silent error coercion patterns found in production code")
        log.info("  Scanned: %s", ", ".join(SCAN_PATHS))
        log.info(
            "  Approved API: eval_required(), eval_speculative(),"
            " eval_bool_required(), eval_bool_speculative()"
        )
        return 0

    log.info("FAIL: %d silent error coercion violation(s) found", total_violations)
    log.info("")
    for filepath, violations in sorted(all_violations.items()):
        for lineno, line, desc in violations:
            log.info("  %s:%d: %s", filepath, lineno, desc)
            log.info("    %s", line.strip())
            log.info("")
    log.info(
        "Fix: Use eval_required(), eval_speculative(),"
        " eval_bool_required(), or eval_bool_speculative()"
    )
    log.info("      from crates/tla-check/src/error_policy.rs")
    log.info(
        "      Or add 'Part of #1433:' comment if the pattern"
        " is architecturally justified."
    )
    return total_violations


if __name__ == "__main__":
    sys.exit(main())
