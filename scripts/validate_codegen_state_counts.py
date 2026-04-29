#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Validate codegen state counts against TLC baselines.

End-to-end validation pipeline:
  1. Run `tla2 codegen --tir` on a spec to generate Rust code
  2. Create a standalone Cargo project with the generated code
  3. Build and run the generated model checker
  4. Compare state counts against spec_baseline.json

This validates the codegen pipeline produces *semantically correct* code,
not just code that compiles. State count mismatches indicate bugs in the
code generation (incorrect Init/Next/invariant translation).

Usage:
    python3 scripts/validate_codegen_state_counts.py --binary /tmp/tl8c/release/tla2
    python3 scripts/validate_codegen_state_counts.py --binary /tmp/tl8c/release/tla2 --spec DieHard --spec HourClock
    python3 scripts/validate_codegen_state_counts.py --binary /tmp/tl8c/release/tla2 --category small --limit 10

Part of #3937.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_PATH = REPO_ROOT / "tests" / "tlc_comparison" / "spec_baseline.json"
EXAMPLES_DIR = Path.home() / "tlaplus-examples" / "specifications"
RUNTIME_PATH = REPO_ROOT / "crates" / "tla-runtime"
VENDORED_STACKER = REPO_ROOT / "vendored" / "stacker"

# Timeouts
CODEGEN_TIMEOUT = 30
BUILD_TIMEOUT = 180
RUN_TIMEOUT = 120


@dataclass
class ValidationResult:
    """Result of end-to-end codegen validation for one spec."""
    name: str
    category: str
    tlc_states: Optional[int]
    tlc_status: str
    # Stage results
    codegen_ok: bool = False
    codegen_error: Optional[str] = None
    build_ok: bool = False
    build_error: Optional[str] = None
    run_ok: bool = False
    run_error: Optional[str] = None
    # State count comparison
    codegen_distinct_states: Optional[int] = None
    codegen_states_explored: Optional[int] = None
    states_match: Optional[bool] = None
    # Was there a deadlock or invariant violation?
    has_deadlock: bool = False
    has_violation: bool = False
    # Timings
    codegen_elapsed: float = 0.0
    build_elapsed: float = 0.0
    run_elapsed: float = 0.0

    @property
    def overall_status(self) -> str:
        if not self.codegen_ok:
            return "codegen_error"
        if not self.build_ok:
            return "build_error"
        if not self.run_ok:
            return "run_error"
        if self.has_violation:
            return "violation"
        if self.states_match is True:
            return "PASS"
        if self.states_match is False:
            return "STATE_MISMATCH"
        return "unknown"


def load_baseline() -> dict:
    with open(BASELINE_PATH) as f:
        return json.load(f)


def select_specs(
    specs: dict,
    category: Optional[str] = None,
    limit: Optional[int] = None,
    names: Optional[list[str]] = None,
) -> list[tuple[str, dict]]:
    """Select specs to test, filtering by criteria."""
    result = []
    for name, spec in sorted(specs.items()):
        if names and name not in names:
            continue
        if category and spec.get("category") != category:
            continue
        # Only test passing specs with known state counts
        tlc = spec.get("tlc", {})
        if tlc.get("status") != "pass" or not tlc.get("states"):
            continue
        # Only test specs whose source files exist
        tla_path = resolve_tla_path(spec["source"]["tla_path"])
        if not tla_path or not tla_path.exists():
            continue
        result.append((name, spec))
    if limit:
        result = result[:limit]
    return result


def resolve_tla_path(tla_rel: str) -> Optional[Path]:
    """Resolve a TLA path from spec_baseline.json to an absolute path."""
    if tla_rel.startswith("/"):
        p = Path(tla_rel)
        return p if p.exists() else None
    p = EXAMPLES_DIR / tla_rel
    return p if p.exists() else None


def resolve_cfg_path(cfg_rel: str) -> Optional[Path]:
    """Resolve a cfg path from spec_baseline.json to an absolute path."""
    if not cfg_rel:
        return None
    if cfg_rel.startswith("/"):
        p = Path(cfg_rel)
        return p if p.exists() else None
    p = EXAMPLES_DIR / cfg_rel
    return p if p.exists() else None


def run_codegen(
    binary: Path,
    tla_path: Path,
    cfg_path: Optional[Path],
) -> tuple[bool, str, float]:
    """Run tla2 codegen --tir on a spec. Returns (ok, code_or_error, elapsed)."""
    cmd = [str(binary), "codegen", "--tir", str(tla_path)]
    if cfg_path and cfg_path.exists():
        cmd.extend(["--config", str(cfg_path)])

    start = time.monotonic()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=CODEGEN_TIMEOUT,
            cwd=str(tla_path.parent),
        )
        elapsed = time.monotonic() - start
        if result.returncode == 0:
            return True, result.stdout, elapsed
        error = (result.stderr.strip() or result.stdout.strip())[:500]
        return False, error, elapsed
    except subprocess.TimeoutExpired:
        return False, f"codegen timeout ({CODEGEN_TIMEOUT}s)", time.monotonic() - start
    except Exception as e:
        return False, str(e), time.monotonic() - start


def sanitize_package_name(name: str) -> str:
    """Sanitize a spec name for use as a Cargo package name.

    Package names must start with a letter and contain only [a-z0-9_-].
    """
    snake = to_snake_case(name)
    # Ensure starts with a letter
    if snake and not snake[0].isalpha():
        snake = "spec_" + snake
    # Replace any invalid chars
    return re.sub(r'[^a-z0-9_-]', '_', snake)


def create_project(
    rust_code: str,
    spec_name: str,
    work_dir: Path,
) -> Path:
    """Create a standalone Cargo project from generated Rust code.

    Returns the project directory path.
    """
    project_dir = work_dir / f"{spec_name}_codegen"
    src_dir = project_dir / "src"
    src_dir.mkdir(parents=True, exist_ok=True)

    mod_name = sanitize_package_name(spec_name)  # also valid as Rust ident
    machine_type = to_pascal_case(spec_name)
    pkg_name = sanitize_package_name(spec_name)

    # Write Cargo.toml with absolute path to tla-runtime
    # Include [patch] for vendored stacker to avoid crates.io fetches
    stacker_patch = ""
    if VENDORED_STACKER.exists():
        stacker_patch = (
            f'\n[patch.crates-io]\n'
            f'stacker = {{ path = "{VENDORED_STACKER}" }}\n'
        )
    cargo_toml = (
        f'[package]\n'
        f'name = "{pkg_name}-codegen-test"\n'
        f'version = "0.1.0"\n'
        f'edition = "2021"\n'
        f'\n'
        f'[workspace]\n'
        f'\n'
        f'[[bin]]\n'
        f'name = "check"\n'
        f'path = "src/main.rs"\n'
        f'\n'
        f'[dependencies]\n'
        f'tla-runtime = {{ path = "{RUNTIME_PATH}" }}\n'
        f'{stacker_patch}'
    )
    (project_dir / "Cargo.toml").write_text(cargo_toml)

    # Write the generated module
    (src_dir / f"{mod_name}.rs").write_text(rust_code)

    # Write main.rs that runs the model checker and prints structured output
    # We need to detect the actual struct and machine names from the generated code.
    # The generated code follows the pattern: pub struct <Name>State and pub struct <Name>;
    actual_machine = extract_machine_name(rust_code)
    actual_state = f"{actual_machine}State"

    main_rs = (
        f'#![allow(unused)]\n'
        f'mod {mod_name};\n'
        f'\n'
        f'use {mod_name}::{actual_machine};\n'
        f'use tla_runtime::prelude::*;\n'
        f'\n'
        f'fn main() {{\n'
        f'    let machine = {actual_machine};\n'
        f'    let max_states = 10_000_000;\n'
        f'\n'
        f'    let result = model_check(&machine, max_states);\n'
        f'\n'
        f'    // Structured output for parsing\n'
        f'    println!("CODEGEN_DISTINCT_STATES={{}}", result.distinct_states);\n'
        f'    println!("CODEGEN_STATES_EXPLORED={{}}", result.states_explored);\n'
        f'\n'
        f'    if let Some(ref violation) = result.violation {{\n'
        f'        println!("CODEGEN_VIOLATION=true");\n'
        f'        eprintln!("INVARIANT VIOLATION: {{:?}}", violation.state);\n'
        f'    }} else {{\n'
        f'        println!("CODEGEN_VIOLATION=false");\n'
        f'    }}\n'
        f'\n'
        f'    if let Some(ref deadlock) = result.deadlock {{\n'
        f'        println!("CODEGEN_DEADLOCK=true");\n'
        f'    }} else {{\n'
        f'        println!("CODEGEN_DEADLOCK=false");\n'
        f'    }}\n'
        f'\n'
        f'    if result.is_ok() || result.deadlock.is_some() {{\n'
        f'        println!("CODEGEN_STATUS=ok");\n'
        f'    }} else {{\n'
        f'        println!("CODEGEN_STATUS=error");\n'
        f'        std::process::exit(1);\n'
        f'    }}\n'
        f'}}\n'
    )
    (src_dir / "main.rs").write_text(main_rs)

    return project_dir


def extract_machine_name(rust_code: str) -> str:
    """Extract the StateMachine struct name from generated Rust code."""
    # Look for: pub struct FooState
    match = re.search(r'pub struct (\w+)State\b', rust_code)
    if match:
        return match.group(1)
    # Fallback: look for impl StateMachine for X
    match = re.search(r'impl StateMachine for (\w+)', rust_code)
    if match:
        return match.group(1)
    return "Spec"


def find_raw_cargo() -> str:
    """Find the raw cargo binary, bypassing any wrapper scripts."""
    try:
        result = subprocess.run(
            ["rustup", "which", "cargo", "--toolchain", "stable"],
            capture_output=True, text=True, timeout=10,
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except Exception:
        pass
    return "cargo"


RAW_CARGO = find_raw_cargo()


# Shared target dir to avoid recompiling tla-runtime for each spec
SHARED_TARGET_DIR: Optional[Path] = None


def build_project(project_dir: Path) -> tuple[bool, str, float]:
    """Build the generated project. Returns (ok, error_or_empty, elapsed)."""
    target_dir = SHARED_TARGET_DIR or (project_dir / "target")
    cmd = [
        RAW_CARGO, "build", "--release",
        "--target-dir", str(target_dir),
    ]
    env = os.environ.copy()
    env["RUSTUP_TOOLCHAIN"] = "stable-aarch64-apple-darwin"

    start = time.monotonic()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=BUILD_TIMEOUT,
            cwd=str(project_dir),
            env=env,
        )
        elapsed = time.monotonic() - start
        if result.returncode == 0:
            return True, "", elapsed
        # Extract meaningful error lines (skip cargo progress noise)
        error_lines = []
        for line in result.stderr.split("\n"):
            stripped = line.strip()
            if stripped.startswith("error") or stripped.startswith("-->") or "mismatched" in stripped:
                error_lines.append(stripped)
        if error_lines:
            error = "\n".join(error_lines[:10])
        else:
            error = (result.stderr.strip())[:1000]
        return False, error, elapsed
    except subprocess.TimeoutExpired:
        return False, f"build timeout ({BUILD_TIMEOUT}s)", time.monotonic() - start
    except Exception as e:
        return False, str(e), time.monotonic() - start


def run_model_check(project_dir: Path) -> tuple[bool, dict, float]:
    """Run the generated model checker binary. Returns (ok, parsed_output, elapsed)."""
    target_dir = SHARED_TARGET_DIR or (project_dir / "target")
    binary = target_dir / "release" / "check"
    if not binary.exists():
        return False, {"error": f"binary not found at {binary}"}, 0.0

    start = time.monotonic()
    try:
        result = subprocess.run(
            [str(binary)],
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT,
            cwd=str(project_dir),
        )
        elapsed = time.monotonic() - start
        output = result.stdout
        parsed = parse_model_check_output(output)
        if result.returncode == 0:
            return True, parsed, elapsed
        # Non-zero exit can mean invariant violation (expected for some specs)
        parsed["exit_code"] = result.returncode
        parsed["stderr"] = (result.stderr.strip())[:500]
        return False, parsed, elapsed
    except subprocess.TimeoutExpired:
        return False, {"error": f"runtime timeout ({RUN_TIMEOUT}s)"}, time.monotonic() - start
    except Exception as e:
        return False, {"error": str(e)}, time.monotonic() - start


def parse_model_check_output(output: str) -> dict:
    """Parse structured output from the generated model checker."""
    result = {}
    for line in output.split("\n"):
        if "=" in line:
            key, _, value = line.partition("=")
            key = key.strip()
            value = value.strip()
            if key == "CODEGEN_DISTINCT_STATES":
                result["distinct_states"] = int(value)
            elif key == "CODEGEN_STATES_EXPLORED":
                result["states_explored"] = int(value)
            elif key == "CODEGEN_VIOLATION":
                result["violation"] = value == "true"
            elif key == "CODEGEN_DEADLOCK":
                result["deadlock"] = value == "true"
            elif key == "CODEGEN_STATUS":
                result["status"] = value
    return result


def validate_spec(
    binary: Path,
    name: str,
    spec: dict,
    work_dir: Path,
) -> ValidationResult:
    """Run end-to-end validation for one spec."""
    tla_rel = spec["source"]["tla_path"]
    cfg_rel = spec["source"]["cfg_path"]
    tla_path = resolve_tla_path(tla_rel)
    cfg_path = resolve_cfg_path(cfg_rel) if cfg_rel else None

    tlc = spec.get("tlc", {})
    vr = ValidationResult(
        name=name,
        category=spec.get("category", "unknown"),
        tlc_states=tlc.get("states"),
        tlc_status=tlc.get("status", "unknown"),
    )

    # Step 1: codegen
    ok, code_or_error, elapsed = run_codegen(binary, tla_path, cfg_path)
    vr.codegen_elapsed = elapsed
    if not ok:
        vr.codegen_error = code_or_error
        return vr
    vr.codegen_ok = True
    rust_code = code_or_error

    # Check if code has meaningful Init/Next
    if "fn init(" not in rust_code or "fn next(" not in rust_code:
        vr.codegen_error = "generated code missing init/next"
        vr.codegen_ok = False
        return vr

    # Step 2: create project and build
    project_dir = create_project(rust_code, name, work_dir)
    ok, error, elapsed = build_project(project_dir)
    vr.build_elapsed = elapsed
    if not ok:
        vr.build_ok = False
        vr.build_error = error
        return vr
    vr.build_ok = True

    # Step 3: run model checker
    ok, parsed, elapsed = run_model_check(project_dir)
    vr.run_elapsed = elapsed
    vr.codegen_distinct_states = parsed.get("distinct_states")
    vr.codegen_states_explored = parsed.get("states_explored")
    vr.has_violation = parsed.get("violation", False)
    vr.has_deadlock = parsed.get("deadlock", False)

    if not ok and not vr.has_violation:
        vr.run_error = parsed.get("error") or parsed.get("stderr") or "unknown runtime error"
        return vr
    vr.run_ok = True

    # Step 4: compare state counts
    # TLC baseline uses "states" which is distinct state count
    if vr.tlc_states and vr.codegen_distinct_states is not None:
        # For specs where TLC reports an error (invariant violation),
        # the state count is the total at time of violation, not total reachable.
        # For passing specs, we compare distinct states directly.
        if vr.tlc_status == "pass":
            # TLC reports error for DieHard (NotSolved violated), but our baseline
            # shows it as "pass" with 16 states. The codegen model checker might
            # find a violation on the invariant. Handle both cases.
            if vr.has_violation:
                # Can't compare state counts reliably when violation is found
                # (BFS stops at violation point)
                vr.states_match = None
            elif vr.has_deadlock:
                # Deadlock found — the total distinct states should still match
                # since BFS explores everything until deadlock
                vr.states_match = (vr.codegen_distinct_states == vr.tlc_states)
            else:
                vr.states_match = (vr.codegen_distinct_states == vr.tlc_states)

    return vr


def to_snake_case(s: str) -> str:
    """Convert PascalCase/camelCase to snake_case."""
    result = []
    for i, c in enumerate(s):
        if c.isupper() and i > 0:
            result.append("_")
        result.append(c.lower())
    return "".join(result)


def to_pascal_case(s: str) -> str:
    """Convert snake_case or plain names to PascalCase."""
    result = []
    capitalize = True
    for c in s:
        if c == "_" or c == "-":
            capitalize = True
        elif capitalize:
            result.append(c.upper())
            capitalize = False
        else:
            result.append(c)
    return "".join(result)


def print_summary(results: list[ValidationResult]) -> None:
    """Print a summary of validation results."""
    total = len(results)
    if total == 0:
        print("No specs tested.")
        return

    codegen_ok = sum(1 for r in results if r.codegen_ok)
    build_ok = sum(1 for r in results if r.build_ok)
    run_ok = sum(1 for r in results if r.run_ok)
    pass_count = sum(1 for r in results if r.overall_status == "PASS")
    mismatch_count = sum(1 for r in results if r.overall_status == "STATE_MISMATCH")
    violation_count = sum(1 for r in results if r.overall_status == "violation")

    print()
    print("=" * 70)
    print("CODEGEN STATE COUNT VALIDATION SUMMARY")
    print("=" * 70)
    print(f"Total specs tested:      {total}")
    print(f"Codegen OK:              {codegen_ok}/{total}")
    print(f"Build OK:                {build_ok}/{total}")
    print(f"Run OK:                  {run_ok}/{total}")
    print(f"State count PASS:        {pass_count}/{total}")
    print(f"State count MISMATCH:    {mismatch_count}/{total}")
    print(f"Invariant violation:     {violation_count}/{total}")
    print()

    # Detailed table
    print(f"{'Spec':<30} {'Status':<16} {'TLC':>8} {'Codegen':>8} {'Match':>6}")
    print("-" * 70)
    for r in sorted(results, key=lambda x: (x.overall_status != "PASS", x.name)):
        tlc_str = str(r.tlc_states) if r.tlc_states else "-"
        cg_str = str(r.codegen_distinct_states) if r.codegen_distinct_states is not None else "-"
        match_str = {True: "YES", False: "NO", None: "-"}.get(r.states_match, "-")
        status = r.overall_status
        print(f"{r.name:<30} {status:<16} {tlc_str:>8} {cg_str:>8} {match_str:>6}")

    # Show errors
    errors = [r for r in results if r.overall_status not in ("PASS", "STATE_MISMATCH")]
    if errors:
        print()
        print("ERRORS:")
        for r in errors:
            error_msg = r.codegen_error or r.build_error or r.run_error or "unknown"
            # Truncate to first line
            first_line = error_msg.split("\n")[0][:80]
            print(f"  {r.name}: {r.overall_status} - {first_line}")


def write_json_report(results: list[ValidationResult], output_path: Path) -> None:
    """Write a JSON report of the validation results."""
    data = {
        "date": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "total": len(results),
        "pass": sum(1 for r in results if r.overall_status == "PASS"),
        "mismatch": sum(1 for r in results if r.overall_status == "STATE_MISMATCH"),
        "specs": [
            {
                "name": r.name,
                "category": r.category,
                "status": r.overall_status,
                "tlc_states": r.tlc_states,
                "codegen_distinct_states": r.codegen_distinct_states,
                "codegen_states_explored": r.codegen_states_explored,
                "states_match": r.states_match,
                "has_violation": r.has_violation,
                "has_deadlock": r.has_deadlock,
                "codegen_error": r.codegen_error,
                "build_error": r.build_error,
                "run_error": r.run_error,
                "timings": {
                    "codegen_s": round(r.codegen_elapsed, 2),
                    "build_s": round(r.build_elapsed, 2),
                    "run_s": round(r.run_elapsed, 2),
                },
            }
            for r in results
        ],
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(data, indent=2))
    print(f"\nJSON report: {output_path}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Validate codegen state counts against TLC baselines."
    )
    parser.add_argument(
        "--binary", type=Path, required=True,
        help="Path to tla2 binary",
    )
    parser.add_argument(
        "--category", choices=["small", "medium", "large", "xlarge"],
        help="Filter specs by category",
    )
    parser.add_argument(
        "--limit", type=int,
        help="Maximum number of specs to test",
    )
    parser.add_argument(
        "--spec", action="append",
        help="Test specific spec(s) by name (repeatable)",
    )
    parser.add_argument(
        "--json", type=Path,
        help="Write JSON report to this path",
    )
    parser.add_argument(
        "--keep-work-dir", action="store_true",
        help="Don't delete the temporary work directory",
    )
    parser.add_argument(
        "--shared-target", type=Path,
        help="Shared Cargo target dir (avoids recompiling tla-runtime per spec)",
    )
    args = parser.parse_args()

    if not args.binary.exists():
        print(f"ERROR: binary not found at {args.binary}", file=sys.stderr)
        sys.exit(1)

    if not RUNTIME_PATH.exists():
        print(f"ERROR: tla-runtime not found at {RUNTIME_PATH}", file=sys.stderr)
        sys.exit(1)

    global SHARED_TARGET_DIR
    if args.shared_target:
        SHARED_TARGET_DIR = args.shared_target
        SHARED_TARGET_DIR.mkdir(parents=True, exist_ok=True)

    baseline = load_baseline()
    specs_to_test = select_specs(
        baseline["specs"],
        category=args.category,
        limit=args.limit,
        names=args.spec,
    )

    if not specs_to_test:
        print("No specs selected for testing.", file=sys.stderr)
        sys.exit(1)

    print(f"Testing {len(specs_to_test)} specs with binary: {args.binary}")
    print(f"Runtime: {RUNTIME_PATH}")
    print()

    work_dir = Path(tempfile.mkdtemp(prefix="codegen_validate_"))
    print(f"Work directory: {work_dir}")
    print()

    results = []
    for idx, (name, spec) in enumerate(specs_to_test):
        progress = f"[{idx+1}/{len(specs_to_test)}]"
        print(f"{progress} {name} ({spec.get('category','?')})...", end=" ", flush=True)

        vr = validate_spec(args.binary, name, spec, work_dir)
        results.append(vr)

        # Print inline result
        status = vr.overall_status
        if status == "PASS":
            print(f"PASS (states={vr.codegen_distinct_states}, "
                  f"codegen={vr.codegen_elapsed:.1f}s, "
                  f"build={vr.build_elapsed:.1f}s, "
                  f"run={vr.run_elapsed:.1f}s)")
        elif status == "STATE_MISMATCH":
            print(f"MISMATCH (tlc={vr.tlc_states}, codegen={vr.codegen_distinct_states})")
        elif status == "violation":
            print(f"VIOLATION (states={vr.codegen_distinct_states})")
        else:
            error = vr.codegen_error or vr.build_error or vr.run_error or "?"
            first_line = error.split("\n")[0][:60]
            print(f"{status}: {first_line}")

    print_summary(results)

    if args.json:
        write_json_report(results, args.json)

    if not args.keep_work_dir:
        shutil.rmtree(work_dir, ignore_errors=True)
        print(f"Cleaned up work directory: {work_dir}")
    else:
        print(f"Work directory kept: {work_dir}")


if __name__ == "__main__":
    main()
