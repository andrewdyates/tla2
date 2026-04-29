#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Validate TLA2 codegen coverage against the full spec baseline suite.

Reads specs from tests/tlc_comparison/spec_baseline.json, runs
`tla2 codegen` (both AST and TIR paths) on each spec, and reports
coverage metrics including:
  - codegen_ok: code generation succeeded (Rust source emitted)
  - codegen_error: code generation failed (parse/lower/emit error)
  - compile_ok: generated Rust compiles with rustc --edition 2021
  - compile_error: generated Rust fails to compile
  - error categorization by root cause

Results are written to reports/codegen-coverage.md.

Usage:
    python3 scripts/validate_codegen.py [--binary PATH] [--category small]
        [--limit 30] [--compile] [--tir] [--output reports/codegen-coverage.md]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_PATH = REPO_ROOT / "tests" / "tlc_comparison" / "spec_baseline.json"
EXAMPLES_DIR = Path.home() / "tlaplus-examples" / "specifications"
DEFAULT_BINARY = Path("/tmp/tla2-codegen-r4/release/tla2")
DEFAULT_OUTPUT = REPO_ROOT / "reports" / "codegen-coverage.md"

# Timeout for codegen (seconds)
CODEGEN_TIMEOUT = 30
# Timeout for rustc compile check (seconds)
COMPILE_TIMEOUT = 30


@dataclass
class SpecResult:
    """Result of running codegen on a single spec."""
    name: str
    category: str
    tla_path: str
    cfg_path: str
    tlc_states: Optional[int]
    tlc_status: str
    # Codegen results
    codegen_ok: bool = False
    codegen_error: Optional[str] = None
    codegen_elapsed: float = 0.0
    generated_lines: int = 0
    # Compile results (if --compile)
    compile_ok: Optional[bool] = None
    compile_error: Optional[str] = None
    # TIR codegen results (if --tir)
    tir_codegen_ok: Optional[bool] = None
    tir_codegen_error: Optional[str] = None
    tir_generated_lines: int = 0
    # Meaningful codegen (has Init+Next, not empty stubs)
    meaningful: bool = False
    tir_meaningful: bool = False
    # Error classification
    error_category: Optional[str] = None


def classify_error(error_text: str) -> str:
    """Classify codegen errors into root cause categories."""
    lower = error_text.lower()

    if "parse" in lower or "syntax" in lower or "unexpected token" in lower:
        return "parse_error"
    if "lower failed" in lower or "lower produced no module" in lower:
        return "lower_error"
    if "tir lowering failed" in lower:
        return "tir_lower_error"
    if "not yet implemented" in lower or "todo" in lower or "unimplemented" in lower:
        return "unimplemented"
    if "extends" in lower or "module not found" in lower or "load extends" in lower:
        return "module_not_found"
    if "instance" in lower or "load instance" in lower:
        return "instance_error"
    if "unknown identifier" in lower:
        return "unknown_identifier"
    if "unsupported for codegen" in lower:
        return "unsupported_feature"
    if "unsupported" in lower:
        return "unsupported_feature"
    if "timeout" in lower or "timed out" in lower:
        return "timeout"
    if "panic" in lower or "stack overflow" in lower or "thread" in lower:
        return "crash"
    if "no such file" in lower or "os error 2" in lower:
        return "file_not_found"
    if "type inference error" in lower:
        return "type_inference"
    if "type" in lower and ("mismatch" in lower or "error" in lower):
        return "type_error"
    return "other"


def classify_compile_error(error_text: str) -> str:
    """Classify Rust compilation errors."""
    if "cannot find" in error_text:
        return "missing_item"
    if "expected" in error_text and "found" in error_text:
        return "type_mismatch"
    if "not found in" in error_text:
        return "import_error"
    if "trait" in error_text:
        return "trait_error"
    return "other_compile"


def is_meaningful_codegen(rust_code: str) -> bool:
    """Check if generated Rust code has substantive Init/Next implementations.

    Returns False for empty stubs that just return vec![] or have
    "No Init operator found" / "No Next operator found" comments.
    """
    has_init = False
    has_next = False
    for line in rust_code.split("\n"):
        stripped = line.strip()
        # Check for actual Init implementations (not empty stubs)
        if "fn init(" in stripped and "No Init operator found" not in rust_code:
            has_init = True
        if "fn next(" in stripped and "No Next operator found" not in rust_code:
            has_next = True
    return has_init and has_next


def run_codegen(
    binary: Path,
    tla_path: Path,
    cfg_path: Optional[Path],
    tir: bool = False,
) -> tuple[bool, str, float, int]:
    """Run tla2 codegen on a spec, return (ok, output_or_error, elapsed, lines)."""
    cmd = [str(binary), "codegen", str(tla_path)]
    if tir:
        cmd.append("--tir")
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
            output = result.stdout
            lines = output.count("\n")
            return True, output, elapsed, lines
        else:
            error = result.stderr.strip() or result.stdout.strip()
            # Truncate long errors
            if len(error) > 500:
                error = error[:500] + "..."
            return False, error, elapsed, 0
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return False, "timeout after {}s".format(CODEGEN_TIMEOUT), elapsed, 0
    except Exception as e:
        elapsed = time.monotonic() - start
        return False, str(e), elapsed, 0


def run_compile_check(rust_code: str) -> tuple[bool, str]:
    """Try to compile the generated Rust code with rustc."""
    with tempfile.NamedTemporaryFile(
        suffix=".rs", mode="w", delete=False
    ) as f:
        f.write(rust_code)
        f.flush()
        tmp_path = f.name

    try:
        result = subprocess.run(
            [
                "rustc",
                "--edition", "2021",
                "--crate-type", "lib",
                "-o", "/dev/null",
                tmp_path,
            ],
            capture_output=True,
            text=True,
            timeout=COMPILE_TIMEOUT,
        )
        if result.returncode == 0:
            return True, ""
        error = result.stderr.strip()
        if len(error) > 500:
            error = error[:500] + "..."
        return False, error
    except subprocess.TimeoutExpired:
        return False, "compile timeout"
    except Exception as e:
        return False, str(e)
    finally:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass


def load_baseline() -> dict:
    """Load spec_baseline.json."""
    with open(BASELINE_PATH) as f:
        return json.load(f)


def select_specs(
    specs: dict,
    category: Optional[str] = None,
    limit: Optional[int] = None,
    names: Optional[list[str]] = None,
) -> list[tuple[str, dict]]:
    """Select specs to test, optionally filtering by category or names."""
    result = []
    for name, spec in sorted(specs.items()):
        if names and name not in names:
            continue
        if category and spec.get("category") != category:
            continue
        # Only test specs whose source files exist
        tla_path = EXAMPLES_DIR / spec["source"]["tla_path"]
        if not tla_path.exists():
            continue
        result.append((name, spec))
    if limit:
        result = result[:limit]
    return result


def run_validation(
    binary: Path,
    specs_to_test: list[tuple[str, dict]],
    do_compile: bool = False,
    do_tir: bool = False,
) -> list[SpecResult]:
    """Run codegen on all selected specs and collect results."""
    results = []
    total = len(specs_to_test)

    for idx, (name, spec) in enumerate(specs_to_test):
        tla_rel = spec["source"]["tla_path"]
        cfg_rel = spec["source"]["cfg_path"]
        tla_path = EXAMPLES_DIR / tla_rel
        cfg_path = EXAMPLES_DIR / cfg_rel if cfg_rel else None

        sr = SpecResult(
            name=name,
            category=spec.get("category", "unknown"),
            tla_path=tla_rel,
            cfg_path=cfg_rel or "",
            tlc_states=spec.get("tlc", {}).get("states"),
            tlc_status=spec.get("tlc", {}).get("status", "unknown"),
        )

        # Progress output every spec
        progress = f"[{idx+1}/{total}]"
        print(f"{progress} {name} ({sr.category})...", end=" ", flush=True)

        # AST codegen
        ok, output, elapsed, lines = run_codegen(binary, tla_path, cfg_path, tir=False)
        sr.codegen_ok = ok
        sr.codegen_elapsed = elapsed
        sr.generated_lines = lines
        if not ok:
            sr.codegen_error = output
            sr.error_category = classify_error(output)
            print(f"CODEGEN_ERROR ({sr.error_category}) {elapsed:.1f}s")
        else:
            sr.meaningful = is_meaningful_codegen(output)
            tag = "meaningful" if sr.meaningful else "stub"
            print(f"OK ({lines} lines, {tag}, {elapsed:.1f}s)", end="")

            # Optionally try to compile
            if do_compile:
                compile_ok, compile_err = run_compile_check(output)
                sr.compile_ok = compile_ok
                if not compile_ok:
                    sr.compile_error = compile_err
                    print(f" COMPILE_ERROR", end="")
                else:
                    print(f" COMPILES", end="")
            print()

        # TIR codegen (if requested)
        if do_tir:
            tir_ok, tir_output, _, tir_lines = run_codegen(
                binary, tla_path, cfg_path, tir=True
            )
            sr.tir_codegen_ok = tir_ok
            sr.tir_generated_lines = tir_lines
            if tir_ok:
                sr.tir_meaningful = is_meaningful_codegen(tir_output)
            if not tir_ok:
                sr.tir_codegen_error = tir_output

        results.append(sr)

    return results


def generate_report(
    results: list[SpecResult],
    binary: Path,
    do_compile: bool,
    do_tir: bool,
) -> str:
    """Generate a Markdown report from the results."""
    lines = []
    lines.append("# Codegen Coverage Report")
    lines.append("")
    lines.append(f"**Date:** {time.strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append(f"**Binary:** `{binary}`")
    lines.append(f"**Specs tested:** {len(results)}")
    lines.append(f"**Compile check:** {'yes' if do_compile else 'no'}")
    lines.append(f"**TIR path:** {'yes' if do_tir else 'no'}")
    lines.append("")

    # Summary
    total = len(results)
    codegen_ok = sum(1 for r in results if r.codegen_ok)
    codegen_err = total - codegen_ok
    meaningful = sum(1 for r in results if r.meaningful)
    lines.append("## Summary (AST Path)")
    lines.append("")
    lines.append(f"| Metric | Count | Pct |")
    lines.append(f"|--------|------:|----:|")
    lines.append(
        f"| Codegen OK | {codegen_ok} | {100*codegen_ok/total:.0f}% |"
        if total > 0 else "| Codegen OK | 0 | 0% |"
    )
    lines.append(
        f"| Meaningful (Init+Next) | {meaningful} | {100*meaningful/total:.0f}% |"
        if total > 0 else "| Meaningful (Init+Next) | 0 | 0% |"
    )
    lines.append(
        f"| Stub Only | {codegen_ok - meaningful} | {100*(codegen_ok - meaningful)/total:.0f}% |"
        if total > 0 else "| Stub Only | 0 | 0% |"
    )
    lines.append(
        f"| Codegen Error | {codegen_err} | {100*codegen_err/total:.0f}% |"
        if total > 0 else "| Codegen Error | 0 | 0% |"
    )

    if do_compile:
        compile_tested = [r for r in results if r.compile_ok is not None]
        compile_ok = sum(1 for r in compile_tested if r.compile_ok)
        compile_err = len(compile_tested) - compile_ok
        if compile_tested:
            lines.append(
                f"| Compiles OK | {compile_ok} | "
                f"{100*compile_ok/len(compile_tested):.0f}% |"
            )
            lines.append(
                f"| Compile Error | {compile_err} | "
                f"{100*compile_err/len(compile_tested):.0f}% |"
            )

    if do_tir:
        tir_tested = [r for r in results if r.tir_codegen_ok is not None]
        tir_ok = sum(1 for r in tir_tested if r.tir_codegen_ok)
        tir_err = len(tir_tested) - tir_ok
        tir_meaningful = sum(1 for r in tir_tested if r.tir_meaningful)
        if tir_tested:
            lines.append("")
            lines.append("**TIR Path:**")
            lines.append("")
            lines.append(f"| Metric | Count | Pct |")
            lines.append(f"|--------|------:|----:|")
            lines.append(
                f"| TIR Codegen OK | {tir_ok} | "
                f"{100*tir_ok/len(tir_tested):.0f}% |"
            )
            lines.append(
                f"| TIR Meaningful (Init+Next) | {tir_meaningful} | "
                f"{100*tir_meaningful/len(tir_tested):.0f}% |"
            )
            lines.append(
                f"| TIR Stub Only | {tir_ok - tir_meaningful} | "
                f"{100*(tir_ok - tir_meaningful)/len(tir_tested):.0f}% |"
            )
            lines.append(
                f"| TIR Codegen Error | {tir_err} | "
                f"{100*tir_err/len(tir_tested):.0f}% |"
            )

    lines.append("")

    # By category breakdown
    lines.append("## Coverage by Category")
    lines.append("")
    lines.append("| Category | Total | Codegen OK | Pct |")
    lines.append("|----------|------:|-----------:|----:|")
    by_cat: dict[str, list[SpecResult]] = defaultdict(list)
    for r in results:
        by_cat[r.category].append(r)
    for cat in ["small", "medium", "large", "xlarge", "unknown"]:
        if cat in by_cat:
            cat_results = by_cat[cat]
            cat_ok = sum(1 for r in cat_results if r.codegen_ok)
            pct = 100 * cat_ok / len(cat_results) if cat_results else 0
            lines.append(
                f"| {cat} | {len(cat_results)} | {cat_ok} | {pct:.0f}% |"
            )
    lines.append("")

    # Error categories
    error_results = [r for r in results if not r.codegen_ok]
    if error_results:
        lines.append("## Error Categories")
        lines.append("")
        cat_counts = Counter(r.error_category for r in error_results)
        lines.append("| Error Category | Count |")
        lines.append("|----------------|------:|")
        for cat, count in cat_counts.most_common():
            lines.append(f"| {cat} | {count} |")
        lines.append("")

    # Detailed results table
    lines.append("## Detailed Results")
    lines.append("")
    header = "| Spec | Category | TLC States | Codegen | Lines |"
    sep = "|------|----------|-----------|---------|------:|"
    if do_compile:
        header += " Compile |"
        sep += "---------|"
    if do_tir:
        header += " TIR |"
        sep += "-----|"
    header += " Error |"
    sep += "-------|"

    lines.append(header)
    lines.append(sep)

    for r in sorted(results, key=lambda x: (not x.codegen_ok, x.name)):
        states_str = str(r.tlc_states) if r.tlc_states else "-"
        codegen_str = "OK" if r.codegen_ok else "FAIL"
        lines_str = str(r.generated_lines) if r.codegen_ok else "-"
        error_str = r.error_category or ""

        row = f"| {r.name} | {r.category} | {states_str} | {codegen_str} | {lines_str} |"
        if do_compile:
            if r.compile_ok is True:
                row += " OK |"
            elif r.compile_ok is False:
                row += " FAIL |"
            else:
                row += " - |"
        if do_tir:
            if r.tir_codegen_ok is True:
                row += " OK |"
            elif r.tir_codegen_ok is False:
                row += " FAIL |"
            else:
                row += " - |"
        row += f" {error_str} |"
        lines.append(row)

    lines.append("")

    # Error details for failures
    if error_results:
        lines.append("## Error Details")
        lines.append("")
        for r in sorted(error_results, key=lambda x: x.name):
            lines.append(f"### {r.name}")
            lines.append(f"- **Category:** {r.error_category}")
            lines.append(f"- **File:** `{r.tla_path}`")
            error_text = (r.codegen_error or "").strip()
            if error_text:
                # Limit to first 3 lines
                error_lines = error_text.split("\n")[:3]
                lines.append("```")
                lines.extend(error_lines)
                lines.append("```")
            lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Validate TLA2 codegen against spec baseline suite."
    )
    parser.add_argument(
        "--binary",
        type=Path,
        default=DEFAULT_BINARY,
        help="Path to tla2 binary (default: %(default)s)",
    )
    parser.add_argument(
        "--category",
        choices=["small", "medium", "large", "xlarge"],
        help="Filter specs by category",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Maximum number of specs to test",
    )
    parser.add_argument(
        "--spec",
        action="append",
        help="Test specific spec(s) by name (repeatable)",
    )
    parser.add_argument(
        "--compile",
        action="store_true",
        help="Also check if generated Rust compiles with rustc",
    )
    parser.add_argument(
        "--tir",
        action="store_true",
        help="Also test TIR-based codegen path",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output report path (default: %(default)s)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Also write JSON results alongside markdown",
    )
    args = parser.parse_args()

    # Validate binary exists
    if not args.binary.exists():
        print(f"ERROR: binary not found at {args.binary}", file=sys.stderr)
        print(
            "Build with: RUSTUP_TOOLCHAIN=stable-aarch64-apple-darwin "
            "$(rustup which cargo --toolchain stable) build --release "
            "--bin tla2 --target-dir /tmp/tla2-codegen-r4",
            file=sys.stderr,
        )
        sys.exit(1)

    # Load baseline
    baseline = load_baseline()
    specs = baseline["specs"]

    # Select specs
    specs_to_test = select_specs(
        specs,
        category=args.category,
        limit=args.limit,
        names=args.spec,
    )

    if not specs_to_test:
        print("No specs selected for testing.", file=sys.stderr)
        sys.exit(1)

    print(f"Testing {len(specs_to_test)} specs with binary: {args.binary}")
    print(f"Options: compile={args.compile}, tir={args.tir}")
    print()

    # Run validation
    results = run_validation(
        args.binary,
        specs_to_test,
        do_compile=args.compile,
        do_tir=args.tir,
    )

    # Print summary to stdout
    total = len(results)
    codegen_ok = sum(1 for r in results if r.codegen_ok)
    meaningful = sum(1 for r in results if r.meaningful)
    print()
    print(f"=== CODEGEN COVERAGE SUMMARY (AST path) ===")
    print(f"Total:        {total}")
    print(f"Codegen OK:   {codegen_ok} ({100*codegen_ok/total:.0f}%)")
    print(f"  Meaningful: {meaningful} ({100*meaningful/total:.0f}%)")
    print(f"  Stub only:  {codegen_ok - meaningful} ({100*(codegen_ok - meaningful)/total:.0f}%)")
    print(f"Codegen ERR:  {total-codegen_ok} ({100*(total-codegen_ok)/total:.0f}%)")

    if args.compile:
        compile_tested = [r for r in results if r.compile_ok is not None]
        compile_ok = sum(1 for r in compile_tested if r.compile_ok)
        if compile_tested:
            print(
                f"Compiles OK:  {compile_ok}/{len(compile_tested)} "
                f"({100*compile_ok/len(compile_tested):.0f}%)"
            )

    if args.tir:
        tir_tested = [r for r in results if r.tir_codegen_ok is not None]
        tir_ok = sum(1 for r in tir_tested if r.tir_codegen_ok)
        tir_meaningful = sum(1 for r in tir_tested if r.tir_meaningful)
        if tir_tested:
            print()
            print(f"=== TIR PATH ===")
            print(f"TIR OK:       {tir_ok}/{len(tir_tested)} ({100*tir_ok/len(tir_tested):.0f}%)")
            print(f"  Meaningful: {tir_meaningful} ({100*tir_meaningful/len(tir_tested):.0f}%)")
            print(f"  Stub only:  {tir_ok - tir_meaningful} ({100*(tir_ok - tir_meaningful)/len(tir_tested):.0f}%)")

    # Error breakdown
    error_results = [r for r in results if not r.codegen_ok]
    if error_results:
        cat_counts = Counter(r.error_category for r in error_results)
        print()
        print("Error breakdown:")
        for cat, count in cat_counts.most_common():
            print(f"  {cat}: {count}")

    # Generate and write report
    report = generate_report(results, args.binary, args.compile, args.tir)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report)
    print(f"\nReport written to: {args.output}")

    # Optionally write JSON
    if args.json:
        json_path = args.output.with_suffix(".json")
        json_data = {
            "date": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "binary": str(args.binary),
            "total": total,
            "codegen_ok": codegen_ok,
            "codegen_meaningful": meaningful,
            "codegen_error": total - codegen_ok,
            "specs": [
                {
                    "name": r.name,
                    "category": r.category,
                    "codegen_ok": r.codegen_ok,
                    "meaningful": r.meaningful,
                    "codegen_error": r.codegen_error,
                    "error_category": r.error_category,
                    "generated_lines": r.generated_lines,
                    "codegen_elapsed": round(r.codegen_elapsed, 2),
                    "compile_ok": r.compile_ok,
                    "tir_codegen_ok": r.tir_codegen_ok,
                    "tir_meaningful": r.tir_meaningful,
                    "tlc_states": r.tlc_states,
                }
                for r in results
            ],
        }
        json_path.write_text(json.dumps(json_data, indent=2))
        print(f"JSON written to: {json_path}")


if __name__ == "__main__":
    main()
