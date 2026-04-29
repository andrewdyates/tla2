# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""CLI orchestration for TLC baseline collection."""

import argparse

from .baseline_json import (
    compute_categories,
    compute_stats,
    load_existing_output,
    make_untested_tla2_entry,
    order_spec_entry,
    seed_from_expected_results,
    write_output,
)
from .config import ALL_SPECS, EXAMPLES_DIR, EXPECTED_RESULTS, OUTPUT_FILE, TIMEOUT
from .provenance import build_provenance
from .tlc_runner import categorize_runtime, run_tlc


def main():
    parser = argparse.ArgumentParser(description="Collect TLC baselines for all specs.")
    parser.add_argument("--timeout", type=int, default=TIMEOUT, help="Timeout per spec in seconds")
    parser.add_argument("--no-resume", action="store_true", help="Do not reuse existing output file")
    parser.add_argument(
        "--no-seed-expected-results",
        action="store_true",
        help="Do not seed from tests/tlc_comparison/expected_results.json",
    )
    args = parser.parse_args()

    timeout_seconds = args.timeout
    seed_enabled = not args.no_seed_expected_results
    seed_source = EXPECTED_RESULTS if seed_enabled else None

    provenance = build_provenance(
        timeout_seconds=timeout_seconds,
        seed_enabled=seed_enabled,
        seed_source=seed_source,
    )

    print(f"Collecting TLC baselines for {len(ALL_SPECS)} specs...")
    print(f"Output: {OUTPUT_FILE}")
    print(f"Timeout: {timeout_seconds}s per spec")
    print(f"Provenance: schema_version={provenance['schema_version']}, "
          f"tlc={provenance['tlc']['tlc_version']}, "
          f"examples={provenance['inputs']['examples_git']['head_short']}")
    print()

    existing = {} if args.no_resume else load_existing_output(OUTPUT_FILE)
    baselines_raw = dict(existing.get("specs", {})) if isinstance(existing.get("specs"), dict) else {}
    baselines = {k: v for k, v in baselines_raw.items() if isinstance(v, dict)}

    if seed_enabled:
        seeded = seed_from_expected_results()
        for name, data in seeded.items():
            baselines.setdefault(name, data)

    baselines = {name: order_spec_entry(entry) for name, entry in baselines.items()}

    for i, spec in enumerate(ALL_SPECS):
        print(f"\r[{i+1}/{len(ALL_SPECS)}] {spec.name[:40]:<40}", end="", flush=True)

        existing_entry = baselines.get(spec.name)
        if isinstance(existing_entry, dict):
            tlc = existing_entry.get("tlc") or {}
            status = tlc.get("status")
            if status == "pass" and tlc.get("states") is not None:
                continue
            if status in {"error", "timeout"}:
                continue

        spec_path = EXAMPLES_DIR / spec.tla_path
        cfg_path = EXAMPLES_DIR / spec.cfg_path

        if not spec_path.exists():
            baselines[spec.name] = {
                "tlc": {
                    "status": "error",
                    "states": None,
                    "runtime_seconds": None,
                    "error_type": "missing_file",
                    "error": f"File not found: {spec.tla_path}",
                },
                "tla2": (existing_entry or {}).get("tla2")
                if isinstance(existing_entry, dict)
                else make_untested_tla2_entry(),
                "verified_match": False,
                "category": "unknown",
            }
            write_output(OUTPUT_FILE, baselines=baselines, provenance=provenance)
            continue

        if not cfg_path.exists():
            baselines[spec.name] = {
                "tlc": {
                    "status": "error",
                    "states": None,
                    "runtime_seconds": None,
                    "error_type": "missing_config",
                    "error": f"Config not found: {spec.cfg_path}",
                },
                "tla2": (existing_entry or {}).get("tla2")
                if isinstance(existing_entry, dict)
                else make_untested_tla2_entry(),
                "verified_match": False,
                "category": "unknown",
            }
            write_output(OUTPUT_FILE, baselines=baselines, provenance=provenance)
            continue

        tlc_result = run_tlc(spec_path, cfg_path, timeout_seconds=timeout_seconds)
        category = categorize_runtime(tlc_result.get("runtime_seconds"))

        tla2_data = None
        issue = None
        if isinstance(existing_entry, dict):
            tla2_data = existing_entry.get("tla2")
            issue = existing_entry.get("issue")
        if not isinstance(tla2_data, dict):
            tla2_data = make_untested_tla2_entry()

        verified_match = (
            tla2_data.get("status") == "pass"
            and tla2_data.get("states") is not None
            and tlc_result.get("states") is not None
            and tla2_data.get("states") == tlc_result.get("states")
        )

        spec_entry = {
            "tlc": tlc_result,
            "tla2": tla2_data,
            "verified_match": verified_match,
            "category": category,
            "source": {
                "tla_path": spec.tla_path,
                "cfg_path": spec.cfg_path,
            },
        }
        if issue is not None:
            spec_entry["issue"] = issue

        baselines[spec.name] = order_spec_entry(spec_entry)
        write_output(OUTPUT_FILE, baselines=baselines, provenance=provenance)

        stats = compute_stats(baselines)
        status_str = (
            f"tlc_pass:{stats['tlc_pass']} "
            f"tlc_err:{stats['tlc_error']} "
            f"tlc_timeout:{stats['tlc_timeout']}"
        )
        print(f"\r[{i+1}/{len(ALL_SPECS)}] {spec.name[:30]:<30} {status_str}", end="", flush=True)

    print("\n")

    print("=" * 60)
    print("TLC BASELINE COLLECTION SUMMARY")
    print("=" * 60)
    stats = compute_stats(baselines)
    print(f"TLC pass:    {stats['tlc_pass']}")
    print(f"TLC error:   {stats['tlc_error']}")
    print(f"TLC timeout: {stats['tlc_timeout']}")
    print()

    categories = compute_categories(baselines)
    print("Runtime Categories:")
    print(f"  Small (<1s):     {categories['small']}")
    print(f"  Medium (<30s):   {categories['medium']}")
    print(f"  Large (<300s):   {categories['large']}")
    print(f"  XLarge (>300s):  {categories['xlarge']}")
    print(f"  Skip/Unknown:    {categories['skip'] + categories['unknown']}")
    print()

    write_output(OUTPUT_FILE, baselines=baselines, provenance=provenance)
    print(f"Wrote {OUTPUT_FILE}")

    errors = [
        (name, data)
        for name, data in baselines.items()
        if (data.get("tlc") or {}).get("status") in ("error", "timeout")
    ]
    if errors:
        print()
        print("ERRORS/TIMEOUTS:")
        for name, data in errors[:20]:
            tlc = data.get("tlc") or {}
            print(f"  {name}: {tlc.get('status')} - {tlc.get('error_type', 'unknown')}")
        if len(errors) > 20:
            print(f"  ... and {len(errors) - 20} more")
