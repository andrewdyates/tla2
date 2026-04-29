# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Baseline schema normalization, ordering, validation, and writing."""

import json
import os
import sys
from collections import OrderedDict
from datetime import datetime
from pathlib import Path

from json_jcs import sha256_jcs

from .config import (
    ALL_SPECS,
    CATEGORIES_KEY_ORDER,
    EXPECTED_RESULTS,
    SPEC_ENTRY_KEY_ORDER,
    STATS_KEY_ORDER,
    TLA2_ENTRY_KEY_ORDER,
    TLC_ENTRY_KEY_ORDER,
)
from .tlc_runner import categorize_runtime


def make_untested_tla2_entry() -> dict:
    """Return the canonical placeholder for an untested TLA2 result."""
    return {
        "status": "untested",
        "states": None,
        "error_type": None,
        "last_run": None,
        "git_commit": None,
    }


def load_existing_output(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        with open(path) as f:
            data = json.load(f)
        if isinstance(data, dict) and isinstance(data.get("specs"), dict):
            return data
    except Exception:
        return {}
    return {}


def seed_from_expected_results() -> dict:
    if not EXPECTED_RESULTS.exists():
        return {}
    try:
        with open(EXPECTED_RESULTS) as f:
            data = json.load(f)
    except Exception:
        return {}

    out = {}
    specs = data.get("specs", {})
    if not isinstance(specs, dict):
        return {}

    for name, spec_data in specs.items():
        if not isinstance(spec_data, dict):
            continue
        states = spec_data.get("distinct_states")
        if not isinstance(states, int):
            continue
        has_error = bool(spec_data.get("has_error", False))
        error_type = spec_data.get("error_type") if has_error else None
        tlc_status = "error" if has_error else "pass"
        runtime_seconds = None
        stats = spec_data.get("runtime_stats") or {}
        if isinstance(stats, dict) and isinstance(stats.get("median_seconds"), (int, float)):
            runtime_seconds = round(float(stats["median_seconds"]), 2)
        out[name] = {
            "tlc": {
                "status": tlc_status,
                "states": states,
                "runtime_seconds": runtime_seconds,
                "error_type": error_type,
                "error": None,
            },
            "tla2": make_untested_tla2_entry(),
            "verified_match": False,
            "category": categorize_runtime(runtime_seconds),
            "source": "expected_results.json",
        }
    return out


def compute_stats(baselines: dict) -> OrderedDict:
    """Compute status statistics with deterministic key ordering."""
    counts = {k: 0 for k in STATS_KEY_ORDER}
    for data in baselines.values():
        tlc_status = (data.get("tlc") or {}).get("status") or data.get("status") or "unknown"
        if tlc_status == "pass":
            counts["tlc_pass"] += 1
        elif tlc_status == "timeout":
            counts["tlc_timeout"] += 1
        else:
            counts["tlc_error"] += 1

        tla2 = data.get("tla2")
        if not isinstance(tla2, dict):
            counts["tla2_untested"] += 1
            continue

        tla2_status = tla2.get("status") or "untested"
        if tla2_status == "pass" and data.get("verified_match") is True:
            counts["tla2_match"] += 1
        elif tla2_status == "mismatch":
            counts["tla2_mismatch"] += 1
        elif tla2_status == "fail":
            counts["tla2_fail"] += 1
        else:
            counts["tla2_untested"] += 1

    return OrderedDict((k, counts[k]) for k in STATS_KEY_ORDER)


def compute_categories(baselines: dict) -> OrderedDict:
    """Compute category statistics with deterministic key ordering."""
    counts = {}
    for data in baselines.values():
        category = data.get("category", "unknown")
        counts[category] = counts.get(category, 0) + 1
    result = OrderedDict()
    for k in CATEGORIES_KEY_ORDER:
        result[k] = counts.pop(k, 0)
    for k in sorted(counts.keys()):
        result[k] = counts[k]
    return result


def validate_baselines(baselines: dict) -> list[str]:
    """Check for data quality anomalies in baseline entries."""
    warnings = []
    for name, data in baselines.items():
        tlc = data.get("tlc") or {}
        tlc_status = tlc.get("status", "unknown")
        tlc_states = tlc.get("states")

        if tlc_status == "pass" and tlc_states is None:
            warnings.append(
                f"{name}: TLC status=pass but states=null — state count not parsed"
            )

        tlc_error_type = tlc.get("error_type")
        if tlc_status == "pass" and tlc_error_type not in (None, "unknown"):
            warnings.append(
                f"{name}: TLC status=pass but error_type={tlc_error_type} — "
                f"status should likely be 'error'"
            )

    return warnings


def order_spec_entry(entry: dict) -> OrderedDict:
    """Order spec entry keys for deterministic output."""
    if "tlc" not in entry or not isinstance(entry.get("tlc"), dict):
        legacy_v2_keys = {
            "expected_states",
            "tlc_runtime_seconds",
            "status",
            "error",
            "error_type",
        }
        tlc = {
            "status": entry.get("status", "unknown"),
            "states": entry.get("expected_states"),
            "runtime_seconds": entry.get("tlc_runtime_seconds"),
            "error_type": entry.get("error_type"),
            "error": entry.get("error"),
        }
        out = {
            "tlc": tlc,
            "tla2": make_untested_tla2_entry(),
            "verified_match": False,
            "category": entry.get("category", "unknown"),
        }
        if "source" in entry:
            out["source"] = entry.get("source")
        for k, v in entry.items():
            if k in out or k in legacy_v2_keys:
                continue
            out[k] = v
        entry = out

    result = OrderedDict()
    for k in SPEC_ENTRY_KEY_ORDER:
        if k in entry:
            if k == "tlc" and isinstance(entry.get("tlc"), dict):
                tlc = entry["tlc"]
                ordered = OrderedDict((kk, tlc.get(kk)) for kk in TLC_ENTRY_KEY_ORDER if kk in tlc)
                for kk in sorted(tlc.keys()):
                    if kk not in ordered:
                        ordered[kk] = tlc[kk]
                result[k] = ordered
            elif k == "tla2" and isinstance(entry.get("tla2"), dict):
                tla2 = entry["tla2"]
                ordered = OrderedDict((kk, tla2.get(kk)) for kk in TLA2_ENTRY_KEY_ORDER if kk in tla2)
                for kk in sorted(tla2.keys()):
                    if kk not in ordered:
                        ordered[kk] = tla2[kk]
                result[k] = ordered
            else:
                result[k] = entry[k]
    for k in sorted(entry.keys()):
        if k not in result:
            result[k] = entry[k]
    return result


def build_ordered_specs(baselines: dict) -> OrderedDict:
    """Build specs dict ordered by ALL_SPECS catalog order, then extras sorted."""
    result = OrderedDict()
    all_spec_names = {spec.name for spec in ALL_SPECS}

    for spec in ALL_SPECS:
        if spec.name in baselines:
            result[spec.name] = order_spec_entry(baselines[spec.name])

    extra_names = sorted(k for k in baselines.keys() if k not in all_spec_names)
    for name in extra_names:
        result[name] = order_spec_entry(baselines[name])

    return result


def write_output(path: Path, *, baselines: dict, provenance: OrderedDict):
    """Write baseline output with deterministic key ordering and provenance."""
    anomalies = validate_baselines(baselines)
    for warning in anomalies:
        print(f"WARNING: baseline anomaly: {warning}", file=sys.stderr)

    stats = compute_stats(baselines)
    categories = compute_categories(baselines)
    ordered_specs = build_ordered_specs(baselines)
    specs_jcs_sha256 = sha256_jcs(ordered_specs)

    output = OrderedDict()
    output["schema_version"] = provenance.get("schema_version", 1)
    output["generated"] = datetime.now().isoformat()
    output["collector"] = provenance.get("collector", OrderedDict())
    output["tlc"] = provenance.get("tlc", OrderedDict())
    output["inputs"] = provenance.get("inputs", OrderedDict())
    output["seed"] = provenance.get("seed", OrderedDict())
    output["tlc_timeout_seconds"] = provenance.get("tlc_timeout_seconds", 600)

    output["total_specs"] = len(ALL_SPECS)
    output["specs_jcs_sha256"] = specs_jcs_sha256
    output["stats"] = stats
    output["categories"] = categories
    output["specs"] = ordered_specs

    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w") as f:
        json.dump(output, f, indent=2)
    os.replace(tmp, path)
