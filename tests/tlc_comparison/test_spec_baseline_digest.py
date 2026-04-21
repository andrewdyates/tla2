# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

import json
import sys
from pathlib import Path

import pytest

@pytest.mark.no_tla2_build
def test_spec_baseline_specs_digest_matches() -> None:
    scripts_dir = Path(__file__).resolve().parents[2] / "scripts"
    sys.path.insert(0, str(scripts_dir))
    from json_jcs import sha256_jcs  # noqa: PLC0415

    baseline_path = Path(__file__).parent / "spec_baseline.json"
    data = json.loads(baseline_path.read_text())
    assert isinstance(data.get("specs"), dict)
    assert isinstance(data.get("schema_version"), int)
    assert data["schema_version"] >= 3

    digest = data.get("specs_jcs_sha256")
    assert isinstance(digest, str) and len(digest) == 64
    assert sha256_jcs(data["specs"]) == digest

    # Schema v3 invariants: TLC results are namespaced under .specs.<name>.tlc
    for name, spec in data["specs"].items():
        assert isinstance(spec, dict), name
        assert "expected_states" not in spec, name
        assert "tlc_runtime_seconds" not in spec, name
        assert "status" not in spec, name
        assert isinstance(spec.get("tlc"), dict), name
        assert "states" in spec["tlc"], name
        assert isinstance(spec.get("tla2"), dict), name
        assert spec["tla2"].get("status") in {"untested", "pass", "mismatch", "fail"}, name
        assert spec.get("verified_match") in {True, False}, name

    # Verified match implies a passing run (schema v3).
    for name, spec in data["specs"].items():
        if spec.get("verified_match") is True:
            assert spec["tla2"].get("status") == "pass", name
        if spec["tla2"].get("status") in {"mismatch", "fail"}:
            assert spec.get("verified_match") is False, name

    stats = data.get("stats") or {}
    mismatch_count = sum(
        1
        for spec in data["specs"].values()
        if spec.get("tla2", {}).get("status") == "mismatch"
    )
    assert stats.get("tla2_mismatch", 0) == mismatch_count
