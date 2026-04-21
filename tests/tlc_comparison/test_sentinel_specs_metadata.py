# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

import json
from pathlib import Path

import pytest


def _load_sentinel_specs() -> list[str]:
    path = Path(__file__).parent / "sentinel_specs.txt"
    specs: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        specs.append(line)
    return specs


def _load_spec_baseline() -> dict:
    path = Path(__file__).parent / "spec_baseline.json"
    if not path.exists():
        return {"specs": {}}
    return json.loads(path.read_text(encoding="utf-8"))


@pytest.mark.no_tla2_build
def test_sentinel_specs_are_verified_matches() -> None:
    """Sentinel specs must be known-good exact matches (no stale optimism)."""
    baseline = _load_spec_baseline()
    specs = baseline.get("specs", {})

    for name in _load_sentinel_specs():
        entry = specs.get(name)
        assert isinstance(entry, dict), f"sentinel spec missing from spec_baseline.json: {name}"
        assert entry.get("verified_match") is True, (
            f"sentinel spec is not a verified match (verified_match!=true): {name}"
        )
        tlc = entry.get("tlc")
        assert isinstance(tlc, dict), f"sentinel spec missing tlc entry: {name}"
        assert tlc.get("status") == "pass", f"sentinel spec TLC status is not pass: {name}"

