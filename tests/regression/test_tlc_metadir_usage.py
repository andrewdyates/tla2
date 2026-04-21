# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Regression test for #976: prevent TLC ./states disk bloat in repo trees.
#
# We want TLC runs (from our scripts) to use an ephemeral -metadir by default,
# and only write ./states when explicitly requested (TLA2_KEEP_STATES=1).

from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]

SOURCE_GROUPS = {
    "verify_correctness": [
        PROJECT_ROOT / "scripts" / "verify_correctness.sh",
        PROJECT_ROOT / "scripts" / "lib" / "verify_correctness" / "runners.sh",
    ],
    "compare_with_tlc": [PROJECT_ROOT / "scripts" / "compare_with_tlc.sh"],
    "collect_tlc_baseline": [
        PROJECT_ROOT / "scripts" / "collect_tlc_baseline.py",
        PROJECT_ROOT / "scripts" / "collect_tlc_baseline" / "tlc_runner.py",
    ],
    "differential_test": [PROJECT_ROOT / "scripts" / "differential_test.sh"],
    "differential_test_v2": [PROJECT_ROOT / "scripts" / "differential_test_v2.sh"],
    "test_all_liveness": [PROJECT_ROOT / "scripts" / "test_all_liveness.sh"],
}

PRESERVE_SOURCE_GROUPS = {
    "verify_correctness",
    "compare_with_tlc",
    "collect_tlc_baseline",
}


def read_source_group(paths: list[Path]) -> str:
    return "\n".join(path.read_text(encoding="utf-8") for path in paths)


def test_tlc_runs_use_ephemeral_metadir_by_default() -> None:
    for name, paths in SOURCE_GROUPS.items():
        text = read_source_group(paths)
        assert "-metadir" in text, f"{name} should pass -metadir to TLC by default"
        assert (
            "TLA2_KEEP_STATES" in text
        ), f"{name} should allow opting into keeping ./states via TLA2_KEEP_STATES=1"
        if name in PRESERVE_SOURCE_GROUPS:
            assert (
                "TLA2_PRESERVE_STATES_DIR" in text
            ), f"{name} should allow preserving any existing ./states via TLA2_PRESERVE_STATES_DIR=1"
