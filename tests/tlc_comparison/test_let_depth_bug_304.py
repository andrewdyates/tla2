# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from pathlib import Path

import pytest

from .conftest import run_tla2, run_tlc


@pytest.mark.timeout(120)
def test_304_let_binding_depth_matches_tlc():
    """Regression test for #304: LET binding depth bug in compiled guards."""
    repo_root = Path(__file__).parent.parent.parent
    spec = repo_root / "tests" / "specs" / "bug_repro" / "TestLETDepthBug.tla"
    cfg = repo_root / "tests" / "specs" / "bug_repro" / "TestLETDepthBug.cfg"

    assert spec.exists(), f"Spec not found: {spec}"
    assert cfg.exists(), f"Config not found: {cfg}"

    tlc = run_tlc(spec, cfg, timeout=60)
    tla2 = run_tla2(spec, cfg, timeout=60)

    assert not tlc.has_error, f"TLC error:\n{tlc.raw_output}"
    assert not tla2.has_error, f"TLA2 error:\n{tla2.raw_output}"

    assert tlc.distinct_states == 4, (
        f"TLC baseline changed! Expected 4, got {tlc.distinct_states}\n"
        f"Output:\n{tlc.raw_output}"
    )
    assert tla2.distinct_states == tlc.distinct_states, (
        "State count mismatch vs TLC\n"
        f"TLC distinct:  {tlc.distinct_states}\n"
        f"TLA2 distinct: {tla2.distinct_states}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )

