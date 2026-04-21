# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from pathlib import Path

import pytest

from .conftest import run_tla2, run_tlc


@pytest.mark.timeout(120)
def test_floor_division_and_mod_matches_tlc():
    """Regression test for #631: Integer \\div and % must use floor-division semantics.

    Verifies BOTH:
    - (-3 \\div 2) = -2
    - (-3 % 2) = 1

    by checking an invariant that TLC should satisfy and requiring TLA2 to match.
    """
    repro_dir = Path(__file__).parent / "repros" / "floor_division_631"
    spec = repro_dir / "TestFloorDiv631.tla"
    cfg = repro_dir / "TestFloorDiv631.cfg"

    tlc = run_tlc(spec, cfg, timeout=60)
    tla2 = run_tla2(spec, cfg, timeout=60)

    assert not tlc.has_error, f"TLC error:\n{tlc.raw_output}"
    assert not tla2.has_error, f"TLA2 error:\n{tla2.raw_output}"

    assert tlc.distinct_states == 1, f"Unexpected TLC baseline:\n{tlc.raw_output}"
    assert tla2.distinct_states == tlc.distinct_states, (
        "State count mismatch vs TLC\n"
        f"TLC distinct:  {tlc.distinct_states}\n"
        f"TLA2 distinct: {tla2.distinct_states}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )
