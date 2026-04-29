# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""
Regression test for #392/#418: LazyFuncValue and SetPredValue must capture
state_env at definition time (TLC parity).
"""

from pathlib import Path

import pytest

from .conftest import run_tla2, run_tlc


@pytest.mark.timeout(60)
def test_lazy_values_capture_state_env() -> None:
    """TLC and TLA2 must agree when lazy values (function and set filter) outlive their defining state."""
    repro_dir = Path(__file__).parent / "repros" / "lazy_capture_392_418"
    spec = repro_dir / "TestLazyCapture.tla"
    config = repro_dir / "TestLazyCapture.cfg"

    tlc = run_tlc(spec, config, timeout=30)
    tla2 = run_tla2(spec, config, timeout=30)

    assert tlc.error_type != "parse", f"TLC parse error:\n{tlc.raw_output}"
    assert tlc.has_error is False, f"TLC error:\n{tlc.raw_output}"
    assert tla2.has_error is False, f"TLA2 error:\n{tla2.raw_output}"

    # Spec has exactly two states: Init (x=0) and Next (x=1).
    assert tlc.distinct_states == 2, f"TLC distinct states: {tlc.distinct_states}\n{tlc.raw_output}"
    assert tlc.distinct_states == tla2.distinct_states, (
        f"State count mismatch: TLC={tlc.distinct_states}, TLA2={tla2.distinct_states}\n\n"
        f"--- TLC ---\n{tlc.raw_output}\n\n--- TLA2 ---\n{tla2.raw_output}"
    )

