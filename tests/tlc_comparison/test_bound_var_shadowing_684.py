# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""
Regression test for #684: Bound identifiers inside an extended module must
not be accidentally resolved to same-named constants in the extending module.

This is the exact pattern in tlaplus-examples Paxos: Voting.tla defines
OneValuePerBallot using bound identifiers a1/a2/v1/v2, while MCVoting.tla
declares constants a1/a2/v1/v2.
"""

from pathlib import Path

import pytest

from .conftest import run_tla2, run_tlc


@pytest.mark.timeout(60)
def test_bound_vars_do_not_capture_extending_module_constants() -> None:
    repro_dir = Path(__file__).parent / "repros" / "bound_var_shadowing_684"
    spec = repro_dir / "ShadowTest.tla"
    config = repro_dir / "ShadowTest.cfg"

    # When a spec violates an invariant, early-stop behavior (and thus partial
    # state counts) can be order-dependent. Run both checkers in "continue"
    # mode so we compare full exploration counts (TLC parity).
    tlc = run_tlc(spec, config, timeout=30, continue_on_error=True)
    tla2 = run_tla2(spec, config, timeout=30, continue_on_error=True)

    assert tlc.error_type != "parse", f"TLC parse error:\n{tlc.raw_output}"
    assert tla2.error_type != "parse", f"TLA2 parse error:\n{tla2.raw_output}"

    assert tlc.has_error is True, f"Expected TLC to find an invariant violation:\n{tlc.raw_output}"
    assert tla2.has_error is True, f"Expected TLA2 to find an invariant violation:\n{tla2.raw_output}"
    assert tlc.error_type == "invariant", f"TLC error type: {tlc.error_type}\n{tlc.raw_output}"
    assert tla2.error_type == "invariant", f"TLA2 error type: {tla2.error_type}\n{tla2.raw_output}"

    # Spec has 16 distinct states total.
    assert tlc.distinct_states == 16, f"TLC distinct states: {tlc.distinct_states}\n{tlc.raw_output}"
    assert tlc.distinct_states == tla2.distinct_states, (
        f"State count mismatch: TLC={tlc.distinct_states}, TLA2={tla2.distinct_states}\n\n"
        f"--- TLC ---\n{tlc.raw_output}\n\n--- TLA2 ---\n{tla2.raw_output}"
    )
