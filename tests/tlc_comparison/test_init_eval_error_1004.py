# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from pathlib import Path

import pytest

from .conftest import run_tla2, run_tlc


@pytest.mark.timeout(120)
def test_init_eval_error_model_value_apply_surfaces_as_error_1004() -> None:
    """Regression test for #1004: Init evaluation errors must be reported.

    Applying a model value as a function during Init should be a fatal error (matching TLC),
    not treated as an unsatisfied constraint that yields "Init predicate has no solutions".

    Also verifies that evaluation stops at the error point (no post-error Print()).
    """

    repro_dir = Path(__file__).resolve().parent / "repros" / "init_eval_error_model_value_apply_1004"
    spec = repro_dir / "InitEvalErrorModelValueApply.tla"
    cfg = repro_dir / "InitEvalErrorModelValueApply.cfg"

    tlc = run_tlc(spec, cfg, timeout=60)
    assert tlc.has_error, f"Expected TLC to report an error:\n{tlc.raw_output}"
    assert "Should never get this far" not in tlc.raw_output

    tla2 = run_tla2(spec, cfg, timeout=60, extra_env={"TLA2_NO_COMPILED_ACTION": "1"})
    assert tla2.has_error, f"Expected TLA2 to report an error:\n{tla2.raw_output}"
    assert tla2.error_type == tlc.error_type, (
        "TLA2/TLC error classification mismatch.\n"
        f"TLC error_type={tlc.error_type}\n"
        f"TLA2 error_type={tla2.error_type}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )

    # Core bug: TLA2 used to swallow the eval error and claim Init has no solutions.
    assert "Init predicate has no solutions" not in tla2.raw_output

    # Parity with TLC: stop at the error point.
    assert "Should never get this far" not in tla2.raw_output

