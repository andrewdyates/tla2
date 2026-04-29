# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Regression test for #1048: missing module via named INSTANCE.

Both TLC and TLA2 should fail at parse/semantic stage when a named instance
references a module that doesn't exist.
"""

from pathlib import Path

import pytest

from .conftest import run_tla2, run_tlc


@pytest.mark.timeout(120)
def test_missing_module_named_instance_both_fail() -> None:
    """Verify TLC and TLA2 both fail for missing module via named INSTANCE.

    The spec uses `I == INSTANCE Missing` which is valid syntax (unlike INSTANCE
    in expression positions), but the module 'Missing' doesn't exist.

    Both checkers should:
    - Report an error (has_error=True)
    - Classify as parse/semantic error
    """
    repro_dir = (
        Path(__file__).resolve().parent
        / "repros"
        / "missing_module_named_instance_1048"
    )
    spec = repro_dir / "MissingModuleInstance.tla"
    cfg = repro_dir / "MissingModuleInstance.cfg"

    # TLC should fail with parse/semantic error
    tlc = run_tlc(spec, cfg, timeout=60)
    assert tlc.has_error, f"Expected TLC to report an error:\n{tlc.raw_output}"
    assert tlc.error_type == "parse", (
        f"Expected TLC parse error, got error_type={tlc.error_type}\n"
        f"Output:\n{tlc.raw_output}"
    )
    # TLC says "Cannot find source file for module Missing"
    assert "Missing" in tlc.raw_output, (
        f"Expected TLC to mention missing module name:\n{tlc.raw_output}"
    )

    # TLA2 should fail with same error type
    tla2 = run_tla2(spec, cfg, timeout=60)
    assert tla2.has_error, f"Expected TLA2 to report an error:\n{tla2.raw_output}"
    assert tla2.error_type == tlc.error_type, (
        f"Error type mismatch: TLC={tlc.error_type}, TLA2={tla2.error_type}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )
    # TLA2 says "Module 'Missing' not found"
    assert "Missing" in tla2.raw_output, (
        f"Expected TLA2 to mention missing module name:\n{tla2.raw_output}"
    )
