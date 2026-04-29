# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Regression test for #406: Sequential LET shadowing in state_var pass
#
# Tests that TLA2 handles sequential LET scoping correctly when LET def
# names collide with state variable names.
#
# NOTE: TLC/SANY rejects this spec with "Operator x already defined or declared"
# because SANY doesn't allow LET definitions to shadow module-level VARIABLEs.
# TLA2 is more permissive and accepts this spec. This test verifies TLA2's
# handling is correct (y=1, not y=0 from incorrect StateVar conversion).
#
# A separate issue should track adding SANY-compatible semantic validation to TLA2.

import subprocess
from pathlib import Path

import pytest


SPEC_DIR = Path(__file__).parent
SPEC = SPEC_DIR / "LetShadow.tla"
CONFIG = SPEC_DIR / "LetShadow.cfg"


def run_tla2(spec: Path, config: Path) -> subprocess.CompletedProcess:
    """Run TLA2 model checker."""
    tla2_bin = Path(__file__).parents[4] / "target" / "release" / "tla2"
    return subprocess.run(
        [str(tla2_bin), "check", str(spec), "--config", str(config)],
        capture_output=True,
        text=True,
        timeout=60,
    )


def test_let_shadow_tla2_success():
    """TLA2 should succeed with sequential LET shadowing.

    The invariant `LET x == 1, y == x IN y = 1` should pass because:
    - `x == 1` defines a local LET operator (shadowing state var x)
    - `y == x` references the LET-defined x (value 1), not state var x (value 0)
    - `y = 1` is TRUE

    Without the #406 fix, state_var.rs might convert the `x` in `y == x` to
    StateVar(x), making y=0 and the invariant fail.
    """
    result = run_tla2(SPEC, CONFIG)
    # Check for success (no invariant violation)
    assert result.returncode == 0, f"TLA2 failed with code {result.returncode}: {result.stdout}\n{result.stderr}"
    assert "No errors found" in result.stdout, f"Expected success: {result.stdout}"


def test_let_shadow_state_count():
    """TLA2 should find exactly 1 state (simple stuttering spec)."""
    result = run_tla2(SPEC, CONFIG)
    assert "States found: 1" in result.stdout, f"Expected 1 state: {result.stdout}"


def test_tlc_rejects_this_spec():
    """Document that TLC rejects this spec (semantic error).

    SANY doesn't allow LET definitions to shadow module-level VARIABLEs.
    This test documents the divergence - see issue for TLA2 semantic validation.
    """
    tlc_jar = Path.home() / "tlaplus" / "tla2tools.jar"
    result = subprocess.run(
        ["java", "-jar", str(tlc_jar), "-config", str(CONFIG), str(SPEC)],
        capture_output=True,
        text=True,
        timeout=60,
        cwd=SPEC.parent,
    )
    # TLC should fail with semantic error
    assert result.returncode != 0, "TLC should reject this spec"
    assert "already defined" in result.stderr, f"Expected 'already defined' error: {result.stderr}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
