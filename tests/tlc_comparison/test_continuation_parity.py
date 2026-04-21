# Copyright 2026 Andrew Yates.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""
Continuation Parity Tests

Verifies continuation-passing successor enumeration matches the default path exactly.
"""

import pytest
from .conftest import run_tla2


# Comprehensive set of specs covering different TLA+ patterns:
# - MCBakery: Complex multi-process mutual exclusion with Or branches
# - EnabledInAction: ENABLED operator in action context
# - OperatorReplacementPrimeTest: Operator expansion with primed variables
# - TokenRing: Larger state space (46k states)
# - SubSeqExceptTest: Sequence operators with EXCEPT
# - FunctionOverrideTest: Function domain/codomain with EXCEPT
# - test1-test10: Basic operator and expression patterns
PARITY_SPECS = [
    "MCBakery.tla",
    "EnabledInAction.tla",
    "OperatorReplacementPrimeTest.tla",
    "TokenRing.tla",
    "SubSeqExceptTest.tla",
    "FunctionOverrideTest.tla",
    "test1.tla",
    "test2.tla",
    "test3.tla",
    "test4.tla",
    "test5.tla",
    "test6.tla",
    "test7.tla",
    "test8.tla",
    "test9.tla",
    "test10.tla",
]


@pytest.mark.parametrize("spec_name", PARITY_SPECS)
def test_continuation_matches_non_continuation(test_specs_dir, spec_name):
    """Verify continuation-passing (default) produces identical results to non-continuation path."""
    spec = test_specs_dir / spec_name
    if not spec.exists():
        pytest.fail(f"Spec not found: {spec}")

    # Default path uses continuation (enabled by default)
    cont = run_tla2(spec)
    # Disable continuation with TLA2_NO_CONTINUATION=1
    no_cont = run_tla2(spec, extra_env={"TLA2_NO_CONTINUATION": "1"})

    assert cont.has_error == no_cont.has_error, (
        f"Error mismatch: cont={cont.has_error}, no_cont={no_cont.has_error}"
    )
    assert cont.error_type == no_cont.error_type, (
        f"Error type mismatch: cont={cont.error_type}, no_cont={no_cont.error_type}"
    )
    assert cont.states == no_cont.states, (
        f"State mismatch: cont={cont.states}, no_cont={no_cont.states}"
    )
