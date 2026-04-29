# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Author: Andrew Yates <andrewyates.name@gmail.com>

from pathlib import Path
import re

import pytest

from .conftest import run_tla2, run_tlc


@pytest.mark.timeout(600)
def test_bitwise_and_in_set_filter_matches_tlc():
    repro_dir = Path(__file__).parent / "repros" / "bitand_set_pred"
    spec = repro_dir / "test_bitand2.tla"
    cfg = repro_dir / "test_bitand2.cfg"

    tlc = run_tlc(spec, cfg, timeout=60)
    tla2 = run_tla2(spec, cfg, timeout=60, extra_env={"TLA2_NO_COMPILED_ACTION": "1"})

    assert not tlc.has_error, f"TLC error:\n{tlc.raw_output}"
    assert not tla2.has_error, f"TLA2 error:\n{tla2.raw_output}"

    assert tlc.distinct_states == 2, f"Unexpected TLC baseline:\n{tlc.raw_output}"
    assert tla2.distinct_states == tlc.distinct_states, (
        "State count mismatch vs TLC\n"
        f"TLC distinct:  {tlc.distinct_states}\n"
        f"TLA2 distinct: {tla2.distinct_states}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )


@pytest.mark.timeout(120)
def test_376_inline_bitwise_and_set_filter():
    """Regression test for #376: Bitwise AND in set comprehension predicates.

    Tests the INLINE version (RECURSIVE+LET defined in same module).
    This is the core #376 fix - the EXTENDS variant (#399) is separate.

    Verifies:
    1. SetOfPowerOfTwo(3) = {1, 2, 4} matches TLC
    2. State count matches TLC exactly
    3. Init and Next both produce same SetOfPowerOfTwo result

    Part of #376 - regression coverage for Init-vs-Next set comprehension.
    """
    repo_root = Path(__file__).parent.parent.parent
    spec = repo_root / "tests" / "regression" / "p0_repro" / "test_376_bits.tla"
    cfg = repo_root / "tests" / "regression" / "p0_repro" / "test_376_bits.cfg"

    assert spec.exists(), f"Spec not found: {spec}"
    assert cfg.exists(), f"Config not found: {cfg}"

    tlc = run_tlc(spec, cfg, timeout=60)
    tla2 = run_tla2(spec, cfg, timeout=60, extra_env={"TLA2_NO_COMPILED_ACTION": "1"})

    # Both should succeed without errors
    assert not tlc.has_error, f"TLC error:\n{tlc.raw_output}"
    assert not tla2.has_error, f"TLA2 error:\n{tla2.raw_output}"

    # Verify TLC baseline (4 states: 0, 1, 2, 4)
    assert tlc.distinct_states == 4, (
        f"TLC baseline changed! Expected 4, got {tlc.distinct_states}\n"
        f"Output:\n{tlc.raw_output}"
    )

    # State count must match exactly
    assert tla2.distinct_states == tlc.distinct_states, (
        f"#376 REGRESSION: State count mismatch\n"
        f"TLC distinct:  {tlc.distinct_states}\n"
        f"TLA2 distinct: {tla2.distinct_states}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )

    # Verify SetOfPowerOfTwo(3) = {1, 2, 4} appears in TLA2 output
    # This checks that the set comprehension filter works correctly
    assert "{1, 2, 4}" in tla2.raw_output, (
        f"#376 REGRESSION: SetOfPowerOfTwo(3) should be {{1, 2, 4}}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )

    def parse_transitions(output: str) -> int | None:
        match = re.search(r"^\s*Transitions:\s*(\d+)\s*$", output, re.MULTILINE)
        return int(match.group(1)) if match else None

    def parse_printed_next_values(output: str) -> list[int]:
        # Matches lines like: TLC Print: <<"Next: d =", 2>>
        return [
            int(m.group(1))
            for m in re.finditer(r'Next: d =",\s*(\d+)\b', output)
        ]

    def parse_printed_set_values(output: str) -> list[str]:
        # Matches lines like: TLC Print: <<"Init: SetOfPowerOfTwo(3) =", {1, 2, 4}>>
        return [
            m.group(1)
            for m in re.finditer(
                r'Init: SetOfPowerOfTwo\(3\) =",\s*(\{[^}]+\})',
                output,
            )
        ]

    # Strengthen verification: ensure transition count is sane and printed values are correct.
    tla2_transitions = parse_transitions(tla2.raw_output)
    assert tla2_transitions is not None, f"Failed to parse TLA2 transitions:\n{tla2.raw_output}"
    assert tla2_transitions == 12, (
        f"#376 REGRESSION: Unexpected transition count (should be 12)\n"
        f"TLA2 transitions: {tla2_transitions}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )

    printed_sets = parse_printed_set_values(tla2.raw_output)
    assert printed_sets, (
        f"#376 REGRESSION: Expected Init to PrintT SetOfPowerOfTwo(3)\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )
    assert all(s == "{1, 2, 4}" for s in printed_sets), (
        f"#376 REGRESSION: Init printed unexpected SetOfPowerOfTwo(3)\n"
        f"Printed: {printed_sets}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )

    next_values = parse_printed_next_values(tla2.raw_output)
    assert next_values, (
        f"#376 REGRESSION: Expected Next to PrintT chosen d values\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )
    assert set(next_values).issubset({1, 2, 4}), (
        f"#376 REGRESSION: Next printed unexpected d values\n"
        f"Printed values: {sorted(set(next_values))}\n"
        f"TLA2 output:\n{tla2.raw_output}"
    )
