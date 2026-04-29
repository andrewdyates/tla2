# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from pathlib import Path
import re
from collections import Counter
from typing import Optional, Tuple

import pytest

from .conftest import run_tla2, run_tlc


def _normalize_model_values(s: str) -> str:
    # TLA2 currently prints model values with an '@' sigil (e.g. "@A").
    # TLC prints model values without a sigil (e.g. "A").
    # Normalize away the sigil so this test checks semantic witness parity.
    return re.sub(r"@([A-Za-z0-9_]+)", r"\1", s)


def _split_tla_comma_separated(s: str) -> list[str]:
    """Split a TLA+ pretty-printed comma list at top-level commas.

    Used for canonicalizing sets that may contain tuples, e.g.:
      {<<A, 1>>, <<B, 2>>}
    """
    parts: list[str] = []
    start = 0
    i = 0
    brace = 0
    bracket = 0
    paren = 0
    tuple_depth = 0

    while i < len(s):
        if s.startswith("<<", i):
            tuple_depth += 1
            i += 2
            continue
        if s.startswith(">>", i) and tuple_depth > 0:
            tuple_depth -= 1
            i += 2
            continue

        ch = s[i]
        if ch == "{":
            brace += 1
        elif ch == "}":
            brace = max(0, brace - 1)
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            bracket = max(0, bracket - 1)
        elif ch == "(":
            paren += 1
        elif ch == ")":
            paren = max(0, paren - 1)
        elif ch == "," and brace == 0 and bracket == 0 and paren == 0 and tuple_depth == 0:
            parts.append(s[start:i].strip())
            start = i + 1
        i += 1

    tail = s[start:].strip()
    if tail:
        parts.append(tail)
    return parts


def _canonicalize_value(s: str) -> str:
    s = _normalize_model_values(s).strip()
    if s.startswith("{") and s.endswith("}"):
        inner = s[1:-1].strip()
        if not inner:
            return "{}"
        elems = [e for e in _split_tla_comma_separated(inner) if e]
        return "{%s}" % (", ".join(sorted(elems)))
    return s


# Related repro for #1004:
#   tests/tlc_comparison/repros/choose_witness_tuples_mv/ChooseWitnessTuplesMV.tla


def _parse_print_value(output: str, key: str) -> str:
    # Both TLC and TLA2 print a tuple per PrintT call, on its own line, like:
    #   <<"MV_CHOOSE", A>>
    # Capture the value after the string key.
    pattern = rf'^\s*<<\s*"{re.escape(key)}",\s*(.+?)\s*>>\s*$'
    matches = re.findall(pattern, output, flags=re.MULTILINE)
    assert matches, f"Missing PrintT({key!r}) output:\n{output}"
    assert len(matches) == 1, f"Expected exactly one PrintT({key!r}) line, got {len(matches)}:\n{output}"
    return _canonicalize_value(matches[0].strip())


@pytest.mark.timeout(120)
def test_choose_witness_993_model_values_and_subset_order_matches_tlc():
    """Regression test for #993: CHOOSE witness parity (model values + SUBSET domains).

    Verifies that the CHOOSE witness printed by Init matches Java TLC exactly.
    """
    repro_dir = Path(__file__).resolve().parent / "repros" / "choose_witness_993"
    spec = (repro_dir / "ChooseWitness993.tla").resolve()
    cfg = (repro_dir / "ChooseWitness993.cfg").resolve()

    tlc = run_tlc(spec, cfg, timeout=60)

    assert not tlc.has_error, f"TLC error:\n{tlc.raw_output}"
    assert tlc.distinct_states == 1, f"Unexpected TLC baseline:\n{tlc.raw_output}"

    tlc_mv = _parse_print_value(tlc.raw_output, "MV_CHOOSE")
    tlc_subset2 = _parse_print_value(tlc.raw_output, "MV_SUBSET2_CHOOSE")

    trials = 20
    outcomes: Counter = Counter()
    first_mismatch: Optional[Tuple[int, str, str, str]] = None

    for i in range(trials):
        tla2 = run_tla2(spec, cfg, timeout=60, extra_env={"TLA2_NO_COMPILED_ACTION": "1"})
        assert not tla2.has_error, f"TLA2 error:\n{tla2.raw_output}"
        assert tla2.distinct_states == tlc.distinct_states, (
            "State count mismatch vs TLC\n"
            f"TLC distinct:  {tlc.distinct_states}\n"
            f"TLA2 distinct: {tla2.distinct_states}\n"
            f"TLA2 output:\n{tla2.raw_output}"
        )

        tla2_mv = _parse_print_value(tla2.raw_output, "MV_CHOOSE")
        tla2_subset2 = _parse_print_value(tla2.raw_output, "MV_SUBSET2_CHOOSE")
        outcomes[(tla2_mv, tla2_subset2)] += 1

        if (tla2_mv, tla2_subset2) != (tlc_mv, tlc_subset2) and first_mismatch is None:
            first_mismatch = (i, tla2_mv, tla2_subset2, tla2.raw_output)

    if first_mismatch is None:
        return

    mismatch_i, tla2_mv, tla2_subset2, tla2_output = first_mismatch
    observed = "\n".join(
        f"  {mv}, {subset2}: {count}"
        for (mv, subset2), count in outcomes.most_common()
    )
    pytest.fail(
        "CHOOSE witness mismatch vs TLC (witness differs; may be non-deterministic across runs).\n"
        f"  TLC MV_CHOOSE:        {tlc_mv}\n"
        f"  TLC MV_SUBSET2_CHOOSE:{tlc_subset2}\n"
        f"\nFirst mismatch at trial {mismatch_i + 1}/{trials}:\n"
        f"  TLA2 MV_CHOOSE:        {tla2_mv}\n"
        f"  TLA2 MV_SUBSET2_CHOOSE:{tla2_subset2}\n"
        f"\nObserved TLA2 outcomes across {trials} runs:\n{observed}\n"
        + "\n--- TLC output ---\n"
        + tlc.raw_output
        + "\n\n--- TLA2 output (first mismatch) ---\n"
        + tla2_output,
    )
