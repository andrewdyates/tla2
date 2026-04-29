# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

import subprocess
import textwrap
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
HELPERS = PROJECT_ROOT / "scripts" / "liveness_harness_common.sh"


def _evaluate_gate(
    *,
    tlc_output: str,
    tla2_output: str,
    tlc_rc: int = 0,
    tla2_rc: int = 0,
    tlc_states: str = "",
    tla2_states: str = "",
) -> dict[str, str]:
    script = textwrap.dedent(
        f"""
        set -euo pipefail
        source "{HELPERS}"

        tlc_output=$(cat <<'TLC'
        {tlc_output}
        TLC
        )
        tla2_output=$(cat <<'TLA2'
        {tla2_output}
        TLA2
        )

        tlc_status="$(classify_tlc_status "$tlc_output" {tlc_rc})"
        tla2_status="$(classify_tla2_status "$tla2_output" {tla2_rc})"

        echo "tlc_status=$tlc_status"
        echo "tla2_status=$tla2_status"
        evaluate_liveness_gate "$tlc_status" "$tla2_status" "{tlc_states}" "{tla2_states}"
        """
    )

    result = subprocess.run(
        ["bash", "-lc", script],
        check=True,
        text=True,
        capture_output=True,
    )

    parsed: dict[str, str] = {}
    for line in result.stdout.splitlines():
        for item in line.split("|"):
            if "=" not in item:
                continue
            key, value = item.split("=", 1)
            parsed[key.strip()] = value.strip()
    return parsed


def test_system_loop_no_fair_verdict_mismatch_fails_even_when_states_match() -> None:
    # Regression for #1530: old state-only logic would have passed this row.
    parsed = _evaluate_gate(
        tlc_output=(
            "Error: Temporal properties were violated.\n"
            "4 states generated, 4 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output=(
            "Model checking complete: No errors found (exhaustive).\n"
            "States found: 4\n"
        ),
        tlc_rc=0,
        tla2_rc=0,
        tlc_states="4",
        tla2_states="4",
    )

    assert parsed["tlc_status"] == "liveness", f"expected tlc_status=liveness, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "success", f"expected tla2_status=success, got {parsed['tla2_status']!r}"
    assert parsed["state_match"] == "yes", f"expected state_match=yes, got {parsed['state_match']!r}"
    assert parsed["verdict_match"] == "no", f"expected verdict_match=no, got {parsed['verdict_match']!r}"
    assert parsed["overall"] == "FAIL", f"expected overall=FAIL, got {parsed['overall']!r}"


def test_error_status_class_match_is_treated_as_parity_pass() -> None:
    parsed = _evaluate_gate(
        tlc_output="Error: Failed to parse configuration.\n",
        tla2_output="Error: Failed to parse configuration.\n",
        tlc_rc=1,
        tla2_rc=1,
    )

    assert parsed["tlc_status"] == "error", f"expected tlc_status=error, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "error", f"expected tla2_status=error, got {parsed['tla2_status']!r}"
    assert parsed["verdict_match"] == "yes", f"expected verdict_match=yes, got {parsed['verdict_match']!r}"
    assert parsed["overall"] == "PASS", f"expected overall=PASS, got {parsed['overall']!r}"


def test_tla2_liveness_tlc_success_is_fail() -> None:
    """Reverse direction: TLA2 reports liveness violation but TLC succeeds."""
    parsed = _evaluate_gate(
        tlc_output=(
            "Model checking completed. No error has been found.\n"
            "10 states generated, 10 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output=(
            "Error: Temporal properties were violated.\n"
            "States found: 10\n"
        ),
        tlc_states="10",
        tla2_states="10",
    )

    assert parsed["tlc_status"] == "success", f"expected tlc_status=success, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "liveness", f"expected tla2_status=liveness, got {parsed['tla2_status']!r}"
    assert parsed["verdict_match"] == "no", f"expected verdict_match=no, got {parsed['verdict_match']!r}"
    assert parsed["overall"] == "FAIL", f"expected overall=FAIL, got {parsed['overall']!r}"


def test_both_liveness_states_match_is_pass() -> None:
    """Both detect liveness violation with matching states -> PASS."""
    parsed = _evaluate_gate(
        tlc_output=(
            "Error: Temporal properties were violated.\n"
            "8 states generated, 8 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output=(
            "Error: Temporal properties were violated.\n"
            "States found: 8\n"
        ),
        tlc_states="8",
        tla2_states="8",
    )

    assert parsed["tlc_status"] == "liveness", f"expected tlc_status=liveness, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "liveness", f"expected tla2_status=liveness, got {parsed['tla2_status']!r}"
    assert parsed["verdict_match"] == "yes", f"expected verdict_match=yes, got {parsed['verdict_match']!r}"
    assert parsed["overall"] == "PASS", f"expected overall=PASS, got {parsed['overall']!r}"


def test_both_liveness_states_differ_still_pass() -> None:
    """Both detect liveness violation but state counts differ -> PASS.

    Verdict-class match is sufficient for error detection; state count
    differences in error cases are not regressions.
    """
    parsed = _evaluate_gate(
        tlc_output=(
            "Error: Temporal properties were violated.\n"
            "8 states generated, 8 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output=(
            "Error: Temporal properties were violated.\n"
            "States found: 6\n"
        ),
        tlc_states="8",
        tla2_states="6",
    )

    assert parsed["tlc_status"] == "liveness", f"expected tlc_status=liveness, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "liveness", f"expected tla2_status=liveness, got {parsed['tla2_status']!r}"
    assert parsed["verdict_match"] == "yes", f"expected verdict_match=yes, got {parsed['verdict_match']!r}"
    assert parsed["overall"] == "PASS", f"expected overall=PASS, got {parsed['overall']!r}"


def test_both_invariant_is_pass() -> None:
    """Both detect invariant violation -> PASS (verdict class match)."""
    parsed = _evaluate_gate(
        tlc_output=(
            "Error: Invariant InvOK is violated.\n"
            "5 states generated, 5 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output=(
            "Error: Invariant InvOK is violated.\n"
            "States found: 5\n"
        ),
        tlc_states="5",
        tla2_states="5",
    )

    assert parsed["tlc_status"] == "invariant", f"expected tlc_status=invariant, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "invariant", f"expected tla2_status=invariant, got {parsed['tla2_status']!r}"
    assert parsed["verdict_match"] == "yes", f"expected verdict_match=yes, got {parsed['verdict_match']!r}"
    assert parsed["overall"] == "PASS", f"expected overall=PASS, got {parsed['overall']!r}"


def test_deadlock_vs_success_is_fail() -> None:
    """TLC detects deadlock, TLA2 reports success -> FAIL."""
    parsed = _evaluate_gate(
        tlc_output=(
            "Error: Deadlock reached.\n"
            "3 states generated, 3 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output=(
            "Model checking complete: No errors found (exhaustive).\n"
            "States found: 3\n"
        ),
        tlc_states="3",
        tla2_states="3",
    )

    assert parsed["tlc_status"] == "deadlock", f"expected tlc_status=deadlock, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "success", f"expected tla2_status=success, got {parsed['tla2_status']!r}"
    assert parsed["verdict_match"] == "no", f"expected verdict_match=no, got {parsed['verdict_match']!r}"
    assert parsed["overall"] == "FAIL", f"expected overall=FAIL, got {parsed['overall']!r}"


def test_both_success_states_match_is_pass() -> None:
    """Both succeed with matching state counts -> PASS."""
    parsed = _evaluate_gate(
        tlc_output=(
            "Model checking completed. No error has been found.\n"
            "100 states generated, 100 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output=(
            "Model checking complete: No errors found (exhaustive).\n"
            "States found: 100\n"
        ),
        tlc_states="100",
        tla2_states="100",
    )

    assert parsed["tlc_status"] == "success", f"expected tlc_status=success, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "success", f"expected tla2_status=success, got {parsed['tla2_status']!r}"
    assert parsed["verdict_match"] == "yes", f"expected verdict_match=yes, got {parsed['verdict_match']!r}"
    assert parsed["state_match"] == "yes", f"expected state_match=yes, got {parsed['state_match']!r}"
    assert parsed["overall"] == "PASS", f"expected overall=PASS, got {parsed['overall']!r}"


def test_both_success_states_differ_is_fail() -> None:
    """Both succeed but state counts differ -> FAIL (state count regression)."""
    parsed = _evaluate_gate(
        tlc_output=(
            "Model checking completed. No error has been found.\n"
            "100 states generated, 100 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output=(
            "Model checking complete: No errors found (exhaustive).\n"
            "States found: 90\n"
        ),
        tlc_states="100",
        tla2_states="90",
    )

    assert parsed["tlc_status"] == "success", f"expected tlc_status=success, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "success", f"expected tla2_status=success, got {parsed['tla2_status']!r}"
    assert parsed["verdict_match"] == "yes", f"expected verdict_match=yes, got {parsed['verdict_match']!r}"
    assert parsed["state_match"] == "no", f"expected state_match=no, got {parsed['state_match']!r}"
    assert parsed["overall"] == "FAIL", f"expected overall=FAIL, got {parsed['overall']!r}"


def test_tla2_timeout_is_error() -> None:
    """TLA2 timeout with valid TLC result -> ERROR."""
    parsed = _evaluate_gate(
        tlc_output=(
            "Model checking completed. No error has been found.\n"
            "50 states generated, 50 distinct states found, 0 states left on queue.\n"
        ),
        tla2_output="[TIMEOUT] after 600s: tla check spec.tla\n",
        tla2_rc=124,
        tlc_states="50",
        tla2_states="",
    )

    assert parsed["tlc_status"] == "success", f"expected tlc_status=success, got {parsed['tlc_status']!r}"
    assert parsed["tla2_status"] == "timeout", f"expected tla2_status=timeout, got {parsed['tla2_status']!r}"
    assert parsed["overall"] == "ERROR", f"expected overall=ERROR, got {parsed['overall']!r}"
