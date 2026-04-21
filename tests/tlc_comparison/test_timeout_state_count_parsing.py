# Copyright 2026 Andrew Yates.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

import pytest

from .conftest import parse_tla2_output, parse_tlc_output


@pytest.mark.no_tla2_build
def test_timeout_wrapper_preserves_tla2_state_count_parsing() -> None:
    output = "\n".join(
        [
            "Timeout after 1s",
            "cmd: tla check Spec.tla",
            "cwd: /tmp/spec",
            "",
            "",
            "--- stdout (partial) ---",
            "",
            "States found: 1,234",
            "",
        ]
    )
    parsed = parse_tla2_output(output)
    assert parsed.states == 1234
    assert parsed.distinct_states == 1234


@pytest.mark.no_tla2_build
def test_timeout_wrapper_preserves_tlc_state_count_parsing() -> None:
    output = "\n".join(
        [
            "Timeout after 1s",
            "cmd: java -jar tla2tools.jar Spec.tla",
            "cwd: /tmp/spec",
            "",
            "",
            "--- stdout (partial) ---",
            "",
            "1,000 states generated, 900 distinct states found, 0 states left on queue.",
            "",
        ]
    )
    parsed = parse_tlc_output(output)
    assert parsed.states == 1000
    assert parsed.distinct_states == 900


@pytest.mark.no_tla2_build
def test_timeout_wrapper_preserves_tla2_state_count_parsing_from_stderr() -> None:
    output = "\n".join(
        [
            "Timeout after 1s",
            "cmd: tla check Spec.tla",
            "cwd: /tmp/spec",
            "",
            "",
            "--- stderr (partial) ---",
            "",
            "States found: 10",
            "",
        ]
    )
    parsed = parse_tla2_output(output)
    assert parsed.states == 10
    assert parsed.distinct_states == 10


@pytest.mark.no_tla2_build
def test_timeout_wrapper_preserves_tlc_state_count_parsing_from_stderr() -> None:
    output = "\n".join(
        [
            "Timeout after 1s",
            "cmd: java -jar tla2tools.jar Spec.tla",
            "cwd: /tmp/spec",
            "",
            "",
            "--- stderr (partial) ---",
            "",
            "10 states generated, 9 distinct states found, 0 states left on queue.",
            "",
        ]
    )
    parsed = parse_tlc_output(output)
    assert parsed.states == 10
    assert parsed.distinct_states == 9
