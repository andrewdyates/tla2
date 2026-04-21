# Copyright 2026 Andrew Yates.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

import pytest

from .conftest import parse_tla2_output, parse_tlc_output


@pytest.mark.no_tla2_build
def test_parse_tla2_output_classifies_semantic_errors_as_parse() -> None:
    out = "\n".join(
        [
            "/tmp/foo.tla: semantic error: duplicate definition of `Range`",
            "/tmp/foo.tla: semantic error: duplicate definition of `Restrict`",
            "Error: semantic analysis failed with 2 error(s)",
            "",
        ]
    )
    parsed = parse_tla2_output(out)
    assert parsed.has_error
    assert parsed.error_type == "parse"


@pytest.mark.no_tla2_build
def test_parse_tlc_output_treats_warnings_only_as_success() -> None:
    out = "\n".join(
        [
            "Semantic errors:",
            "",
            "*** Warnings: 10",
            "",
            "90 states generated, 45 distinct states found, 0 states left on queue.",
        ]
    )
    parsed = parse_tlc_output(out)
    assert not parsed.has_error
    assert parsed.error_type is None
    assert parsed.states == 90
    assert parsed.distinct_states == 45


@pytest.mark.no_tla2_build
def test_parse_tlc_output_detects_semantic_errors_without_error_prefix() -> None:
    out = "\n".join(
        [
            "Semantic errors:",
            "",
            "*** Errors: 1",
            "",
            "line 1, col 1 to line 1, col 10 of module Foo",
            "",
            "Some semantic error text",
        ]
    )
    parsed = parse_tlc_output(out)
    assert parsed.has_error
    assert parsed.error_type == "parse"


@pytest.mark.no_tla2_build
def test_parse_tlc_output_allows_commas_in_state_counts() -> None:
    out = "1,234 states generated, 5,678 distinct states found, 0 states left on queue."
    parsed = parse_tlc_output(out)
    assert not parsed.has_error
    assert parsed.states == 1234
    assert parsed.distinct_states == 5678


@pytest.mark.no_tla2_build
def test_parse_tlc_output_allows_leading_whitespace_in_summary_line() -> None:
    out = "   1,234 states generated, 5,678 distinct states found, 0 states left on queue."
    parsed = parse_tlc_output(out)
    assert not parsed.has_error
    assert parsed.states == 1234
    assert parsed.distinct_states == 5678


@pytest.mark.no_tla2_build
def test_parse_tlc_output_classifies_cannot_handle_temporal_formula_as_unsupported() -> None:
    out = "\n".join(
        [
            "Error: TLC cannot handle the temporal formula []S",
            "",
            "0 states generated, 0 distinct states found, 0 states left on queue.",
        ]
    )
    parsed = parse_tlc_output(out)
    assert parsed.has_error
    assert parsed.error_type == "unsupported"


@pytest.mark.no_tla2_build
def test_parse_tla2_output_classifies_cannot_handle_temporal_formula_as_unsupported() -> None:
    out = "\n".join(
        [
            "Error: TLC cannot handle the temporal formula []S",
            "",
        ]
    )
    parsed = parse_tla2_output(out)
    assert parsed.has_error
    assert parsed.error_type == "unsupported"


@pytest.mark.no_tla2_build
def test_parse_tla2_output_classifies_cannot_handle_temporal_formula_with_reason_as_unsupported() -> None:
    out = (
        "Error: Liveness error: Failed to convert property 'Prop': "
        "TLC cannot handle the temporal formula bytes 1-2 of module Spec:\n"
        "some reason\n"
    )
    parsed = parse_tla2_output(out)
    assert parsed.has_error
    assert parsed.error_type == "unsupported"


@pytest.mark.no_tla2_build
def test_parse_tlc_output_normalizes_crlf_newlines() -> None:
    out = "\r\n".join(
        [
            "Error: TLC cannot handle the temporal formula []S",
            "",
            "0 states generated, 0 distinct states found, 0 states left on queue.",
            "",
        ]
    )
    parsed = parse_tlc_output(out)
    assert parsed.has_error
    assert parsed.error_type == "unsupported"
    assert parsed.states == 0
    assert parsed.distinct_states == 0


@pytest.mark.no_tla2_build
def test_parse_tla2_output_normalizes_cr_newlines() -> None:
    out = (
        "Error: Liveness error: Failed to convert property 'Prop': "
        "TLC cannot handle the temporal formula bytes 1-2 of module Spec:\r"
        "some reason\r"
    )
    parsed = parse_tla2_output(out)
    assert parsed.has_error
    assert parsed.error_type == "unsupported"


@pytest.mark.no_tla2_build
def test_parse_tla2_output_allows_commas_in_state_counts() -> None:
    out = "States found: 1,234\n"
    parsed = parse_tla2_output(out)
    assert not parsed.has_error
    assert parsed.states == 1234
    assert parsed.distinct_states == 1234
