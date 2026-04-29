# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Focused tests for scripts/validate_coffecan_codegen_poc.py."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import validate_coffecan_codegen_poc as coffecan


def test_create_parser_has_expected_defaults() -> None:
    args = coffecan.create_parser().parse_args([])

    assert args.beans == 3000, f"expected default beans=3000, got {args.beans!r}"
    assert args.timeout == 1800, f"expected default timeout=1800, got {args.timeout!r}"
    assert args.skip_build is False, f"expected --skip-build default False, got {args.skip_build!r}"
    assert (
        args.skip_interpreter is False
    ), f"expected --skip-interpreter default False, got {args.skip_interpreter!r}"
    assert args.skip_tlc is False, f"expected --skip-tlc default False, got {args.skip_tlc!r}"
    assert (
        args.with_invariants is False
    ), f"expected --with-invariants default False, got {args.with_invariants!r}"
    assert args.output_json is None, f"expected no output-json path by default, got {args.output_json!r}"


def test_expected_states_uses_closed_form() -> None:
    assert coffecan.expected_states(1) == 2, "N=1 should yield 2 reachable states"
    assert coffecan.expected_states(10) == 65, "N=10 should yield 65 reachable states"
    assert coffecan.expected_states(3000) == 4_504_500, (
        "N=3000 should yield 4,504,500 reachable states"
    )


def test_parse_tlc_states_supports_primary_and_fallback_formats() -> None:
    canonical = "123 states generated, 45 distinct states found, 0 states left on queue."
    fallback = "Model checking completed. 45 distinct states found."

    assert coffecan.parse_tlc_states(canonical) == 45, canonical
    assert coffecan.parse_tlc_states(fallback) == 45, fallback
    assert coffecan.parse_tlc_states("no TLC summary here") is None, (
        "non-summary text should not produce a parsed TLC state count"
    )


def test_stage_wrapper_writes_optional_invariant(monkeypatch, tmp_path: Path) -> None:
    source_tla = tmp_path / "CoffeeCan.tla"
    source_tla.write_text("---- MODULE CoffeeCan ----\n====\n", encoding="utf-8")
    monkeypatch.setattr(coffecan, "COFFEECAN_TLA", source_tla)

    wrapper_tla, wrapper_cfg = coffecan.stage_wrapper(
        tmp_path / "no_inv",
        7,
        with_invariants=False,
    )
    no_inv_tla = wrapper_tla.read_text(encoding="utf-8")
    no_inv_cfg = wrapper_cfg.read_text(encoding="utf-8")
    assert "INSTANCE CoffeeCan WITH MaxBeanCount <- 7" in no_inv_tla, no_inv_tla
    assert "InvType ==" not in no_inv_tla, no_inv_tla
    assert "INVARIANTS" not in no_inv_cfg, no_inv_cfg

    wrapper_tla, wrapper_cfg = coffecan.stage_wrapper(
        tmp_path / "with_inv",
        7,
        with_invariants=True,
    )
    with_inv_tla = wrapper_tla.read_text(encoding="utf-8")
    with_inv_cfg = wrapper_cfg.read_text(encoding="utf-8")
    assert "InvType ==" in with_inv_tla, with_inv_tla
    assert "INVARIANTS" in with_inv_cfg, with_inv_cfg
    assert "InvType" in with_inv_cfg, with_inv_cfg


def test_validate_summary_counts_accepts_matching_results() -> None:
    coffecan.validate_summary_counts(
        {
            "expected_states": 65,
            "aot": {"states_distinct": 65},
            "interpreter": {"states_found": 65, "states_distinct": 65},
            "tlc": {"states_found": 65},
        }
    )


def test_validate_summary_counts_rejects_interpreter_mismatch() -> None:
    with pytest.raises(RuntimeError, match="Interpreter state count mismatch"):
        coffecan.validate_summary_counts(
            {
                "expected_states": 65,
                "aot": {"states_distinct": 65},
                "interpreter": {"states_found": 64, "states_distinct": 64},
                "tlc": {"states_found": 65},
            }
        )
