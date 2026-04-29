# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Focused tests for the CoffeeCan validator health-check hook."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import system_health_check as shc


def test_check_coffecan_codegen_validator_help_success(monkeypatch) -> None:
    captured: dict[str, object] = {}

    def fake_run(cmd: list[str], *, timeout_sec: int) -> tuple[int, str]:
        captured["cmd"] = cmd
        captured["timeout_sec"] = timeout_sec
        return 0, "usage: validate_coffecan_codegen_poc.py"

    monkeypatch.setattr(shc, "_run", fake_run)

    result = shc._check_coffecan_codegen_validator_help()

    assert result.ok is True, f"expected success check, got {result}"
    assert result.detail == "usage ok", f"expected usage-ok detail, got {result.detail!r}"
    assert captured["cmd"] == [
        "python3",
        "scripts/validate_coffecan_codegen_poc.py",
        "--help",
    ], captured
    assert captured["timeout_sec"] == 10, captured


def test_check_coffecan_codegen_validator_help_failure_trims_output(monkeypatch) -> None:
    monkeypatch.setattr(
        shc,
        "_run",
        lambda _cmd, *, timeout_sec: (1, "boom" * 200),
    )

    result = shc._check_coffecan_codegen_validator_help()

    assert result.ok is False, f"expected failure check, got {result}"
    assert result.detail is not None, "expected failure detail to be populated"
    assert result.detail.startswith("boom"), result.detail
    assert result.detail.endswith("... (truncated)"), result.detail
