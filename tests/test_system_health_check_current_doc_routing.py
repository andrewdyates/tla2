# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Focused tests for the current-doc routing health-check hook."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import system_health_check as shc


def test_check_current_doc_routing_success(monkeypatch) -> None:
    captured: dict[str, object] = {}

    def fake_run(cmd: list[str], *, timeout_sec: int) -> tuple[int, str]:
        captured["cmd"] = cmd
        captured["timeout_sec"] = timeout_sec
        return 0, "Current doc routing guards passed."

    monkeypatch.setattr(shc, "_run", fake_run)

    result = shc._check_current_doc_routing()

    assert result.ok is True, f"expected success check, got {result}"
    assert result.detail == "routing guards passed", (
        f"expected routing-guards-passed detail, got {result.detail!r}"
    )
    assert captured["cmd"] == [
        "python3",
        "scripts/check_current_doc_routing.py",
    ], captured
    assert captured["timeout_sec"] == 10, captured


def test_check_current_doc_routing_failure_trims_output(monkeypatch) -> None:
    monkeypatch.setattr(
        shc,
        "_run",
        lambda _cmd, *, timeout_sec: (1, "drift" * 200),
    )

    result = shc._check_current_doc_routing()

    assert result.ok is False, f"expected failure check, got {result}"
    assert result.detail is not None, "expected failure detail to be populated"
    assert result.detail.startswith("drift"), result.detail
    assert result.detail.endswith("... (truncated)"), result.detail
