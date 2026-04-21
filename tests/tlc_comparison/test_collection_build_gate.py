# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest

from . import conftest as tlc_conftest

pytestmark = pytest.mark.no_tla2_build


class _FakeItem:
    def __init__(self, nodeid: str, *, no_tla2_build: bool) -> None:
        self.nodeid = nodeid
        self._no_tla2_build = no_tla2_build

    def get_closest_marker(self, name: str) -> object | None:
        if name == "no_tla2_build" and self._no_tla2_build:
            return object()
        return None


def _session(*, collectonly: bool, items: list[_FakeItem]) -> SimpleNamespace:
    return SimpleNamespace(
        items=items,
        config=SimpleNamespace(option=SimpleNamespace(collectonly=collectonly)),
    )


def test_collection_finish_skips_build_during_collect_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[Path] = []
    monkeypatch.setattr(
        tlc_conftest,
        "_ensure_tla2_built",
        lambda repo_root: calls.append(repo_root),
    )

    tlc_conftest.pytest_collection_finish(
        _session(
            collectonly=True,
            items=[
                _FakeItem(
                    "tests/tlc_comparison/test_tlc_equivalence.py::test_parity",
                    no_tla2_build=False,
                )
            ],
        )
    )

    assert calls == [], f"collect-only should skip the tla-cli prebuild, got {calls!r}"


def test_collection_finish_builds_for_runnable_tlc_tests(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[Path] = []
    monkeypatch.setattr(
        tlc_conftest,
        "_ensure_tla2_built",
        lambda repo_root: calls.append(repo_root),
    )

    tlc_conftest.pytest_collection_finish(
        _session(
            collectonly=False,
            items=[
                _FakeItem(
                    "tests/tlc_comparison/test_tlc_equivalence.py::test_parity",
                    no_tla2_build=False,
                )
            ],
        )
    )

    expected = [Path(tlc_conftest.__file__).parent.parent.parent]
    assert calls == expected, f"expected one tla-cli prebuild at {expected!r}, got {calls!r}"


def test_collection_finish_skips_build_for_no_tla2_build_only_tests(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[Path] = []
    monkeypatch.setattr(
        tlc_conftest,
        "_ensure_tla2_built",
        lambda repo_root: calls.append(repo_root),
    )

    tlc_conftest.pytest_collection_finish(
        _session(
            collectonly=False,
            items=[
                _FakeItem(
                    "tests/tlc_comparison/test_output_parsing.py::test_parse_summary",
                    no_tla2_build=True,
                )
            ],
        )
    )

    assert calls == [], f"no_tla2_build-only sessions should skip the prebuild, got {calls!r}"
