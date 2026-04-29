# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import os
import stat
from pathlib import Path

import pytest

from .tlc_discovery import discover_tlc_backend

pytestmark = pytest.mark.no_tla2_build


def _make_executable(path: Path) -> None:
    path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


def test_discover_prefers_tlc_bin_over_path_and_jar(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_tlc_bin = tmp_path / "my_tlc_wrapper"
    _make_executable(fake_tlc_bin)

    fake_path_tlc = tmp_path / "tlc"
    _make_executable(fake_path_tlc)

    monkeypatch.setenv("TLC_BIN", str(fake_tlc_bin))
    monkeypatch.setenv("PATH", f"{tmp_path}{os.pathsep}{os.environ.get('PATH','')}")
    monkeypatch.setenv("TLA2TOOLS_JAR", str(tmp_path / "tla2tools.jar"))

    backend = discover_tlc_backend(allow_default_tlaplus=False)
    assert backend.kind == "cli"
    assert backend.tlc_bin == fake_tlc_bin


def test_discover_uses_tlc_on_path_when_present(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_path_tlc = tmp_path / "tlc"
    _make_executable(fake_path_tlc)

    monkeypatch.delenv("TLC_BIN", raising=False)
    monkeypatch.setenv("PATH", str(tmp_path))
    monkeypatch.delenv("TLA2TOOLS_JAR", raising=False)
    monkeypatch.delenv("TLC_JAR", raising=False)

    backend = discover_tlc_backend(allow_default_tlaplus=False)
    assert backend.kind == "cli"
    assert backend.tlc_bin == fake_path_tlc


def test_discover_uses_tla2tools_jar_env(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    jar = tmp_path / "tla2tools.jar"
    jar.write_text("not really a jar", encoding="utf-8")

    monkeypatch.delenv("TLC_BIN", raising=False)
    monkeypatch.setenv("PATH", str(tmp_path))  # no tlc present
    monkeypatch.setenv("TLA2TOOLS_JAR", str(jar))
    monkeypatch.delenv("TLC_JAR", raising=False)

    backend = discover_tlc_backend(allow_default_tlaplus=False)
    assert backend.kind == "java"
    assert backend.tla2tools_jar == jar


def test_discover_supports_tlc_jar_alias(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    jar = tmp_path / "tla2tools.jar"
    jar.write_text("not really a jar", encoding="utf-8")

    monkeypatch.delenv("TLC_BIN", raising=False)
    monkeypatch.setenv("PATH", str(tmp_path))  # no tlc present
    monkeypatch.delenv("TLA2TOOLS_JAR", raising=False)
    monkeypatch.setenv("TLC_JAR", str(jar))

    backend = discover_tlc_backend(allow_default_tlaplus=False)
    assert backend.kind == "java"
    assert backend.tla2tools_jar == jar


def test_discover_errors_without_backend(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.delenv("TLC_BIN", raising=False)
    monkeypatch.delenv("TLA2TOOLS_JAR", raising=False)
    monkeypatch.delenv("TLC_JAR", raising=False)
    monkeypatch.setenv("PATH", str(tmp_path))  # empty PATH: no `tlc`

    with pytest.raises(RuntimeError, match=r"failed to discover a TLC runner"):
        discover_tlc_backend(allow_default_tlaplus=False)

