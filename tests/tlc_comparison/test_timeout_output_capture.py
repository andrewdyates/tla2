# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

import sys
from pathlib import Path

import pytest

from .conftest import _artifact_dir, _run_with_timeout, _write_artifact


@pytest.mark.no_tla2_build
def test_run_with_timeout_includes_partial_stdout_and_stderr(tmp_path) -> None:
    cmd = [
        sys.executable,
        "-u",
        "-c",
        "\n".join(
            [
                "import sys",
                "import time",
                "print('hello-stdout', flush=True)",
                "print('hello-stderr', file=sys.stderr, flush=True)",
                "time.sleep(60)",
            ]
        ),
    ]

    exit_code, output, timed_out = _run_with_timeout(cmd, cwd=tmp_path, timeout=2)

    assert timed_out is True
    assert exit_code == -1
    assert "Timeout after 2s" in output
    assert "cmd: " in output
    assert f"cwd: {tmp_path}" in output
    assert "--- stdout (partial) ---" in output
    assert "hello-stdout" in output
    assert "--- stderr (partial) ---" in output
    assert "hello-stderr" in output


@pytest.mark.no_tla2_build
def test_timeout_artifact_includes_partial_stdout_and_stderr(tmp_path, monkeypatch) -> None:
    repo_root = Path(__file__).parent.parent.parent
    artifacts_dir = tmp_path / "artifacts"
    monkeypatch.setenv("TLA2_TLC_COMPARISON_ARTIFACTS_DIR", str(artifacts_dir))
    resolved_artifacts_dir = _artifact_dir(repo_root)
    assert resolved_artifacts_dir == artifacts_dir

    cmd = [
        sys.executable,
        "-u",
        "-c",
        "\n".join(
            [
                "import sys",
                "import time",
                "print('hello-stdout', flush=True)",
                "print('hello-stderr', file=sys.stderr, flush=True)",
                "time.sleep(60)",
            ]
        ),
    ]

    exit_code, output, timed_out = _run_with_timeout(cmd, cwd=tmp_path, timeout=2)

    assert timed_out is True
    assert exit_code == -1
    assert "Timeout after 2s" in output
    assert "cmd: " in output
    assert f"cwd: {tmp_path}" in output
    assert "--- stdout (partial) ---" in output
    assert "hello-stdout" in output
    assert "--- stderr (partial) ---" in output
    assert "hello-stderr" in output

    spec = tmp_path / "Spec.tla"
    log_path = _write_artifact(
        artifacts_dir=resolved_artifacts_dir,
        kind="python_timeout",
        spec=spec,
        config=None,
        cmd=cmd,
        cwd=tmp_path,
        output=output,
    )
    text = log_path.read_text(encoding="utf-8", errors="replace")
    assert "# kind: python_timeout" in text
    assert "Timeout after 2s" in text
    assert "\ncmd: " in text
    assert f"\ncwd: {tmp_path}" in text
    assert "--- stdout (partial) ---" in text
    assert "hello-stdout" in text
    assert "--- stderr (partial) ---" in text
    assert "hello-stderr" in text


@pytest.mark.no_tla2_build
def test_run_with_timeout_normalizes_carriage_returns(tmp_path) -> None:
    cmd = [
        sys.executable,
        "-u",
        "-c",
        "\n".join(
            [
                "import sys",
                "import time",
                "sys.stdout.write('a\\rb\\r\\nc\\r')",
                "sys.stdout.flush()",
                "sys.stderr.write('x\\ry\\r\\nz\\r')",
                "sys.stderr.flush()",
                "time.sleep(60)",
            ]
        ),
    ]

    _exit_code, output, timed_out = _run_with_timeout(cmd, cwd=tmp_path, timeout=2)

    assert timed_out is True
    assert "\r" not in output
    assert "a\nb\nc" in output
    assert "x\ny\nz" in output
