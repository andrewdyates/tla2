# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import os
import stat
import subprocess
import sys
from pathlib import Path


def _write_fake_gh(tmp_path: Path, *, stdout: str, stderr: str, code: int) -> Path:
    gh = tmp_path / "gh"
    gh.write_text(
        "\n".join(
            [
                "#!/usr/bin/env bash",
                "set -euo pipefail",
                f"printf '%s' {stdout!r}",
                f"printf '%s' {stderr!r} >&2",
                f"exit {code}",
                "",
            ]
        )
    )
    gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
    return gh


def _run_script_with_fake_gh(tmp_path: Path, *, stdout: str, stderr: str, code: int) -> subprocess.CompletedProcess[str]:
    _write_fake_gh(tmp_path, stdout=stdout, stderr=stderr, code=code)

    repo_root = Path(__file__).resolve().parents[1]
    script = repo_root / "scripts" / "gh_issue_list_rest.py"

    env = dict(os.environ)
    env["PATH"] = f"{tmp_path}{os.pathsep}{env.get('PATH', '')}"

    return subprocess.run(
        [sys.executable, str(script), "--repo", "andrewdyates/tla2", "--limit", "1"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        check=False,
    )


def test_gh_issue_list_rest_formats_saml_enforcement(tmp_path: Path) -> None:
    r = _run_script_with_fake_gh(
        tmp_path,
        stdout="",
        stderr=(
            "GraphQL: Resource protected by organization SAML enforcement. "
            "You must grant your OAuth token access to this organization."
        ),
        code=1,
    )
    assert r.returncode == 2
    assert "SAML enforcement" in r.stderr
    assert "gh auth refresh" in r.stderr


def test_gh_issue_list_rest_formats_404_as_sso_hint(tmp_path: Path) -> None:
    r = _run_script_with_fake_gh(
        tmp_path,
        stdout='{"message":"Not Found","status":"404"}',
        stderr="gh: Not Found (HTTP 404)",
        code=1,
    )
    assert r.returncode == 2
    assert "404 Not Found" in r.stderr
    assert "SSO" in r.stderr
    assert "gh auth refresh" in r.stderr


def test_gh_issue_list_rest_formats_rate_limit(tmp_path: Path) -> None:
    r = _run_script_with_fake_gh(
        tmp_path,
        stdout="",
        stderr="gh: API rate limit exceeded for user ID 123.",
        code=1,
    )
    assert r.returncode == 2
    assert "rate limit exceeded" in r.stderr.lower()
    assert "docs/github_cli_rate_limits.md" in r.stderr

