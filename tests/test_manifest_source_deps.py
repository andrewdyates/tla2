# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import shlex
from pathlib import Path

from tests.conftest import run_subprocess


REPO_ROOT = Path(__file__).resolve().parents[1]


def _write_source_dep_fixture(repo: Path, *, include_helpers_in_manifest: bool) -> None:
    manifest_entries = [
    ]
    if include_helpers_in_manifest:
        manifest_entries.extend(
            [
            ]
        )
    (repo / ".sync_manifest").write_text(
        "\n".join(manifest_entries) + "\n",
        encoding="utf-8",
    )
        """#!/usr/bin/env bash
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/lib/target_repo_git.sh"
""",
        encoding="utf-8",
    )
        """#!/usr/bin/env bash
_TARGET_REPO_GIT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${_TARGET_REPO_GIT_DIR}/target_repo_git_prepare.sh"
source "${_TARGET_REPO_GIT_DIR}/target_repo_git_push.sh"
source "${_TARGET_REPO_GIT_DIR}/target_repo_git_commit.sh"
""",
        encoding="utf-8",
    )
    for helper_name in (
        "target_repo_git_prepare.sh",
        "target_repo_git_push.sh",
        "target_repo_git_commit.sh",
    ):
            "#!/usr/bin/env bash\n",
            encoding="utf-8",
        )


def _run_validate_source_dependencies(repo: Path):
    command = f"""
set -euo pipefail
log_error() {{
    printf '%s\\n' "$*" >&2
}}
source {shlex.quote(str(manifest_lib))}
"""
    return run_subprocess(
        ["/bin/bash", "-lc", command],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )


def test_validate_source_dependencies_flags_nested_sync_repo_helper_gap(
    tmp_path: Path,
) -> None:
    _write_source_dep_fixture(tmp_path, include_helpers_in_manifest=False)

    result = _run_validate_source_dependencies(tmp_path)

    assert result.returncode == 1, (
        "expected validate_source_dependencies to fail when a lib helper sourced "
        f"by target_repo_git.sh is missing from the manifest, got {result.returncode}"
    )
    assert "target_repo_git_prepare.sh" in result.stderr, (
        "expected the reported source dependency gap to mention the first missing "
        f"helper, got stderr={result.stderr!r}"
    )


def test_validate_source_dependencies_accepts_nested_sync_repo_helpers_when_covered(
    tmp_path: Path,
) -> None:
    _write_source_dep_fixture(tmp_path, include_helpers_in_manifest=True)

    result = _run_validate_source_dependencies(tmp_path)

    assert result.returncode == 0, (
        "expected validate_source_dependencies to accept nested sync_repo helper "
        f"files once the manifest covers them, got {result.returncode} with "
        f"stderr={result.stderr!r}"
    )
