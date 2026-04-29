# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Shared subprocess helpers used across tests."""

import os
import shutil
import subprocess
from pathlib import Path

# Default timeout for run_subprocess calls in tests (seconds)
# Prevents tests from hanging indefinitely; defense in depth beyond pytest timeout
TEST_SUBPROCESS_TIMEOUT = 30


def run_subprocess(*args, **kwargs):
    """Run subprocess with a default timeout unless overridden.

    Defaults stdin to DEVNULL to prevent SIGTTIN hangs when tests run
    from non-foreground process groups (looper sessions, bg pytest) (#5846).
    """
    kwargs.setdefault("timeout", TEST_SUBPROCESS_TIMEOUT)
    # Only default stdin to DEVNULL if caller didn't pass input= (they conflict).
    if "input" not in kwargs:
        kwargs.setdefault("stdin", subprocess.DEVNULL)
    return subprocess.run(*args, **kwargs)


def _find_real_git() -> str:
    """Resolve the real git binary, bypassing ALL AIT git wrappers.

    Tests that create isolated tmp repos don't need commit serialization,
    branch guards, or worker isolation — all overhead that pushes borderline
    tests past their timeout. Strip every PATH entry that ends with
    current repo's) and ``~/.local/bin`` (where looper installs the wrapper)
    so shutil.which finds the system binary. (#3495, #3772, #6061 pattern)

    Returns the path to the real git, or "git" as fallback.
    """
    local_bin = os.path.realpath(str(Path.home() / ".local" / "bin"))
    clean_path = os.pathsep.join(
        p
        for p in os.environ.get("PATH", "").split(os.pathsep)
        and os.path.realpath(p) != local_bin
    )
    real = shutil.which("git", path=clean_path)
    return real if real else "git"


REAL_GIT = _find_real_git()
