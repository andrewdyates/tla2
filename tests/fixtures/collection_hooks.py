# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Pytest collection/config hooks used across the test suite."""

import pytest


def pytest_configure(config):
    """Validate required test dependencies are installed."""
    missing = []
    try:
        import pytest_timeout  # noqa: F401
    except ImportError:
        missing.append("pytest-timeout")
    try:
        import hypothesis  # noqa: F401
    except ImportError:
        missing.append("hypothesis")
    if missing:
        raise pytest.UsageError(
            f"Required test dependencies not installed: {', '.join(missing)}. "
            "Run: pip install -e '.[test]'"
        )


# Test files that spawn real bash subprocesses need more than the 10s global
# pytest timeout (#4428). Apply timeout(30) to match TEST_SUBPROCESS_TIMEOUT.
_SUBPROCESS_HEAVY_PREFIXES = (
    "tests/test_auth_preflight_keyring",
    "tests/test_bump_git_dep_rev",
    "tests/test_check_env_",
    "tests/test_commit_msg_",
    "tests/test_git_wrapper",
    "tests/test_init_from_template",
    "tests/test_init_labels",
    "tests/test_install_hooks",
    "tests/test_post_commit_",
    "tests/test_post_merge_hook",
    "tests/test_pre_commit_",
    "tests/test_pre_push_hook",
    "tests/test_regression_generated_file_exemption",
    "tests/test_run_scoped_tests",
    "tests/test_spawn_all",
    "tests/test_spawn_preflight_",
    "tests/test_spawn_session",
    "tests/test_sync_check",
    "tests/test_sync_repo",
    "tests/test_verify_incremental",
)


def pytest_collection_modifyitems(items):
    """Apply timeout overrides to test files that need more than the 10s global.

    The global timeout is 10s (#1886) but two categories routinely exceed it:
    1. Subprocess-heavy tests (2-8s per test, breaches under xdist) → 30s
    2. Hypothesis property tests (max_examples=200+ explores many paths) → 120s

    Without the property test override, pytest-timeout's signal handler fires
    mid-generation, causing Hypothesis FlakyStrategyDefinition errors that mask
    real test results.

    Tests with existing @pytest.mark.timeout decorators are left unchanged.
    """
    for item in items:
        if any(m.name == "timeout" for m in item.iter_markers()):
            continue
        if any(item.nodeid.startswith(p) for p in _SUBPROCESS_HEAVY_PREFIXES):
            item.add_marker(pytest.mark.timeout(30))
        elif "_property" in item.nodeid.split("::")[0]:
            item.add_marker(pytest.mark.timeout(120))
