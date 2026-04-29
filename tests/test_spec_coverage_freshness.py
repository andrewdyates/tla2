#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Deterministic tests for _check_spec_coverage_freshness() in system_health_check.py."""

from __future__ import annotations

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import patch

import pytest

# Import the module under test
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import system_health_check as shc


def _make_coverage_json(
    *,
    generated_at: str | None = None,
    git_commit_short: str | None = None,
    binary_info_git_commit: str | None = None,
) -> dict:
    """Build a minimal spec_coverage.json payload."""
    data: dict = {"schema_version": 7, "summary": {"pass": 93}}
    if generated_at is not None:
        data["generated_at"] = generated_at
    if git_commit_short is not None:
        data["git_commit_short"] = git_commit_short
    if binary_info_git_commit is not None:
        data["binary_info"] = {"git_commit": binary_info_git_commit}
    return data


def _write_coverage(tmp_path: Path, data: dict) -> None:
    metrics = tmp_path / "metrics"
    metrics.mkdir(exist_ok=True)
    (metrics / "spec_coverage.json").write_text(json.dumps(data))


def _fresh_timestamp() -> str:
    return (datetime.now(timezone.utc) - timedelta(hours=1)).isoformat()


def _warn_age_timestamp() -> str:
    return (datetime.now(timezone.utc) - timedelta(hours=30)).isoformat()


def _err_age_timestamp() -> str:
    return (datetime.now(timezone.utc) - timedelta(days=8)).isoformat()


class TestSpecCoverageFreshnessMissing:
    def test_missing_file_returns_warn(self, tmp_path: Path) -> None:
        with patch.object(shc, "PROJECT_ROOT", tmp_path):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "warn", f"expected warn for missing file, got {result.level}"
        assert result.ok is True, f"expected ok=True for warn-level missing file, got {result.ok}"
        assert "missing" in (result.detail or ""), f"detail should mention 'missing': {result.detail}"
        assert "diagnose" in (result.detail or ""), f"detail should include refresh command: {result.detail}"

    def test_invalid_json_returns_err(self, tmp_path: Path) -> None:
        metrics = tmp_path / "metrics"
        metrics.mkdir()
        (metrics / "spec_coverage.json").write_text("NOT JSON")
        with patch.object(shc, "PROJECT_ROOT", tmp_path):
            result = shc._check_spec_coverage_freshness()
        assert result.ok is False, f"expected ok=False for invalid json, got {result.ok}"
        assert "invalid json" in (result.detail or ""), f"detail should mention 'invalid json': {result.detail}"

    def test_missing_generated_at_returns_err(self, tmp_path: Path) -> None:
        _write_coverage(tmp_path, {"schema_version": 7})
        with patch.object(shc, "PROJECT_ROOT", tmp_path):
            result = shc._check_spec_coverage_freshness()
        assert result.ok is False, f"expected ok=False for missing generated_at, got {result.ok}"
        assert "missing generated_at" in (result.detail or ""), f"detail should mention field: {result.detail}"


class TestSpecCoverageFreshnessThresholds:
    def test_fresh_snapshot_returns_ok(self, tmp_path: Path) -> None:
        _write_coverage(tmp_path, _make_coverage_json(generated_at=_fresh_timestamp()))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=None),
        ):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "ok", f"expected ok for fresh snapshot, got {result.level}"
        assert result.ok is True, f"expected ok=True for fresh snapshot, got {result.ok}"

    def test_age_warn_threshold_24h(self, tmp_path: Path) -> None:
        _write_coverage(tmp_path, _make_coverage_json(generated_at=_warn_age_timestamp()))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=None),
        ):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "warn", f"expected warn for 30h age, got {result.level}"
        assert result.ok is True, f"expected ok=True for warn-level, got {result.ok}"

    def test_age_err_threshold_7d(self, tmp_path: Path) -> None:
        _write_coverage(tmp_path, _make_coverage_json(generated_at=_err_age_timestamp()))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=None),
        ):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "err", f"expected err for 8-day age, got {result.level}"
        assert result.ok is False, f"expected ok=False for err-level, got {result.ok}"

    def test_drift_warn_threshold_100(self, tmp_path: Path) -> None:
        _write_coverage(tmp_path, _make_coverage_json(
            generated_at=_fresh_timestamp(), binary_info_git_commit="abc123",
        ))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=150),
        ):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "warn", f"expected warn for 150-commit drift, got {result.level}"
        assert "150 commits" in (result.detail or ""), f"detail should show drift count: {result.detail}"

    def test_drift_err_threshold_500(self, tmp_path: Path) -> None:
        _write_coverage(tmp_path, _make_coverage_json(
            generated_at=_fresh_timestamp(), binary_info_git_commit="abc123",
        ))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=600),
        ):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "err", f"expected err for 600-commit drift, got {result.level}"
        assert result.ok is False, f"expected ok=False for err-level drift, got {result.ok}"

    def test_combined_worst_level_wins(self, tmp_path: Path) -> None:
        """Age=ok + drift=err → combined=err."""
        _write_coverage(tmp_path, _make_coverage_json(
            generated_at=_fresh_timestamp(), binary_info_git_commit="abc123",
        ))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=600),
        ):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "err", f"expected err when drift=err overrides age=ok, got {result.level}"


class TestSpecCoverageFreshnessGitCommitField:
    def test_reads_binary_info_git_commit(self, tmp_path: Path) -> None:
        """Current schema: binary_info.git_commit."""
        _write_coverage(tmp_path, _make_coverage_json(
            generated_at=_fresh_timestamp(), binary_info_git_commit="87cb05ce7",
        ))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=50) as mock_dist,
        ):
            result = shc._check_spec_coverage_freshness()
        mock_dist.assert_called_once_with("87cb05ce7")
        assert result.level == "ok", f"expected ok for 50-commit drift, got {result.level}"
        assert "50 commits" in (result.detail or ""), f"detail should show drift: {result.detail}"

    def test_reads_legacy_git_commit_short(self, tmp_path: Path) -> None:
        """Legacy schema: top-level git_commit_short."""
        _write_coverage(tmp_path, _make_coverage_json(
            generated_at=_fresh_timestamp(), git_commit_short="8c76510f",
        ))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=10) as mock_dist,
        ):
            result = shc._check_spec_coverage_freshness()
        mock_dist.assert_called_once_with("8c76510f")
        assert result.level == "ok", f"expected ok for legacy field with 10 drift, got {result.level}"

    def test_unresolvable_commit_returns_warn(self, tmp_path: Path) -> None:
        _write_coverage(tmp_path, _make_coverage_json(
            generated_at=_fresh_timestamp(), binary_info_git_commit="deadbeef",
        ))
        with (
            patch.object(shc, "PROJECT_ROOT", tmp_path),
            patch.object(shc, "_git_commit_distance", return_value=None),
        ):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "warn", f"expected warn for unresolvable commit, got {result.level}"

    def test_no_commit_field_drift_ok(self, tmp_path: Path) -> None:
        """No git commit at all → drift_lvl=ok, only age matters."""
        _write_coverage(tmp_path, _make_coverage_json(generated_at=_fresh_timestamp()))
        with patch.object(shc, "PROJECT_ROOT", tmp_path):
            result = shc._check_spec_coverage_freshness()
        assert result.level == "ok", f"expected ok when no commit field and fresh age, got {result.level}"
