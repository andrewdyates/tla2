# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Baseline schema/provenance/drift checks and spec coverage freshness."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

from json_jcs import sha256_jcs

from system_health_check_support.common import Check


def get_git_head(repo_path: Path) -> str | None:
    """Get git HEAD commit hash for a repo."""
    if not repo_path.exists() or not (repo_path / ".git").exists():
        return None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo_path,
            capture_output=True,
            text=True,
            timeout=10,
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except Exception:
        pass
    return None


def get_jar_sha256(jar_path: Path) -> str | None:
    """Get SHA256 of a JAR file."""
    if not jar_path.exists():
        return None
    try:
        with open(jar_path, "rb") as f:
            return hashlib.sha256(f.read()).hexdigest()
    except Exception:
        return None


def check_spec_baseline(project_root: Path) -> Check:
    path = project_root / "tests" / "tlc_comparison" / "spec_baseline.json"
    if not path.exists():
        return Check(name="tlc_baseline:spec_baseline.json", ok=False, detail="missing")
    try:
        data = json.loads(path.read_text())
        specs = data.get("specs", {})
    except Exception as exc:  # noqa: BLE001 - want a single error surface
        return Check(name="tlc_baseline:spec_baseline.json", ok=False, detail=f"invalid json: {exc}")
    if not isinstance(specs, dict):
        return Check(
            name="tlc_baseline:spec_baseline.json",
            ok=False,
            detail=f"expected dict at .specs, got {type(specs).__name__}",
        )
    return Check(name="tlc_baseline:spec_baseline.json", ok=True, detail=f"specs={len(specs)}")


def check_baseline_provenance(project_root: Path) -> Check:
    """Verify spec_baseline.json has required provenance fields."""
    path = project_root / "tests" / "tlc_comparison" / "spec_baseline.json"
    if not path.exists():
        return Check(name="baseline_provenance", ok=False, detail="baseline missing")
    try:
        data = json.loads(path.read_text())
    except Exception as exc:
        return Check(name="baseline_provenance", ok=False, detail=f"invalid json: {exc}")

    schema_version = data.get("schema_version")
    if schema_version is None:
        return Check(name="baseline_provenance", ok=False, detail="missing schema_version")
    if schema_version < 2:
        return Check(name="baseline_provenance", ok=False, detail=f"schema_version={schema_version} (need >=2)")

    missing = []
    if not data.get("inputs", {}).get("examples_git", {}).get("head"):
        missing.append("inputs.examples_git.head")
    if not data.get("tlc", {}).get("tlc_version"):
        missing.append("tlc.tlc_version")
    if not data.get("tlc", {}).get("jar_sha256"):
        missing.append("tlc.jar_sha256")

    if missing:
        return Check(name="baseline_provenance", ok=False, detail=f"missing: {', '.join(missing)}")

    tlc_version = data["tlc"]["tlc_version"][:20]
    examples_commit = data["inputs"]["examples_git"].get("head_short", "?")
    return Check(name="baseline_provenance", ok=True, detail=f"tlc={tlc_version}, examples={examples_commit}")


def check_baseline_specs_digest(project_root: Path) -> Check:
    """Verify spec_baseline.json contains a formatting-independent digest for .specs."""
    path = project_root / "tests" / "tlc_comparison" / "spec_baseline.json"
    if not path.exists():
        return Check(name="baseline_specs_digest", ok=False, detail="baseline missing")
    try:
        data = json.loads(path.read_text())
    except Exception as exc:
        return Check(name="baseline_specs_digest", ok=False, detail=f"invalid json: {exc}")

    schema_version = data.get("schema_version", 0)
    if schema_version < 2:
        return Check(name="baseline_specs_digest", ok=True, detail="skipped (schema_version < 2)")

    specs = data.get("specs")
    if not isinstance(specs, dict):
        return Check(name="baseline_specs_digest", ok=False, detail="missing/invalid .specs")

    stored = data.get("specs_jcs_sha256")
    if not isinstance(stored, str) or not stored:
        return Check(name="baseline_specs_digest", ok=False, detail="missing specs_jcs_sha256")

    try:
        computed = sha256_jcs(specs)
    except Exception as exc:
        return Check(name="baseline_specs_digest", ok=False, detail=f"digest error: {exc}")

    if computed != stored:
        return Check(name="baseline_specs_digest", ok=False, detail="digest mismatch")

    return Check(name="baseline_specs_digest", ok=True, detail=stored[:16])


def check_baseline_drift(
    project_root: Path,
    tlaplus_examples_dir: Path,
    tla2tools_jar: Path,
) -> Check:
    """Detect drift between baseline provenance and current environment."""
    path = project_root / "tests" / "tlc_comparison" / "spec_baseline.json"
    if not path.exists():
        return Check(name="baseline_drift", ok=False, detail="baseline missing")
    try:
        data = json.loads(path.read_text())
    except Exception as exc:
        return Check(name="baseline_drift", ok=False, detail=f"invalid json: {exc}")

    if data.get("schema_version", 0) < 2:
        return Check(name="baseline_drift", ok=True, detail="skipped (no provenance)")

    drift_warnings = []

    baseline_examples_head = data.get("inputs", {}).get("examples_git", {}).get("head")
    if baseline_examples_head:
        current_examples_head = get_git_head(tlaplus_examples_dir)
        if current_examples_head is None:
            drift_warnings.append("examples: repo missing/not git")
        elif current_examples_head != baseline_examples_head:
            drift_warnings.append(
                f"examples: {baseline_examples_head[:8]} -> {current_examples_head[:8]}"
            )

    baseline_jar_sha256 = data.get("tlc", {}).get("jar_sha256")
    if baseline_jar_sha256 and baseline_jar_sha256 != "unknown":
        current_jar_sha256 = get_jar_sha256(tla2tools_jar)
        if current_jar_sha256 is None:
            drift_warnings.append("tlc: jar missing")
        elif current_jar_sha256 != baseline_jar_sha256:
            drift_warnings.append(
                f"tlc: jar changed ({baseline_jar_sha256[:8]} -> {current_jar_sha256[:8]})"
            )

    if drift_warnings:
        return Check(name="baseline_drift", ok=False, detail="; ".join(drift_warnings))

    return Check(name="baseline_drift", ok=True, detail="no drift")


def threshold_level(value: float, warn: float, err: float) -> str:
    """Return 'ok', 'warn', or 'err' based on thresholds."""
    if value >= err:
        return "err"
    return "warn" if value >= warn else "ok"


_LEVEL_ORDER = {"ok": 0, "warn": 1, "err": 2}


def check_spec_coverage_freshness(
    project_root: Path,
    *,
    git_commit_distance: Callable[[str], int | None],
    now_fn: Callable[[], datetime] | None = None,
) -> Check:
    """Check metrics/spec_coverage.json for staleness by age and commit drift."""
    if now_fn is None:
        now_fn = lambda: datetime.now(timezone.utc)  # noqa: E731
    name = "spec_coverage_freshness"
    refresh = "cargo run --release --bin tla2 -- diagnose --output-metrics"
    path = project_root / "metrics" / "spec_coverage.json"
    if not path.exists():
        return Check(name=name, ok=True, level="warn", detail=f"missing; run: {refresh}")
    try:
        data = json.loads(path.read_text())
    except Exception as exc:  # noqa: BLE001
        return Check(name=name, ok=False, detail=f"invalid json: {exc}")
    generated_at = data.get("generated_at")
    if not generated_at:
        return Check(name=name, ok=False, detail="missing generated_at field")
    try:
        gen_time = datetime.fromisoformat(generated_at).replace(tzinfo=timezone.utc)
        age_hours = (now_fn() - gen_time).total_seconds() / 3600
    except Exception as exc:  # noqa: BLE001
        return Check(name=name, ok=False, detail=f"bad generated_at: {exc}")
    git_commit = data.get("git_commit_short") or data.get("binary_info", {}).get("git_commit")
    drift = git_commit_distance(git_commit) if git_commit else None
    age_lvl = threshold_level(age_hours, warn=24, err=168)
    if drift is not None:
        drift_lvl = threshold_level(drift, warn=100, err=500)
    elif git_commit:
        drift_lvl = "warn"
    else:
        drift_lvl = "ok"
    combined = max(age_lvl, drift_lvl, key=lambda x: _LEVEL_ORDER[x])
    detail = f"age={age_hours:.0f}h, drift={drift} commits" if drift is not None else f"age={age_hours:.0f}h, drift=unknown"
    if combined != "ok":
        detail += f"; refresh: {refresh}"
    return Check(name=name, ok=(combined != "err"), level=combined, detail=detail)


def check_script_pipefail(project_root: Path) -> Check:
    """Verify all bash scripts with set -e also use pipefail."""
    scripts_dir = project_root / "scripts"
    if not scripts_dir.exists():
        return Check(name="script_pipefail", ok=True, detail="scripts/ not found (ok)")

    violations = []
    for script in sorted(scripts_dir.glob("*.sh")):
        content = script.read_text()
        has_set_e = re.search(r"^\s*set\s+-[a-z]*e", content, re.MULTILINE)
        has_pipefail = "pipefail" in content
        if has_set_e and not has_pipefail:
            violations.append(script.name)

    if violations:
        return Check(
            name="script_pipefail",
            ok=False,
            detail=f"missing pipefail: {', '.join(violations[:5])}{'...' if len(violations) > 5 else ''}",
        )
    return Check(name="script_pipefail", ok=True, detail="all scripts ok")
