# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Environment and provenance discovery helpers."""

import hashlib
import re
import subprocess
from collections import OrderedDict
from pathlib import Path

from .config import (
    COMMUNITY_MODULES,
    EXAMPLES_BASE_DIR,
    EXAMPLES_DIR,
    SCHEMA_VERSION,
    TLA2TOOLS,
    TLAPLUS_DIR,
)


def get_git_info(repo_path: Path) -> dict:
    """Get git repo info including commit, dirty status, and status digest."""
    result = {
        "head": "unknown",
        "head_short": "unknown",
        "is_dirty": None,
        "status_porcelain_sha256": None,
    }
    if not repo_path.exists():
        return result
    if not (repo_path / ".git").exists():
        return result
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True, text=True, timeout=10, cwd=repo_path
        )
        if proc.returncode == 0:
            result["head"] = proc.stdout.strip()
        proc = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, timeout=10, cwd=repo_path
        )
        if proc.returncode == 0:
            result["head_short"] = proc.stdout.strip()
        proc = subprocess.run(
            ["git", "status", "--porcelain=v1"],
            capture_output=True, text=True, timeout=10, cwd=repo_path
        )
        if proc.returncode == 0:
            status_output = proc.stdout
            result["is_dirty"] = len(status_output.strip()) > 0
            result["status_porcelain_sha256"] = hashlib.sha256(
                status_output.encode()
            ).hexdigest()[:16]
    except Exception:
        pass
    return result


def get_tlc_version() -> str:
    """Get TLC version string."""
    if not TLA2TOOLS.exists():
        return "unknown"
    try:
        proc = subprocess.run(
            ["java", "-jar", str(TLA2TOOLS), "-version"],
            capture_output=True, text=True, timeout=10
        )
        output = proc.stdout + proc.stderr
        match = re.search(r'TLC2?\s+[Vv]ersion\s+(\d+\.\d+\.\d+)', output)
        if match:
            return match.group(1)
        match = re.search(r'(\d+\.\d+\.\d+)', output)
        if match:
            return match.group(1)
        return output.strip()[:50] or "unknown"
    except Exception:
        return "unknown"


def get_java_version() -> str:
    """Get Java version string."""
    try:
        proc = subprocess.run(
            ["java", "-version"],
            capture_output=True, text=True, timeout=10
        )
        output = proc.stderr + proc.stdout
        match = re.search(r'version\s+"([^"]+)"', output)
        if match:
            return match.group(1)
        return output.split('\n')[0].strip()[:50] or "unknown"
    except Exception:
        return "unknown"


def get_jar_sha256(jar_path: Path) -> str:
    """Get SHA256 of JAR file."""
    if not jar_path.exists():
        return "unknown"
    try:
        with open(jar_path, "rb") as f:
            return hashlib.sha256(f.read()).hexdigest()
    except Exception:
        return "unknown"


def get_tla2_git_commit() -> str:
    """Get current tla2 repo commit."""
    from .config import PROJECT_ROOT
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, timeout=10, cwd=PROJECT_ROOT
        )
        if proc.returncode == 0:
            return proc.stdout.strip()
    except Exception:
        pass
    return "unknown"


def build_provenance(*, timeout_seconds: int, seed_enabled: bool, seed_source: Path | None) -> OrderedDict:
    """Build provenance metadata for the baseline."""
    has_community_modules = COMMUNITY_MODULES.exists()
    return OrderedDict([
        ("schema_version", SCHEMA_VERSION),
        ("collector", OrderedDict([
            ("tla2_git_commit", get_tla2_git_commit()),
            ("script", "scripts/collect_tlc_baseline.py"),
        ])),
        ("tlc", OrderedDict([
            ("jar_path", str(TLA2TOOLS)),
            ("jar_sha256", get_jar_sha256(TLA2TOOLS)),
            ("community_modules_path", str(COMMUNITY_MODULES) if has_community_modules else None),
            ("community_modules_sha256", get_jar_sha256(COMMUNITY_MODULES) if has_community_modules else None),
            ("tlc_version", get_tlc_version()),
            ("java_version", get_java_version()),
            ("jvm_args", ["-Xmx4g"]),
            ("workers", 1),
        ])),
        ("inputs", OrderedDict([
            ("examples_dir", str(EXAMPLES_DIR)),
            ("examples_git", get_git_info(EXAMPLES_BASE_DIR)),
            ("tlaplus_git", get_git_info(TLAPLUS_DIR)),
        ])),
        ("seed", OrderedDict([
            ("enabled", seed_enabled),
            ("policy", "seed_then_skip" if seed_enabled else "no_seed"),
            ("source_path", str(seed_source) if seed_source else None),
        ])),
        ("tlc_timeout_seconds", timeout_seconds),
    ])
