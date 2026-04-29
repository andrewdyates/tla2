# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Shared helpers: Check dataclass, subprocess runner, text utilities, manifest builder."""

from __future__ import annotations

import json
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    # None means "derive from ok" (ok->ok, !ok->err). "warn" is a non-blocking warning.
    level: str | None = None
    detail: str | None = None


def check_level(check: Check) -> str:
    if check.level is not None:
        return check.level
    return "ok" if check.ok else "err"


def run(cmd: list[str], *, cwd: Path, timeout_sec: int) -> tuple[int, str]:
    result = subprocess.run(
        cmd,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=timeout_sec,
    )
    stdout = (result.stdout or "").strip()
    stderr = (result.stderr or "").strip()
    out_parts = []
    if stdout:
        out_parts.append(stdout)
    if stderr:
        out_parts.append(f"STDERR:\n{stderr}")
    output = "\n".join(out_parts)
    return result.returncode, output


def trim(output: str, *, max_chars: int = 400) -> str:
    output = output.strip()
    if len(output) <= max_chars:
        return output
    return output[:max_chars].rstrip() + "\n... (truncated)"


def last_line(output: str) -> str:
    lines = [line.strip() for line in (output or "").splitlines() if line.strip()]
    return lines[-1] if lines else ""


def check_exists(path: Path) -> Check:
    if path.exists():
        return Check(name=f"exists:{path}", ok=True)
    return Check(name=f"exists:{path}", ok=False, detail="missing")


def check_json(path: Path) -> Check:
    if not path.exists():
        return Check(name=f"json:{path}", ok=False, detail="missing")
    try:
        data = json.loads(path.read_text())
    except Exception as exc:  # noqa: BLE001 - want a single error surface
        return Check(name=f"json:{path}", ok=False, detail=f"invalid json: {exc}")
    return Check(name=f"json:{path}", ok=True, detail=f"keys={sorted(data.keys())}")


def git_commit(project_root: Path) -> str:
    try:
        rc, out = run(["git", "rev-parse", "HEAD"], cwd=project_root, timeout_sec=5)
        if rc != 0:
            return "unknown"
        return out.strip()[:12]
    except Exception:  # noqa: BLE001
        return "unknown"


def manifest(project_root: Path, checks: list[Check]) -> dict[str, Any]:
    levels = [check_level(c) for c in checks]
    has_err = any(level == "err" for level in levels)
    has_warn = any(level == "warn" for level in levels)
    status = "fail" if has_err else ("warn" if has_warn else "pass")
    return {
        "schema_version": "1.0",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "git_commit": git_commit(project_root),
        "project": project_root.name,
        "summary": {
            "status": status,
            "passed": sum(1 for level in levels if level == "ok"),
            "warnings": sum(1 for level in levels if level == "warn"),
            "errors": sum(1 for level in levels if level == "err"),
        },
        "checks": [
            {"name": c.name, "ok": c.ok, "level": check_level(c), "detail": c.detail}
            for c in checks
        ],
    }
