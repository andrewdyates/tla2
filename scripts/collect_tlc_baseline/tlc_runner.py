# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""TLC execution, output parsing, and result classification."""

import os
import re
import subprocess
import tempfile
import time
from contextlib import nullcontext
from pathlib import Path

from .config import COMMUNITY_MODULES, PROJECT_ROOT, TLA2TOOLS


def parse_tlc_output(output: str) -> tuple[int | None, str | None]:
    match = re.search(
        r"^\s*([0-9,]+) states generated, ([0-9,]+) distinct states found, ([0-9,]+) states left",
        output,
        re.MULTILINE,
    )
    if match:
        return int(match.group(2).replace(",", "")), None

    match = re.search(r"([0-9,]+) distinct states found", output)
    if match:
        return int(match.group(1).replace(",", "")), None

    match = re.search(r"Cannot find source file for module ([A-Za-z0-9_]+)\b", output)
    if match:
        return None, f"missing_module:{match.group(1)}"

    return None, "no_state_count"


def classify_error(output: str) -> str | None:
    if not re.search(r"Error:", output):
        return None

    if "Invariant" in output and "violated" in output:
        return "invariant"
    if "Deadlock" in output:
        return "deadlock"
    if "Parsing or semantic analysis failed" in output:
        return "parse"
    if "Temporal properties were violated" in output:
        return "liveness"
    if "Action property" in output and "violated" in output:
        return "action"
    if re.search(r"Property .* is violated", output):
        return "safety"
    return "unknown"


def cleanup_states_dir(states_dir: Path) -> None:
    # Safety guard: only ever remove a directory named "states" under a spec dir.
    if states_dir.name != "states":
        return
    try:
        import shutil

        if states_dir.is_symlink():
            states_dir.unlink()
        elif states_dir.is_dir():
            shutil.rmtree(states_dir)
    except Exception:
        pass


def run_tlc(spec_path: Path, cfg_path: Path, *, timeout_seconds: int) -> dict:
    """Run TLC and return baseline data."""
    result = {
        "status": "unknown",
        "states": None,
        "runtime_seconds": None,
        "error_type": None,
        "error": None,
    }

    use_ephemeral_metadir = os.environ.get("TLA2_KEEP_STATES", "").strip() != "1"
    preserve_states_dir = os.environ.get("TLA2_PRESERVE_STATES_DIR", "").strip() == "1"
    states_dir = spec_path.parent / "states"

    start = time.time()
    try:
        metadir_root = Path(
            os.environ.get("TLA2_TLC_METADIR_ROOT", str(PROJECT_ROOT / "target" / "tlc_metadir"))
        )
        if use_ephemeral_metadir:
            metadir_root.mkdir(parents=True, exist_ok=True)

        metadir_ctx = (
            tempfile.TemporaryDirectory(dir=metadir_root)
            if use_ephemeral_metadir
            else nullcontext(None)
        )
        with metadir_ctx as tlc_metadir:
            classpath = str(TLA2TOOLS)
            if COMMUNITY_MODULES.exists():
                classpath += os.pathsep + str(COMMUNITY_MODULES)
            args = [
                "java",
                "-Xmx4g",
                "-cp",
                classpath,
                "tlc2.TLC",
            ]
            if tlc_metadir is not None:
                args += ["-metadir", str(tlc_metadir)]
            args += [
                "-config",
                str(cfg_path),
                "-workers",
                "1",
                str(spec_path),
            ]
            proc = subprocess.run(
                args,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
                cwd=str(spec_path.parent),
            )
        elapsed = time.time() - start
        result["runtime_seconds"] = round(elapsed, 2)

        output = proc.stdout + proc.stderr

        states, parse_err = parse_tlc_output(output)
        result["states"] = states

        error_type = classify_error(output)
        result["error_type"] = error_type

        if states is not None:
            result["status"] = "pass"
        elif parse_err is not None and parse_err.startswith("missing_module:"):
            result["status"] = "error"
            result["error_type"] = "missing_module"
            result["error"] = f"Missing module: {parse_err.split(':', 1)[1]}"
        elif proc.returncode != 0 and ("Exception" in output):
            result["status"] = "error"
        elif parse_err is not None:
            result["status"] = "error"
            result["error"] = parse_err
        else:
            result["status"] = "unknown"
            result["error"] = "No state count found in output"

        if result["status"] in {"error", "unknown"} and result["error"] is None:
            for line in output.split("\n"):
                if "Error:" in line or "Exception" in line:
                    result["error"] = line[:200]
                    break

    except subprocess.TimeoutExpired:
        result["status"] = "timeout"
        result["runtime_seconds"] = timeout_seconds
        result["error"] = f"Timeout after {timeout_seconds}s"
        result["error_type"] = "timeout"
    except Exception as e:
        result["status"] = "error"
        result["error"] = str(e)[:200]
    finally:
        if use_ephemeral_metadir and (not preserve_states_dir):
            cleanup_states_dir(states_dir)

    return result


def categorize_runtime(seconds: float) -> str:
    """Categorize spec by runtime."""
    if seconds is None:
        return "unknown"
    elif seconds < 1:
        return "small"
    elif seconds < 30:
        return "medium"
    elif seconds < 300:
        return "large"
    else:
        return "xlarge"
