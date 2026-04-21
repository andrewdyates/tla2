# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from pathlib import Path

from .conftest import run_tla2


def test_tla2_can_run_from_non_repo_cwd(tmp_path: Path, test_specs_dir: Path) -> None:
    spec = test_specs_dir / "instance_standalone_test" / "Outer.tla"
    cfg = test_specs_dir / "instance_standalone_test" / "Outer.cfg"

    result = run_tla2(spec, cfg, timeout=30, cwd=tmp_path)

    assert result.exit_code == 0, result.raw_output
    assert not result.has_error, result.raw_output
    assert result.states == 3, result.raw_output
    assert "Loaded instanced modules: Inner" in result.raw_output

