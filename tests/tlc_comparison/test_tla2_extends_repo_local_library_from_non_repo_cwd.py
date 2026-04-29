# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from pathlib import Path

from .conftest import run_tla2


def test_tla2_can_extend_repo_local_library_from_non_repo_cwd(tmp_path: Path) -> None:
    spec_dir = tmp_path / "spec"
    run_dir = tmp_path / "run"
    spec_dir.mkdir()
    run_dir.mkdir()

    spec = spec_dir / "Main.tla"
    cfg = spec_dir / "Main.cfg"

    spec.write_text(
        "\n".join(
            [
                "------------------------- MODULE Main -------------------------",
                "EXTENDS Naturals, FunctionTheorems",
                "",
                "VARIABLE x",
                "Init == x = 0",
                "Next == x' \\in {0, 1} /\\ x' # x",
                "==============================================================",
                "",
            ]
        ),
        encoding="utf-8",
    )
    cfg.write_text("INIT Init\nNEXT Next\n", encoding="utf-8")

    result = run_tla2(spec, cfg, timeout=30, cwd=run_dir)

    assert result.exit_code == 0, result.raw_output
    assert not result.has_error, result.raw_output
    assert result.states == 2, result.raw_output
    assert "Loaded extended modules:" in result.raw_output
    assert "FunctionTheorems" in result.raw_output

