# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

import re
from pathlib import Path

from .conftest import run_tla2, run_tlc


def _extract_cannot_handle_location(output: str) -> str:
    # TLC sometimes prefixes with "Error:". Keep this regex tolerant and extract only
    # the location blob after "... temporal formula ".
    m = re.search(
        r"cannot handle the temporal formula\s+([^:\n]+)(?::\n|\n|$)",
        output,
        re.IGNORECASE,
    )
    assert m is not None, f"Missing EC2213 marker in output tail:\n{output[-800:]}"
    return m.group(1).strip()


def test_cannot_handle_temporal_formula_2213_matches_tlc(tmp_path: Path, monkeypatch) -> None:
    repro_dir = Path(__file__).parent / "repros" / "cannot_handle_temporal_formula_2213"
    spec = repro_dir / "CannotHandleTemporalFormula2213.tla"
    cfg = repro_dir / "CannotHandleTemporalFormula2213.cfg"
    assert spec.exists()
    assert cfg.exists()

    # Capture artifacts for this parity test, but keep them out of the repo.
    monkeypatch.setenv(
        "TLA2_TLC_COMPARISON_ARTIFACTS_DIR",
        str(tmp_path / "artifacts"),
    )

    tlc = run_tlc(spec, cfg, timeout=60)
    tla2 = run_tla2(spec, cfg, timeout=60)

    assert tlc.has_error, f"TLC unexpectedly succeeded:\n{tlc.raw_output[-800:]}"
    assert tla2.has_error, f"TLA2 unexpectedly succeeded:\n{tla2.raw_output[-800:]}"

    assert tlc.error_type == "unsupported", f"TLC error_type={tlc.error_type}\n{tlc.raw_output[-800:]}"
    assert tla2.error_type == "unsupported", f"TLA2 error_type={tla2.error_type}\n{tla2.raw_output[-800:]}"

    tlc_loc = _extract_cannot_handle_location(tlc.raw_output)
    tla2_loc = _extract_cannot_handle_location(tla2.raw_output)
    assert tla2_loc == tlc_loc, (
        "EC2213 location mismatch\n"
        f"  TLC:  {tlc_loc}\n"
        f"  TLA2: {tla2_loc}\n"
        f"  TLC tail:\n{tlc.raw_output[-800:]}\n"
        f"  TLA2 tail:\n{tla2.raw_output[-800:]}\n"
    )

    # If TLC includes a newline-separated reason, require TLA2 to match that shape.
    tlc_has_reason = bool(
        re.search(
            r"cannot handle the temporal formula[^\n]*:\n",
            tlc.raw_output,
            re.IGNORECASE,
        )
    )
    tla2_has_reason = bool(
        re.search(
            r"cannot handle the temporal formula[^\n]*:\n",
            tla2.raw_output,
            re.IGNORECASE,
        )
    )
    assert tla2_has_reason == tlc_has_reason, (
        "EC2213 reason newline-shape mismatch\n"
        f"  TLC has reason:  {tlc_has_reason}\n"
        f"  TLA2 has reason: {tla2_has_reason}\n"
        f"  TLC tail:\n{tlc.raw_output[-800:]}\n"
        f"  TLA2 tail:\n{tla2.raw_output[-800:]}\n"
    )
