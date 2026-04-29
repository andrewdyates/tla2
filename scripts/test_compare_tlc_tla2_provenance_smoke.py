#!/usr/bin/env python3
# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from compare_tlc_tla2 import main as compare_main  # noqa: E402


def _write(path: Path, content: str) -> None:
    path.write_text(content)


def _write_provenance(path: Path, *, spec_path: str, cfg_path: str, cfg_sha256: str) -> None:
    payload = {
        "schema_version": 1,
        "source": {
            "spec_path": spec_path,
            "cfg_path": cfg_path,
            "cfg_sha256": cfg_sha256,
        },
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _run(args: list[str]) -> tuple[int, str, str]:
    out = io.StringIO()
    err = io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = compare_main(args)
    return rc, out.getvalue(), err.getvalue()


def _build_minimal_artifacts(tmp_path: Path) -> tuple[Path, Path]:
    tlc_dot = tmp_path / "tlc.dot"
    tla2_debug = tmp_path / "tla2_debug.txt"
    _write(
        tlc_dot,
        'digraph DiskGraph {\n  1 [label="/\\\\ x = 0",style = filled];\n}\n',
    )
    _write(tla2_debug, "STATE deadbeef tlc=1 depth=0 -> 0 successors\n")
    return tlc_dot, tla2_debug


def test_missing_provenance_fails_by_default(tmp_path: Path) -> None:
    tlc_dot, tla2_debug = _build_minimal_artifacts(tmp_path)
    rc, _stdout, stderr = _run([str(tlc_dot), str(tla2_debug)])
    assert rc != 0
    assert "provenance sidecar not found" in stderr


def test_provenance_mismatch_fails_fast(tmp_path: Path) -> None:
    tlc_dot, tla2_debug = _build_minimal_artifacts(tmp_path)
    tlc_prov = Path(f"{tlc_dot}.provenance.json")
    tla2_prov = Path(f"{tla2_debug}.provenance.json")

    _write_provenance(
        tlc_prov,
        spec_path="NanoBlockchain/MCNano.tla",
        cfg_path="NanoBlockchain/MCNanoSmall.cfg",
        cfg_sha256="a" * 64,
    )
    _write_provenance(
        tla2_prov,
        spec_path="NanoBlockchain/MCNano.tla",
        cfg_path="/tmp/MCNanoSmall_no_view.cfg",
        cfg_sha256="b" * 64,
    )
    rc, _stdout, stderr = _run([str(tlc_dot), str(tla2_debug)])
    assert rc != 0
    assert "Config provenance mismatch" in stderr


def test_matching_provenance_allows_compare(tmp_path: Path) -> None:
    tlc_dot, tla2_debug = _build_minimal_artifacts(tmp_path)
    tlc_prov = Path(f"{tlc_dot}.provenance.json")
    tla2_prov = Path(f"{tla2_debug}.provenance.json")
    _write_provenance(
        tlc_prov,
        spec_path="NanoBlockchain/MCNano.tla",
        cfg_path="NanoBlockchain/MCNanoSmall.cfg",
        cfg_sha256="a" * 64,
    )
    _write_provenance(
        tla2_prov,
        spec_path="NanoBlockchain/MCNano.tla",
        cfg_path="NanoBlockchain/MCNanoSmall.cfg",
        cfg_sha256="a" * 64,
    )
    rc, stdout, stderr = _run([str(tlc_dot), str(tla2_debug)])
    assert rc == 0, stderr
    assert "PERFECT MATCH" in stdout


def test_write_provenance_generates_sidecars(tmp_path: Path) -> None:
    tlc_dot, tla2_debug = _build_minimal_artifacts(tmp_path)
    cfg_path = tmp_path / "MCNanoSmall.cfg"
    cfg_contents = "SPECIFICATION Next\nVIEW View\n"
    cfg_path.write_text(cfg_contents)

    rc, _stdout, stderr = _run(
        [
            "--write-provenance",
            "--spec-path",
            "NanoBlockchain/MCNano.tla",
            "--cfg-path",
            str(cfg_path),
            str(tlc_dot),
            str(tla2_debug),
        ]
    )
    assert rc == 0, stderr

    expected_sha = hashlib.sha256(cfg_contents.encode()).hexdigest()
    for sidecar in (
        Path(f"{tlc_dot}.provenance.json"),
        Path(f"{tla2_debug}.provenance.json"),
    ):
        payload = json.loads(sidecar.read_text())
        source = payload["source"]
        assert source["spec_path"] == "NanoBlockchain/MCNano.tla"
        assert source["cfg_path"] == str(cfg_path)
        assert source["cfg_sha256"] == expected_sha
