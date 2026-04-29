# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
SUMMARY = PROJECT_ROOT / "scripts" / "tla2_json_summary.py"


def _run_summary(path: Path) -> dict:
    cmd = [sys.executable, str(SUMMARY), str(path), "--format", "json"]
    res = subprocess.run(cmd, check=True, text=True, capture_output=True)
    return json.loads(res.stdout)


class TestTla2JsonSummary(unittest.TestCase):
    def test_summary_ok_extracts_states(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "ok.json"
            p.write_text(
                json.dumps(
                    {
                        "result": {"status": "ok"},
                        "statistics": {"states_found": 123, "states_distinct": 122},
                        "counterexample": None,
                    }
                ),
                encoding="utf-8",
            )
            out = _run_summary(p)
            self.assertEqual(out["status"], "ok")
            self.assertEqual(out["states_found"], 123)
            self.assertEqual(out["states_distinct"], 122)
            self.assertEqual(out["has_counterexample"], 0)

    def test_summary_invariant_violation_extracts_property(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "inv.json"
            p.write_text(
                json.dumps(
                    {
                        "result": {
                            "status": "error",
                            "error_type": "invariant_violation",
                            "error_code": "TLC_INVARIANT_VIOLATED",
                            "violated_property": {"prop_type": "invariant", "name": "Inv"},
                        },
                        "statistics": {"states_found": 9},
                        "counterexample": {"length": 2, "states": []},
                    }
                ),
                encoding="utf-8",
            )
            out = _run_summary(p)
            self.assertEqual(out["status"], "error")
            self.assertEqual(out["error_type"], "invariant_violation")
            self.assertEqual(out["error_code"], "TLC_INVARIANT_VIOLATED")
            self.assertEqual(out["violated_type"], "invariant")
            self.assertEqual(out["violated_name"], "Inv")
            self.assertEqual(out["has_counterexample"], 1)

    def test_summary_invalid_json_is_parse_error(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "bad.json"
            p.write_text("{not-json", encoding="utf-8")
            out = _run_summary(p)
            self.assertEqual(out["status"], "parse_error")
            self.assertEqual(out["states_found"], 0)
            self.assertEqual(out["states_distinct"], 0)


if __name__ == "__main__":
    unittest.main()
