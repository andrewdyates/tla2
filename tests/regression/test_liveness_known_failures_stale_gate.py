# Copyright 2026 Andrew Yates.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

import subprocess
import textwrap
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]


def _run_stale_scan(known_failures: str, results: str) -> str:
    script = textwrap.dedent(
        f"""
        set -euo pipefail
        tmp_dir="$(mktemp -d)"
        known_file="$tmp_dir/known_failures.txt"
        results_file="$tmp_dir/results.txt"

        cat > "$known_file" <<'KNOWN'
        {known_failures}
        KNOWN

        cat > "$results_file" <<'RESULTS'
        {results}
        RESULTS

        known_specs=""
        if [ -f "$known_file" ]; then
            while IFS= read -r line; do
                line="$(echo "$line" | sed 's/#.*//' | xargs)"
                [ -z "$line" ] && continue
                spec_name="$(echo "$line" | cut -d'|' -f1 | xargs)"
                [ -n "$spec_name" ] && known_specs="$known_specs $spec_name "
            done < "$known_file"
        fi

        STALE=0
        for kf_spec in $known_specs; do
            [ -z "$kf_spec" ] && continue
            kf_overall="$(grep -F "name=$kf_spec|" "$results_file" | head -1 | sed 's/.*overall=\\([^|]*\\).*/\\1/')"
            if [ -n "$kf_overall" ] && [ "$kf_overall" != "FAIL" ] && [ "$kf_overall" != "ERROR" ]; then
                echo "STALE ENTRY: $kf_spec is now $kf_overall — remove from known_failures.txt"
                STALE=$((STALE + 1))
            fi
        done

        [ "$STALE" -gt 0 ] && echo "Stale entries: $STALE (update known_failures.txt)"
        rm -rf "$tmp_dir"
        """
    )
    result = subprocess.run(
        ["bash", "-lc", script],
        cwd=PROJECT_ROOT,
        check=True,
        text=True,
        capture_output=True,
    )
    return result.stdout


def test_known_failure_entry_now_passes_is_reported_stale() -> None:
    known_failures = "SpecA | #1 | verdict_mismatch | historical failure"
    results = "RESULT|name=SpecA|tlc_status=success|tla2_status=success|overall=PASS"

    stdout = _run_stale_scan(known_failures, results)
    assert "STALE ENTRY: SpecA is now PASS" in stdout, f"Expected stale entry for SpecA, got: {stdout!r}"
    assert "Stale entries: 1 (update known_failures.txt)" in stdout, f"Expected stale count of 1, got: {stdout!r}"


def test_active_known_failure_is_not_reported_stale() -> None:
    known_failures = "SpecB | #2 | verdict_mismatch | active failure"
    results = "RESULT|name=SpecB|tlc_status=success|tla2_status=liveness|overall=FAIL"

    stdout = _run_stale_scan(known_failures, results)
    assert "STALE ENTRY:" not in stdout, f"Expected no stale entries for active failure, got: {stdout!r}"
