# Copyright 2026 Dropbox.
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

run_verify_correctness_python_fast_suite() {
# === Python tests (W7: Integrate Python tests into verify_correctness.sh) ===
# Run a subset of Python tests for quick validation
# Full test suite can be run separately with: pytest tests/tlc_comparison/ -m fast
echo ""
echo "=== Running Python TLC Comparison Tests (fast subset) ==="

local pytest_py=""
for cand in \
    "$REPO_ROOT/venv/bin/python" \
    "$REPO_ROOT/tests/tlc_comparison/venv/bin/python" \
    "$REPO_ROOT/tests/tlc_comparison/.venv/bin/python"
do
    if [ -x "$cand" ]; then
        pytest_py="$cand"
        break
    fi
done

if [ -n "$pytest_py" ]; then
    # Run only fast tests to keep verification quick
    # -m fast: only fast-marked tests
    # -x: stop on first failure
    # --tb=short: short traceback
    local pytest_log_dir="$REPO_ROOT/reports/prover/artifacts"
    mkdir -p "$pytest_log_dir"
    local pytest_log="$pytest_log_dir/pytest_tlc_comparison_fast_$(date -u +%Y-%m-%dT%H%M%SZ).txt"
    echo "Python TLC comparison log: $pytest_log"
    if run_with_heartbeat_tee 60 "Python TLC comparison tests still running" "$pytest_log" \
        "$pytest_py" -u -m pytest tests/tlc_comparison/test_tlaplus_examples.py -m fast -vv -x --tb=short
    then
        echo "[ PASS ] Python TLC comparison tests"
        PASS=$((PASS + 1))
    else
        echo "[ FAIL ] Python TLC comparison tests"
        tail -n 200 "$pytest_log" || true
        FAIL=$((FAIL + 1))
    fi
else
    echo "[ SKIP ] Python tests - venv/pytest not found"
    echo "         To enable (recommended):"
    echo "           python3 -m venv tests/tlc_comparison/venv"
    echo "           tests/tlc_comparison/venv/bin/pip install -r tests/tlc_comparison/requirements.txt"
    SKIP=$((SKIP + 1))
fi
}
