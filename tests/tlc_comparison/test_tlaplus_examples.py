# Copyright 2026 Andrew Yates.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""
TLA+ Examples Test Suite

Parametrized tests covering all TLA+ example specifications.
    Compares TLA2 results against cached TLC baselines (preferred:
    spec_baseline.json, fallback: expected_results.json).

To regenerate the cache:
    python scripts/collect_tlc_baseline.py
    python tests/tlc_comparison/generate_expected_results.py  # legacy

To run tests using cache (default, fast):
    # Recommended venv:
    #   python3 -m venv tests/tlc_comparison/venv
    #   tests/tlc_comparison/venv/bin/pip install -r tests/tlc_comparison/requirements.txt
    tests/tlc_comparison/venv/bin/python -m pytest tests/tlc_comparison/ -m fast

To run tests with live TLC comparison (slow):
    tests/tlc_comparison/venv/bin/python -m pytest tests/tlc_comparison/ --live-tlc
"""

import json
import time
import pytest
from pathlib import Path
from typing import Optional, Dict, Any
from .conftest import run_tlc, run_tla2, CheckResult
from .spec_catalog import (
    ALL_SPECS,
    LARGE_SPECS,
    TLA2_LIMITATIONS,
    TLA2_BUGS,
    get_fast_specs,
    SpecInfo,
)


# Cache for expected results
_EXPECTED_RESULTS: Optional[Dict[str, Any]] = None
_SPEC_BASELINE: Optional[Dict[str, Any]] = None

_ACCEPTABLE_ERROR_TYPE_MISMATCHES = {
    ("invariant", "safety"),
    ("safety", "invariant"),
    ("liveness", "temporal"),
    ("temporal", "liveness"),
    ("unknown", "liveness"),
    ("unknown", "safety"),
}


def _assert_error_types_compatible(
    spec_name: str,
    *,
    tlc_error_type: Optional[str],
    tla2_error_type: Optional[str],
    tlc_raw_output: str,
    tla2_raw_output: str,
    tlc_log_path: Optional[str] = None,
    tla2_log_path: Optional[str] = None,
) -> None:
    if tlc_error_type == tla2_error_type:
        return

    pair = (tlc_error_type, tla2_error_type)
    assert pair in _ACCEPTABLE_ERROR_TYPE_MISMATCHES, (
        f"{spec_name}: error type mismatch\n"
        f"  TLC:  {tlc_error_type}\n"
        f"  TLA2: {tla2_error_type}\n"
        f"  TLC log:  {tlc_log_path or '(not recorded)'}\n"
        f"  TLA2 log: {tla2_log_path or '(not recorded)'}\n"
        f"  TLA2 output: {tla2_raw_output[-500:]}\n"
        f"  TLC output:  {tlc_raw_output[-500:]}"
    )


@pytest.mark.no_tla2_build
def test_error_type_mismatch_policy_is_strict() -> None:
    _assert_error_types_compatible(
        "SpecAllowlisted",
        tlc_error_type="invariant",
        tla2_error_type="safety",
        tlc_raw_output="",
        tla2_raw_output="",
    )

    with pytest.raises(AssertionError):
        _assert_error_types_compatible(
            "SpecNotAllowlisted",
            tlc_error_type="deadlock",
            tla2_error_type="invariant",
            tlc_raw_output="TLC tail",
            tla2_raw_output="TLA2 tail",
        )


def load_expected_results() -> Dict[str, Any]:
    """Load cached TLC results from expected_results.json."""
    global _EXPECTED_RESULTS
    if _EXPECTED_RESULTS is not None:
        return _EXPECTED_RESULTS

    cache_path = Path(__file__).parent / "expected_results.json"
    if not cache_path.exists():
        return {"specs": {}, "_metadata": {}}

    with open(cache_path) as f:
        _EXPECTED_RESULTS = json.load(f)
    return _EXPECTED_RESULTS


def load_spec_baseline() -> Dict[str, Any]:
    """Load cached TLC baselines from spec_baseline.json."""
    global _SPEC_BASELINE
    if _SPEC_BASELINE is not None:
        return _SPEC_BASELINE

    cache_path = Path(__file__).parent / "spec_baseline.json"
    if not cache_path.exists():
        _SPEC_BASELINE = {"specs": {}, "_metadata": {}}
        return _SPEC_BASELINE

    with open(cache_path) as f:
        _SPEC_BASELINE = json.load(f)
    return _SPEC_BASELINE


def get_expected(spec_name: str) -> Optional[Dict[str, Any]]:
    """Get expected results for a spec."""
    results = load_expected_results()
    return results.get("specs", {}).get(spec_name)


def get_baseline(spec_name: str) -> Optional[Dict[str, Any]]:
    """Get TLC baseline for a spec (preferred: spec_baseline.json)."""
    baseline = load_spec_baseline()
    spec_data = baseline.get("specs", {}).get(spec_name)
    if isinstance(spec_data, dict):
        return spec_data
    expected = get_expected(spec_name)
    if isinstance(expected, dict):
        return expected
    return None


def format_performance_comparison(
    tla2_time: float,
    tlc_mean: float,
    tlc_stddev: float,
    runs_count: int
) -> str:
    """Format performance comparison string."""
    if tlc_mean <= 0:
        return f"TLA2 {tla2_time:.1f}s (no TLC baseline)"

    ratio = tla2_time / tlc_mean
    if ratio < 1.0:
        return f"TLA2 {tla2_time:.1f}s vs TLC {tlc_mean:.1f}s ({ratio:.1f}x = faster!, n={runs_count})"
    else:
        stddev_str = f"+/-{tlc_stddev:.1f}s" if tlc_stddev > 0 else ""
        return f"TLA2 {tla2_time:.1f}s vs TLC {tlc_mean:.1f}s{stddev_str} ({ratio:.1f}x slower, n={runs_count})"


def make_test_id(spec: SpecInfo) -> str:
    """Create a readable test ID."""
    return spec.name


def get_timeout(spec: SpecInfo) -> int:
    """Get timeout for a spec."""
    return LARGE_SPECS.get(spec.name, spec.timeout_seconds)


# Generate pytest parameters for all runnable specs
def _make_marks(spec: SpecInfo):
    """Generate pytest marks for a spec."""
    marks = []

    # Keep a visible annotation for known limitations/bugs, but do not skip.
    # (See #334: zero skips; every spec must run and either pass or fail.)
    if spec.name in TLA2_LIMITATIONS:
        marks.append(pytest.mark.limitations(reason=TLA2_LIMITATIONS[spec.name]))
    elif spec.name in TLA2_BUGS:
        marks.append(pytest.mark.bug(reason=TLA2_BUGS[spec.name]))

    if spec.name in LARGE_SPECS:
        marks.append(pytest.mark.slow)
        # Override pytest-timeout for large specs (add buffer for TLC+TLA2)
        marks.append(pytest.mark.timeout(LARGE_SPECS[spec.name] * 2 + 60))
    else:
        # Keep known-bad specs out of `-m fast` runs.
        if spec.name not in TLA2_LIMITATIONS and spec.name not in TLA2_BUGS:
            marks.append(pytest.mark.fast)
        # Ensure pytest-timeout doesn't preempt the subprocess-run timeout.
        # We prefer to report a structured timeout via `run_tla2(..., timeout=...)`
        # instead of a hard pytest-timeout failure.
        marks.append(pytest.mark.timeout(spec.timeout_seconds + 30))
    return marks


RUNNABLE_SPECS = [
    pytest.param(
        spec,
        id=make_test_id(spec),
        marks=_make_marks(spec),
    )
    for spec in ALL_SPECS
]

# Fast specs only (for quick CI runs)
FAST_SPECS = [
    pytest.param(spec, id=make_test_id(spec))
    for spec in get_fast_specs()
]


@pytest.mark.parametrize("spec", RUNNABLE_SPECS)
def test_tlc_equivalence(examples_dir: Path, spec: SpecInfo, use_live_tlc: bool):
    """Test that TLA2 matches TLC on this spec.

    Uses cached TLC results by default. Pass --live-tlc to run TLC live.
    """
    spec_path = examples_dir / spec.tla_path
    config_path = examples_dir / spec.cfg_path

    if not spec_path.exists():
        pytest.fail(f"Spec not found: {spec_path}")
    if not config_path.exists():
        pytest.fail(f"Config not found: {config_path}")

    timeout = get_timeout(spec)

    # Get TLC baseline (cached or live)
    cached = get_baseline(spec.name)

    if use_live_tlc or cached is None:
        # Live TLC mode or no cache available
        tlc = run_tlc(spec_path, config_path, timeout=timeout)
        if tlc.error_type == "timeout":
            pytest.fail(f"{spec.name}: TLC timeout after {timeout}s")
        tlc_states = tlc.distinct_states
        tlc_has_error = tlc.has_error
        tlc_error_type = tlc.error_type
        tlc_parsed = tlc.error_type != "parse"
        tlc_raw_output = tlc.raw_output
        tlc_mean = 0.0
        tlc_stddev = 0.0
        tlc_runs = 0
    else:
        # Use cached results
        # Schema v3: namespaced under "tlc" subobject
        if "tlc" in cached and isinstance(cached.get("tlc"), dict):
            # spec_baseline.json v3 format
            tlc_data = cached["tlc"]
            tlc_states = tlc_data.get("states", 0) or 0
            tlc_error_type = tlc_data.get("error_type")
            tlc_status = tlc_data.get("status")
            if tlc_status == "timeout" and tlc_error_type is None:
                tlc_error_type = "timeout"
            elif tlc_status == "error" and tlc_error_type is None:
                tlc_error_type = "unknown"
            tlc_has_error = tlc_error_type is not None
            tlc_parsed = tlc_error_type != "parse"
            tlc_raw_output = ""  # Not available in cache

            tlc_mean = float(tlc_data.get("runtime_seconds") or 0.0)
            tlc_stddev = 0.0
            tlc_runs = 1 if tlc_mean > 0 else 0
        elif "expected_states" in cached:
            # spec_baseline.json v2 format
            tlc_states = cached.get("expected_states", 0) or 0
            tlc_error_type = cached.get("error_type")
            if cached.get("status") == "timeout" and tlc_error_type is None:
                tlc_error_type = "timeout"
            elif cached.get("status") == "error" and tlc_error_type is None:
                tlc_error_type = "unknown"
            tlc_has_error = tlc_error_type is not None
            tlc_parsed = tlc_error_type != "parse"
            tlc_raw_output = ""  # Not available in cache

            tlc_mean = float(cached.get("tlc_runtime_seconds") or 0.0)
            tlc_stddev = 0.0
            tlc_runs = 1 if tlc_mean > 0 else 0
        else:
            # expected_results.json legacy format
            tlc_states = cached.get("distinct_states", 0)
            tlc_has_error = cached.get("has_error", False)
            tlc_error_type = cached.get("error_type")
            tlc_parsed = tlc_error_type != "parse"
            tlc_raw_output = ""  # Not available in cache

            # Get runtime stats
            stats = cached.get("runtime_stats", {})
            tlc_mean = stats.get("mean_seconds", 0.0)
            tlc_stddev = stats.get("stddev_seconds", 0.0)
            tlc_runs = stats.get("runs_count", 0)

    # Run TLA2 and measure time
    start_time = time.time()
    tla2 = run_tla2(spec_path, config_path, timeout=timeout)
    tla2_time = time.time() - start_time

    # Parse error handling
    tla2_parsed = tla2.error_type != "parse"

    if not tlc_parsed and not tla2_parsed:
        return  # Equivalent: both fail to parse/semantically analyze
    elif tlc_parsed and not tla2_parsed:
        assert False, (
            f"{spec.name}: TLA2 PARSER BUG - TLC parses OK but TLA2 fails\n"
            f"  TLA2 log: {tla2.log_path or '(not recorded)'}\n"
            f"  TLA2 error: {tla2.raw_output[-500:]}"
        )
    elif not tlc_parsed and tla2_parsed:
        tlc_tail = tlc_raw_output[-500:] if tlc_raw_output else "(no TLC output; cached baseline)"
        assert False, (
            f"{spec.name}: TLC parse error but TLA2 parses OK\n"
            f"  TLC log:  {getattr(tlc, 'log_path', None) if use_live_tlc or cached is None else '(not recorded)'}\n"
            f"  TLA2 log: {tla2.log_path or '(not recorded)'}\n"
            f"  TLC output:  {tlc_tail}\n"
            f"  TLA2 output: {tla2.raw_output[-500:]}"
        )

    # Compare error detection first
    if tlc_has_error and tla2.has_error:
        _assert_error_types_compatible(
            spec.name,
            tlc_error_type=tlc_error_type,
            tla2_error_type=tla2.error_type,
            tlc_raw_output=tlc_raw_output,
            tla2_raw_output=tla2.raw_output,
            tlc_log_path=getattr(tlc, "log_path", None) if use_live_tlc or cached is None else None,
            tla2_log_path=tla2.log_path,
        )
        # Print performance comparison
        perf = format_performance_comparison(tla2_time, tlc_mean, tlc_stddev, tlc_runs)
        print(f"\n{spec.name}: {perf}")
        return  # Test passes
    elif tlc_has_error != tla2.has_error:
        tlc_tail = tlc_raw_output[-500:] if tlc_raw_output else "(no TLC output; cached baseline)"
        assert False, (
            f"{spec.name}: error detection mismatch\n"
            f"  TLA2 has_error: {tla2.has_error} ({tla2.error_type})\n"
            f"  TLC has_error:  {tlc_has_error} ({tlc_error_type})\n"
            f"  TLC log:  {getattr(tlc, 'log_path', None) if use_live_tlc or cached is None else '(not recorded)'}\n"
            f"  TLA2 log: {tla2.log_path or '(not recorded)'}\n"
            f"  TLA2 output: {tla2.raw_output[-500:]}\n"
            f"  TLC output:  {tlc_tail}"
        )

    # Compare state counts
    assert tla2.distinct_states == tlc_states, (
        f"{spec.name}: state count mismatch\n"
        f"  TLA2: {tla2.distinct_states} states\n"
        f"  TLC:  {tlc_states} states\n"
        f"  TLC log:  {getattr(tlc, 'log_path', None) if use_live_tlc or cached is None else '(not recorded)'}\n"
        f"  TLA2 log: {tla2.log_path or '(not recorded)'}\n"
        f"  TLC output:  {(tlc_raw_output[-300:] if tlc_raw_output else '(no TLC output; cached baseline)')}\n"
        f"  TLA2 output: {tla2.raw_output[-300:]}"
    )

    # Print performance comparison
    perf = format_performance_comparison(tla2_time, tlc_mean, tlc_stddev, tlc_runs)
    print(f"\n{spec.name}: {perf}")


@pytest.mark.fast
@pytest.mark.parametrize("spec", FAST_SPECS[:20])  # First 20 fast specs
def test_fast_smoke(examples_dir: Path, spec: SpecInfo):
    """Quick smoke test on fast specs."""
    spec_path = examples_dir / spec.tla_path
    config_path = examples_dir / spec.cfg_path

    if not spec_path.exists():
        pytest.fail(f"Spec not found: {spec_path}")
    if not config_path.exists():
        pytest.fail(f"Config not found: {config_path}")

    # Just verify TLA2 doesn't crash
    tla2 = run_tla2(spec_path, config_path, timeout=60)

    # Should either complete successfully or find an expected error
    assert tla2.error_type != "parse", (
        f"{spec.name}: TLA2 parse error\n{tla2.raw_output[-500:]}"
    )


class TestCategorySmoke:
    """Quick smoke tests by category - uses cached TLC results."""

    @pytest.fixture
    def run_category_test(self, examples_dir, use_live_tlc):
        """Helper to run a spec by name - uses cache by default."""
        def _run(spec_name: str) -> tuple[int, CheckResult, Optional[CheckResult]]:
            from .spec_catalog import get_spec_by_name
            spec = get_spec_by_name(spec_name)
            if not spec:
                pytest.fail(f"Spec {spec_name} not in catalog")

            spec_path = examples_dir / spec.tla_path
            config_path = examples_dir / spec.cfg_path

            if not spec_path.exists():
                pytest.fail(f"Spec not found: {spec_path}")

            timeout = get_timeout(spec)

            # Use cache unless --live-tlc is passed
            expected = get_expected(spec_name)
            if use_live_tlc or expected is None:
                tlc = run_tlc(spec_path, config_path, timeout=timeout)
                tlc_states = tlc.distinct_states
            else:
                tlc = None
                tlc_states = expected.get("distinct_states", 0)

            tla2 = run_tla2(spec_path, config_path, timeout=timeout)
            return tlc_states, tla2, tlc
        return _run

    def test_diehard(self, run_category_test):
        """DieHard water jug puzzle."""
        tlc_states, tla2, tlc = run_category_test("DieHard")
        assert tla2.distinct_states == tlc_states, (
            "DieHard: state count mismatch\n"
            f"  TLA2: {tla2.distinct_states} states\n"
            f"  TLC:  {tlc_states} states\n"
            f"  TLC log:  {tlc.log_path if tlc else '(not recorded)'}\n"
            f"  TLA2 log: {tla2.log_path or '(not recorded)'}\n"
        )

    def test_tcommit(self, run_category_test):
        """Transaction commit."""
        tlc_states, tla2, tlc = run_category_test("TCommit")
        assert tla2.distinct_states == tlc_states, (
            "TCommit: state count mismatch\n"
            f"  TLA2: {tla2.distinct_states} states\n"
            f"  TLC:  {tlc_states} states\n"
            f"  TLC log:  {tlc.log_path if tlc else '(not recorded)'}\n"
            f"  TLA2 log: {tla2.log_path or '(not recorded)'}\n"
        )

    def test_tokenring(self, run_category_test):
        """Token ring termination detection."""
        tlc_states, tla2, tlc = run_category_test("TokenRing")
        assert tla2.distinct_states == tlc_states, (
            "TokenRing: state count mismatch\n"
            f"  TLA2: {tla2.distinct_states} states\n"
            f"  TLC:  {tlc_states} states\n"
            f"  TLC log:  {tlc.log_path if tlc else '(not recorded)'}\n"
            f"  TLA2 log: {tla2.log_path or '(not recorded)'}\n"
        )

    def test_dining_philosophers(self, run_category_test):
        """Dining philosophers."""
        tlc_states, tla2, tlc = run_category_test("DiningPhilosophers")
        assert tla2.distinct_states == tlc_states, (
            "DiningPhilosophers: state count mismatch\n"
            f"  TLA2: {tla2.distinct_states} states\n"
            f"  TLC:  {tlc_states} states\n"
            f"  TLC log:  {tlc.log_path if tlc else '(not recorded)'}\n"
            f"  TLA2 log: {tla2.log_path or '(not recorded)'}\n"
        )
