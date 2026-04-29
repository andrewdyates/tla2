# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""
TLC Equivalence Tests - CACHED VERSION

Verifies TLA2 produces semantically identical results to TLC.
Uses cached TLC results (preferred: spec_baseline.json, fallback:
expected_results.json) to avoid spawning Java processes.

To run with live TLC (slow, memory-intensive):
    # Recommended venv:
    #   python3 -m venv tests/tlc_comparison/venv
    #   tests/tlc_comparison/venv/bin/pip install -r tests/tlc_comparison/requirements.txt
    tests/tlc_comparison/venv/bin/python -m pytest tests/tlc_comparison/test_tlc_equivalence.py --live-tlc

To regenerate cache:
    python tests/tlc_comparison/generate_expected_results.py
"""

import json
import pytest
from pathlib import Path
from typing import Optional, Dict, Any
from .conftest import run_tlc, run_tla2


# ============================================================================
# Cache Management
# ============================================================================

_EXPECTED_RESULTS: Optional[Dict[str, Any]] = None
_SPEC_BASELINE: Optional[Dict[str, Any]] = None


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


def get_cached_tlc(spec_name: str) -> Optional[Dict[str, Any]]:
    """Get cached TLC results for a spec (preferred: spec_baseline.json)."""
    baseline = load_spec_baseline().get("specs", {}).get(spec_name)
    if isinstance(baseline, dict):
        return baseline
    results = load_expected_results().get("specs", {}).get(spec_name)
    if isinstance(results, dict):
        return results
    return None


def get_tlc_baseline(spec_name: str, spec_path: Path, config_path: Path,
                     use_live_tlc: bool, timeout: int = 120) -> tuple:
    """Get TLC baseline - from cache or live run.

    Returns: (distinct_states, has_error, error_type, raw_output)
    """
    if not use_live_tlc:
        cached = get_cached_tlc(spec_name)
        if cached:
            # Schema v3: namespaced under "tlc" subobject
            if "tlc" in cached and isinstance(cached.get("tlc"), dict):
                tlc_data = cached["tlc"]
                tlc_states = tlc_data.get("states", 0) or 0
                tlc_error_type = tlc_data.get("error_type")
                tlc_status = tlc_data.get("status")
                if tlc_status == "timeout" and tlc_error_type is None:
                    tlc_error_type = "timeout"
                elif tlc_status == "error" and tlc_error_type is None:
                    tlc_error_type = "unknown"
                tlc_has_error = tlc_error_type is not None
            elif "expected_states" in cached:
                # spec_baseline.json v2 format
                tlc_states = cached.get("expected_states", 0) or 0
                tlc_error_type = cached.get("error_type")
                if cached.get("status") == "timeout" and tlc_error_type is None:
                    tlc_error_type = "timeout"
                elif cached.get("status") == "error" and tlc_error_type is None:
                    tlc_error_type = "unknown"
                tlc_has_error = tlc_error_type is not None
            else:
                # expected_results.json legacy format
                tlc_states = cached.get("distinct_states", 0)
                tlc_has_error = cached.get("has_error", False)
                tlc_error_type = cached.get("error_type")
            return (tlc_states, tlc_has_error, tlc_error_type, "")

    # Fall back to live TLC
    tlc = run_tlc(spec_path, config_path, timeout=timeout)
    if tlc.error_type == "timeout":
        pytest.fail(f"{spec_name}: TLC timeout after {timeout}s")
    return (tlc.distinct_states, tlc.has_error, tlc.error_type, tlc.raw_output)


# ============================================================================
# Test Classes - Using Cached Results
# ============================================================================

class TestCoreAlgorithms:
    """Core algorithm specs - must match TLC exactly."""

    def test_diehard(self, examples_dir, use_live_tlc):
        """DieHard water jug puzzle - basic BFS."""
        spec = examples_dir / "DieHard" / "DieHard.tla"
        config = examples_dir / "DieHard" / "DieHard.cfg"

        tlc_states, tlc_error, _, _ = get_tlc_baseline(
            "DieHard", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        assert tlc_states == tla2.distinct_states, \
            f"State count mismatch: TLC={tlc_states}, TLA2={tla2.distinct_states}"
        assert tlc_error == tla2.has_error, \
            f"Error detection mismatch: TLC={tlc_error}, TLA2={tla2.has_error}"

    def test_tcommit(self, examples_dir, use_live_tlc):
        """Transaction commit - distributed commit protocol."""
        spec = examples_dir / "transaction_commit" / "TCommit.tla"
        config = examples_dir / "transaction_commit" / "TCommit.cfg"

        tlc_states, tlc_error, _, _ = get_tlc_baseline(
            "TCommit", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        assert tlc_states == tla2.distinct_states
        assert tlc_error == tla2.has_error

    def test_twophase(self, examples_dir, use_live_tlc):
        """Two-phase commit protocol."""
        spec = examples_dir / "transaction_commit" / "TwoPhase.tla"
        config = examples_dir / "transaction_commit" / "TwoPhase.cfg"

        tlc_states, tlc_error, _, _ = get_tlc_baseline(
            "TwoPhase", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        assert tlc_states == tla2.distinct_states
        assert tlc_error == tla2.has_error


class TestMutualExclusion:
    """Mutual exclusion algorithms."""

    def test_peterson(self, examples_dir, use_live_tlc):
        """Peterson's algorithm with TLAPS proofs."""
        spec = examples_dir / "locks_auxiliary_vars" / "Peterson.tla"
        config = examples_dir / "locks_auxiliary_vars" / "Peterson.cfg"

        tlc_states, tlc_error, tlc_error_type, _ = get_tlc_baseline(
            "Peterson", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        if tlc_error_type == 'parse':
            pytest.fail("TLC parse error (cached baseline); regenerate baselines or run with --live-tlc")

        assert tlc_states == tla2.distinct_states
        assert tlc_error == tla2.has_error

    def test_lock(self, examples_dir, use_live_tlc):
        """Simple lock with auxiliary variables."""
        spec = examples_dir / "locks_auxiliary_vars" / "Lock.tla"
        config = examples_dir / "locks_auxiliary_vars" / "Lock.cfg"

        tlc_states, tlc_error, tlc_error_type, _ = get_tlc_baseline(
            "Lock", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        if tlc_error_type == 'parse':
            pytest.fail("TLC parse error (cached baseline); regenerate baselines or run with --live-tlc")

        assert tlc_states == tla2.distinct_states
        assert tlc_error == tla2.has_error

    def test_mcbakery(self, examples_dir, test_specs_dir, use_live_tlc):
        """Lamport's Bakery algorithm with TLAPS."""
        spec = examples_dir / "Bakery-Boulangerie" / "MCBakery.tla"
        config = test_specs_dir / "MCBakery.cfg"

        tlc_states, tlc_error, tlc_error_type, _ = get_tlc_baseline(
            "MCBakery", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        if tlc_error_type == 'parse':
            pytest.fail("TLC parse error (cached baseline); regenerate baselines or run with --live-tlc")

        assert tlc_states == tla2.distinct_states, \
            f"MCBakery: TLC={tlc_states}, TLA2={tla2.distinct_states}"
        assert tlc_error == tla2.has_error

    def test_mcboulanger_small(self, examples_dir, test_specs_dir, use_live_tlc):
        """Boulangerie algorithm (small config) - exercises prime-dependent IF extraction."""
        spec = examples_dir / "Bakery-Boulangerie" / "MCBoulanger.tla"
        config = test_specs_dir / "MCBoulanger_small.cfg"

        tlc_states, tlc_error, tlc_error_type, _ = get_tlc_baseline(
            "MCBoulanger_small", spec, config, use_live_tlc, timeout=60)
        tla2 = run_tla2(spec, config, timeout=60)

        if tlc_error_type == 'parse':
            pytest.fail("TLC parse error (cached baseline); regenerate baselines or run with --live-tlc")

        assert tlc_states == tla2.distinct_states, \
            f"MCBoulanger_small: TLC={tlc_states}, TLA2={tla2.distinct_states}"
        assert tlc_error == tla2.has_error


class TestDistributedSystems:
    """Distributed algorithm specs."""

    @pytest.mark.nightly
    # TokenRing can take up to 180s per checker; when running with
    # --live-tlc we execute TLC and TLA2 sequentially, so use 2x + buffer.
    @pytest.mark.timeout(420)
    def test_tokenring(self, examples_dir, use_live_tlc):
        """EWD426 Token Ring termination detection."""
        spec = examples_dir / "ewd426" / "TokenRing.tla"
        config = examples_dir / "ewd426" / "TokenRing.cfg"

        tlc_states, _, _, _ = get_tlc_baseline(
            "TokenRing", spec, config, use_live_tlc, timeout=180)
        tla2 = run_tla2(spec, config, timeout=180)

        assert tlc_states == tla2.distinct_states, \
            f"TokenRing: TLC={tlc_states}, TLA2={tla2.distinct_states}"

    def test_mcchangroberts(self, examples_dir, use_live_tlc):
        """Chang-Roberts leader election."""
        spec = examples_dir / "chang_roberts" / "MCChangRoberts.tla"
        config = examples_dir / "chang_roberts" / "MCChangRoberts.cfg"

        tlc_states, _, _, _ = get_tlc_baseline(
            "MCChangRoberts", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        assert tlc_states == tla2.distinct_states

    @pytest.mark.nightly
    # Huang can exceed 300s per checker on loaded hosts; when running with
    # --live-tlc we execute TLC and TLA2 sequentially, so use 2x + buffer.
    @pytest.mark.timeout(1260)
    def test_huang(self, examples_dir, use_live_tlc):
        """Huang termination detection."""
        spec = examples_dir / "Huang" / "Huang.tla"
        config = examples_dir / "Huang" / "Huang.cfg"

        tlc_states, _, _, _ = get_tlc_baseline(
            "Huang", spec, config, use_live_tlc, timeout=600)
        tla2 = run_tla2(spec, config, timeout=600)

        assert tlc_states == tla2.distinct_states, \
            f"Huang: TLC={tlc_states}, TLA2={tla2.distinct_states}"


class TestResourceAllocation:
    """Resource allocation specs."""

    def test_simple_allocator(self, examples_dir, use_live_tlc):
        """Simple resource allocator."""
        spec = examples_dir / "allocator" / "SimpleAllocator.tla"
        config = examples_dir / "allocator" / "SimpleAllocator.cfg"

        tlc_states, _, _, _ = get_tlc_baseline(
            "SimpleAllocator", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        assert tlc_states == tla2.distinct_states

    def test_scheduling_allocator(self, examples_dir, use_live_tlc):
        """Scheduling allocator with liveness."""
        spec = examples_dir / "allocator" / "SchedulingAllocator.tla"
        config = examples_dir / "allocator" / "SchedulingAllocator.cfg"

        tlc_states, _, _, _ = get_tlc_baseline(
            "SchedulingAllocator", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        assert tlc_states == tla2.distinct_states, \
            f"SchedulingAllocator: TLC={tlc_states}, TLA2={tla2.distinct_states}"


class TestClassicProblems:
    """Classic CS problems."""

    def test_dining_philosophers(self, examples_dir, use_live_tlc):
        """Dining philosophers deadlock detection."""
        spec = examples_dir / "DiningPhilosophers" / "DiningPhilosophers.tla"
        config = examples_dir / "DiningPhilosophers" / "DiningPhilosophers.cfg"

        tlc_states, _, _, _ = get_tlc_baseline(
            "DiningPhilosophers", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        assert tlc_states == tla2.distinct_states

    def test_missionaries_and_cannibals(self, examples_dir, use_live_tlc):
        """River crossing puzzle."""
        spec = examples_dir / "MissionariesAndCannibals" / "MissionariesAndCannibals.tla"
        config = examples_dir / "MissionariesAndCannibals" / "MissionariesAndCannibals.cfg"

        tlc_states, _, _, _ = get_tlc_baseline(
            "MissionariesAndCannibals", spec, config, use_live_tlc)
        tla2 = run_tla2(spec, config)

        assert tlc_states == tla2.distinct_states


# ============================================================================
# Smoke Tests - TLA2 only, no TLC spawning
# ============================================================================

# Format: (name, spec_path, config_path, expected_states, expects_error)
SMOKE_TEST_SPECS = [
    # DieHard: NotSolved invariant is violated when puzzle is solved (expected behavior)
    ("DieHard", "DieHard/DieHard.tla", "DieHard/DieHard.cfg", 14, True),
    ("TCommit", "transaction_commit/TCommit.tla", "transaction_commit/TCommit.cfg", 34, False),
    ("DiningPhilosophers", "DiningPhilosophers/DiningPhilosophers.tla",
     "DiningPhilosophers/DiningPhilosophers.cfg", 67, False),
]


@pytest.mark.parametrize("name,spec_path,config_path,expected_states,expects_error", SMOKE_TEST_SPECS)
def test_smoke(examples_dir, name, spec_path, config_path, expected_states, expects_error):
    """Quick smoke test with known expected values - NO TLC spawning."""
    spec = examples_dir / spec_path
    config = examples_dir / config_path

    tla2 = run_tla2(spec, config)

    assert tla2.distinct_states == expected_states, \
        f"{name}: expected {expected_states} states, got {tla2.distinct_states}"
    assert tla2.has_error == expects_error, \
        f"{name}: expected has_error={expects_error}, got {tla2.has_error}"
