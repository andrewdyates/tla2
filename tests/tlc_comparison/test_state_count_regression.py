# Copyright 2026 Dropbox.
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

"""
State Count Regression Tests

Verifies that key specs produce exact state counts matching TLC.
These are regression tests for bugs that have been fixed in TLA2.

Each entry documents:
- The spec name and path
- Expected state count (verified against TLC)
- The bug/fix reference
- Whether an error is expected

This is verification tooling - state counts MUST match TLC exactly.

Part of #83 - regression test coverage for state counts.
"""

import pytest
from pathlib import Path
from typing import NamedTuple, Optional
from .conftest import run_tla2, run_tlc, CheckResult


class RegressionSpec(NamedTuple):
    """Specification for regression testing."""
    name: str
    tla_path: str
    cfg_path: str
    expected_states: int
    expects_error: bool
    error_type: Optional[str]
    timeout: int
    bug_ref: str  # Reference to bug/fix (issue number or commit)
    known_bug: Optional[str] = None  # Description of known TLA2 bug (for labeling)


# Regression test table: specs where bugs were fixed
# Each entry documents the TLC-verified state count
REGRESSION_SPECS = [
    # === Paxos Family ===
    # FastPaxos: Init enumeration fix for CONSTANT Ballot handling
    RegressionSpec(
        name="FastPaxos",
        tla_path="SimplifiedFastPaxos/FastPaxos.tla",
        cfg_path="SimplifiedFastPaxos/FastPaxos.cfg",
        expected_states=25617,  # TLC: 25617 distinct states
        expects_error=False,
        error_type=None,
        timeout=300,
        bug_ref="W#94",
    ),
    # PaxosCommit: Large spec, 1.3M states
    # Regression coverage for:
    # - #86: symmetry canonicalization
    # - #100: recursive Maximum over SUBSET / memoization + cache dependency tracking
    RegressionSpec(
        name="PaxosCommit",
        tla_path="transaction_commit/PaxosCommit.tla",
        cfg_path="transaction_commit/PaxosCommit.cfg",
        expected_states=1321761,  # TLC: 1321761 distinct states (verified 2026-01-12)
        expects_error=False,
        error_type=None,
        timeout=600,  # ~107s TLC runtime
        bug_ref="#86/#100",
    ),
    # === Allocator Family ===
    # AllocatorImplementation: FIXED - was false positive property violation (#256/#948)
    RegressionSpec(
        name="AllocatorImplementation",
        tla_path="allocator/AllocatorImplementation.tla",
        cfg_path="allocator/AllocatorImplementation.cfg",
        expected_states=17701,  # TLC: 17701 distinct states, no errors
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="34b73b1/#87",
    ),
    # AllocatorRefinement: FIXED - was false positive property violation (#256/#948)
    RegressionSpec(
        name="AllocatorRefinement",
        tla_path="allocator/AllocatorRefinement.tla",
        cfg_path="allocator/AllocatorRefinement.cfg",
        expected_states=1690,  # TLC: 1690 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="W#45/14da02d",
    ),
    # === YoYo (W#45 fixes) ===
    # MCYoYoPruning: REGRESSED - false positive invariant violation (#256)
    RegressionSpec(
        name="MCYoYoPruning",
        tla_path="YoYo/MCYoYoPruning.tla",
        cfg_path="YoYo/MCYoYoPruning.cfg",
        expected_states=102,  # TLC: 102 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="W#45/14da02d",
        known_bug="False positive 'Invariant FinishIffTerminated violated' - TLC finds no errors (#256)",
    ),
    # MCYoYoNoPruning: Working spec
    RegressionSpec(
        name="MCYoYoNoPruning",
        tla_path="YoYo/MCYoYoNoPruning.tla",
        cfg_path="YoYo/MCYoYoNoPruning.cfg",
        expected_states=60,  # TLC: 60 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="verified 2026-01-05",
    ),
    # === Mutex (W#93 fixes) ===
    # dijkstra-mutex: Stuttering edge fix for liveness
    RegressionSpec(
        name="dijkstra-mutex_LSpec-model",
        tla_path="dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC.tla",
        cfg_path="dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC.cfg",
        expected_states=90882,  # TLC: 90882 distinct states
        expects_error=False,
        error_type=None,
        timeout=300,  # ~13s TLC, allow buffer
        bug_ref="W#93/b2b2179",
    ),
    # === Cache specs ===
    # MCWriteThroughCache: FIXED - was false positive, now works correctly
    RegressionSpec(
        name="MCWriteThroughCache",
        tla_path="SpecifyingSystems/CachingMemory/MCWriteThroughCache.tla",
        cfg_path="SpecifyingSystems/CachingMemory/MCWriteThroughCache.cfg",
        expected_states=5196,  # TLC: 5196 distinct states, no errors
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="P#117 (verified 2026-01-17)",
    ),
    # MCLiveInternalMemory: Working correctly
    RegressionSpec(
        name="MCLiveInternalMemory",
        tla_path="SpecifyingSystems/Liveness/MCLiveInternalMemory.tla",
        cfg_path="SpecifyingSystems/Liveness/MCLiveInternalMemory.cfg",
        expected_states=4408,  # TLC: 4408 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="W#45/14da02d",
    ),
    # MCLiveWriteThroughCache: FIXED - was 'Undefined variable: r' during liveness check
    RegressionSpec(
        name="MCLiveWriteThroughCache",
        tla_path="SpecifyingSystems/Liveness/MCLiveWriteThroughCache.tla",
        cfg_path="SpecifyingSystems/Liveness/MCLiveWriteThroughCache.cfg",
        expected_states=5196,  # TLC: 5196 distinct states, no errors
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="verified passing 2026-01-17",
    ),
    # === Cat Puzzle (f7e6163 fix) ===
    # CatEvenBoxes: Stuttering edge fix
    RegressionSpec(
        name="CatEvenBoxes",
        tla_path="Moving_Cat_Puzzle/Cat.tla",
        cfg_path="Moving_Cat_Puzzle/CatEvenBoxes.cfg",
        expected_states=48,  # TLC: 48 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="f7e6163",
    ),
    # CatOddBoxes: Stuttering edge fix
    RegressionSpec(
        name="CatOddBoxes",
        tla_path="Moving_Cat_Puzzle/Cat.tla",
        cfg_path="Moving_Cat_Puzzle/CatOddBoxes.cfg",
        expected_states=30,  # TLC: 30 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="f7e6163",
    ),
    # === Chronic regressors (#3036) ===
    # Peterson: Regressed 3+ times (#264, #266, #2949, #2983, #3030).
    # property_classify.rs from_module_ref guard is fragile under INSTANCE changes.
    RegressionSpec(
        name="Peterson",
        tla_path="locks_auxiliary_vars/Peterson.tla",
        cfg_path="locks_auxiliary_vars/Peterson.cfg",
        expected_states=42,  # TLC: 42 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="#3036 (chronic regressor)",
    ),
    # EWD998ChanID: Regressed 3+ times (#322, #2953, #2995, #3030).
    # Same from_module_ref guard fragility as Peterson.
    RegressionSpec(
        name="EWD998ChanID",
        tla_path="ewd998/EWD998ChanID.tla",
        cfg_path="ewd998/EWD998ChanID.cfg",
        expected_states=14,  # TLC: 14 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="#3036 (chronic regressor)",
    ),
    # === Classic specs (baseline) ===
    # DieHard: Invariant violation expected (NotSolved violated when solved)
    RegressionSpec(
        name="DieHard",
        tla_path="DieHard/DieHard.tla",
        cfg_path="DieHard/DieHard.cfg",
        expected_states=14,  # TLC: 14 distinct states
        expects_error=True,
        error_type="invariant",
        timeout=60,
        bug_ref="baseline",
    ),
    # TCommit: Transaction commit baseline
    RegressionSpec(
        name="TCommit",
        tla_path="transaction_commit/TCommit.tla",
        cfg_path="transaction_commit/TCommit.cfg",
        expected_states=34,  # TLC: 34 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="baseline",
    ),
    # TwoPhase: Two-phase commit baseline
    RegressionSpec(
        name="TwoPhase",
        tla_path="transaction_commit/TwoPhase.tla",
        cfg_path="transaction_commit/TwoPhase.cfg",
        expected_states=288,  # TLC: 288 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="baseline",
    ),
    # DiningPhilosophers: Classic baseline
    RegressionSpec(
        name="DiningPhilosophers",
        tla_path="DiningPhilosophers/DiningPhilosophers.tla",
        cfg_path="DiningPhilosophers/DiningPhilosophers.cfg",
        expected_states=67,  # TLC: 67 distinct states
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="baseline",
    ),
    # === CHOOSE + SUBSET (bounded) ===
    # CigaretteSmokers: Exercises SUBSET in ASSUME and CHOOSE via ChooseOne.
    RegressionSpec(
        name="CigaretteSmokers",
        tla_path="CigaretteSmokers/CigaretteSmokers.tla",
        cfg_path="CigaretteSmokers/CigaretteSmokers.cfg",
        expected_states=6,  # TLC baseline: 6 distinct states (spec_baseline.json)
        expects_error=False,
        error_type=None,
        timeout=60,
        bug_ref="#996",
    ),
]


def _make_test_id(spec: RegressionSpec) -> str:
    """Create readable test ID."""
    return spec.name


def _make_marks(spec: RegressionSpec):
    """Generate pytest marks for a spec."""
    marks = []
    if spec.known_bug:
        marks.append(pytest.mark.bug(reason=spec.known_bug))
    # Override the global pytest-timeout (pytest.ini) for long-running specs.
    # Without this, specs like PaxosCommit will be killed at 120s regardless of spec.timeout.
    marks.append(pytest.mark.timeout(spec.timeout))
    if spec.timeout >= 300:
        marks.append(pytest.mark.slow)
    return marks


# Build parametrized list with marks
REGRESSION_PARAMS = [
    pytest.param(spec, id=_make_test_id(spec), marks=_make_marks(spec))
    for spec in REGRESSION_SPECS
]


@pytest.mark.parametrize("spec", REGRESSION_PARAMS)
def test_state_count_regression(examples_dir: Path, spec: RegressionSpec):
    """Verify TLA2 state count matches expected TLC baseline.

    This is a regression test - if this fails, a previously fixed bug
    may have regressed, or the expected count was wrong.
    """
    spec_path = examples_dir / spec.tla_path
    config_path = examples_dir / spec.cfg_path

    if not spec_path.exists():
        pytest.fail(f"Spec not found: {spec_path}")
    if not config_path.exists():
        pytest.fail(f"Config not found: {config_path}")

    # Run TLA2
    result = run_tla2(spec_path, config_path, timeout=spec.timeout)

    # Check for timeout
    if result.error_type == "timeout":
        pytest.fail(
            f"{spec.name}: TLA2 timed out after {spec.timeout}s "
            f"(bug ref: {spec.bug_ref})"
            + (f"\nLog: {result.log_path}" if result.log_path else "")
        )

    # Verify error detection matches expected
    if spec.expects_error:
        assert result.has_error, (
            f"{spec.name}: Expected error ({spec.error_type}) but TLA2 found none "
            f"(bug ref: {spec.bug_ref})"
        )
    else:
        assert not result.has_error, (
            f"{spec.name}: TLA2 found unexpected error ({result.error_type}) "
            f"(bug ref: {spec.bug_ref})\n"
            f"Log: {result.log_path or '(not recorded)'}\n"
            f"Output: {result.raw_output[-500:]}"
        )

    # Verify exact state count match
    assert result.distinct_states == spec.expected_states, (
        f"{spec.name}: State count mismatch (bug ref: {spec.bug_ref})\n"
        f"  Expected (TLC): {spec.expected_states}\n"
        f"  Got (TLA2):     {result.distinct_states}\n"
        f"  Delta:          {result.distinct_states - spec.expected_states}\n"
        f"  Log:            {result.log_path or '(not recorded)'}"
    )


# Fast-only specs for quick CI runs (excludes specs with timeout >= 300s)
FAST_REGRESSION_PARAMS = [
    pytest.param(spec, id=_make_test_id(spec), marks=_make_marks(spec))
    for spec in REGRESSION_SPECS
    if spec.timeout < 300 and spec.known_bug is None
]


@pytest.mark.fast
@pytest.mark.parametrize("spec", FAST_REGRESSION_PARAMS)
def test_fast_state_count_regression(examples_dir: Path, spec: RegressionSpec):
    """Fast regression tests (< 300s timeout).

    These run in CI on every commit. Use -m fast to run only these.
    """
    spec_path = examples_dir / spec.tla_path
    config_path = examples_dir / spec.cfg_path

    if not spec_path.exists():
        pytest.fail(f"Spec not found: {spec_path}")
    if not config_path.exists():
        pytest.fail(f"Config not found: {config_path}")

    result = run_tla2(spec_path, config_path, timeout=spec.timeout)

    if result.error_type == "timeout":
        pytest.fail(
            f"{spec.name}: TLA2 timed out after {spec.timeout}s"
            + (f"\nLog: {result.log_path}" if result.log_path else "")
        )

    if spec.expects_error:
        assert result.has_error, f"{spec.name}: Expected error but TLA2 found none"
    else:
        assert not result.has_error, (
            f"{spec.name}: TLA2 found unexpected error ({result.error_type})"
        )

    assert result.distinct_states == spec.expected_states, (
        f"{spec.name}: State count mismatch\n"
        f"  Expected: {spec.expected_states}, Got: {result.distinct_states}"
    )


class TestLiveComparison:
    """Live TLC comparison tests for validation.

    These tests run both TLA2 and TLC to verify the expected values
    are still correct. Run with --live-tlc flag.
    """

    @pytest.mark.parametrize(
        "spec",
        # Keep this list small (quick TLC validation), but include newly-added baselines.
        REGRESSION_SPECS[:5]
        + [s for s in REGRESSION_SPECS if s.name == "CigaretteSmokers"],
        ids=[_make_test_id(s) for s in REGRESSION_SPECS[:5]]
        + [s.name for s in REGRESSION_SPECS if s.name == "CigaretteSmokers"],
    )
    @pytest.mark.live_tlc
    def test_verify_expected_values(
        self, examples_dir: Path, spec: RegressionSpec
    ):
        """Verify expected values match current TLC output."""
        spec_path = examples_dir / spec.tla_path
        config_path = examples_dir / spec.cfg_path

        if not spec_path.exists():
            pytest.fail(f"Spec not found: {spec_path}")

        tlc = run_tlc(spec_path, config_path, timeout=spec.timeout)

        if tlc.error_type == "timeout":
            pytest.fail(f"{spec.name}: TLC timed out after {spec.timeout}s")

        # Verify our expected values are correct
        assert tlc.distinct_states == spec.expected_states, (
            f"{spec.name}: Expected value may be wrong!\n"
            f"  Documented: {spec.expected_states}\n"
            f"  TLC says:   {tlc.distinct_states}\n"
            f"  Please update REGRESSION_SPECS"
        )
