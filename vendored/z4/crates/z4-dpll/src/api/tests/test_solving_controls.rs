// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for timeout, interrupt, unknown reason, statistics, and
//! check_sat_with_details.

use std::sync::atomic::Ordering;
use std::time::Duration;

use crate::api::*;

#[test]
fn test_timeout_setting() {
    let mut solver = Solver::new(Logic::QfLia);
    assert!(solver.get_timeout().is_none());
    solver.set_timeout(Some(Duration::from_secs(5)));
    assert_eq!(solver.get_timeout(), Some(Duration::from_secs(5)));
    solver.set_timeout(None);
    assert!(solver.get_timeout().is_none());
}

#[test]
fn test_interrupt_flag() {
    let solver = Solver::new(Logic::QfLia);
    assert!(!solver.is_interrupted());
    solver.interrupt();
    assert!(solver.is_interrupted());
    solver.clear_interrupt();
    assert!(!solver.is_interrupted());
}

#[test]
fn test_interrupt_handle_sharing() {
    let solver = Solver::new(Logic::QfLia);
    let handle = solver.get_interrupt_handle();
    assert!(!handle.load(Ordering::Relaxed));
    handle.store(true, Ordering::Relaxed);
    assert!(solver.is_interrupted());
}

#[test]
fn test_check_sat_respects_interrupt_before_start() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

#[test]
fn test_check_sat_assuming_respects_interrupt() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.interrupt();
    let result = solver.check_sat_assuming(&[x_ge_0]);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

#[test]
fn test_zero_timeout_returns_unknown() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

#[test]
fn test_reason_unknown_cleared_on_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.interrupt();
    let _ = solver.check_sat();
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
    solver.clear_interrupt();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
    assert!(solver.get_reason_unknown().is_none());
}

#[test]
fn test_reason_unknown_cleared_on_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.interrupt();
    let _ = solver.check_sat();
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
    solver.clear_interrupt();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_ge_0);
    solver.assert_term(x_lt_0);
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unsat);
    assert!(solver.get_reason_unknown().is_none());
}

#[test]
fn test_check_sat_assuming_zero_timeout() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat_assuming(&[x_ge_0]);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

#[test]
fn test_get_unknown_reason_structured() {
    // Test the structured UnknownReason API
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);

    // Test Interrupted reason
    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(
        solver.get_unknown_reason(),
        Some(UnknownReason::Interrupted)
    );
    solver.clear_interrupt();

    // Test Timeout reason
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_unknown_reason(), Some(UnknownReason::Timeout));
    solver.set_timeout(None);

    // Test that reason is cleared on SAT
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
    assert_eq!(solver.get_unknown_reason(), None);
}

#[test]
fn test_get_statistics_api() {
    // Test that Solver::get_statistics() returns stats from Executor
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let or_ab = solver.or(a, b);
    let not_a = solver.not(a);
    let not_b = solver.not(b);
    solver.assert_term(or_ab);
    solver.assert_term(not_a);
    solver.assert_term(not_b);

    // Should be UNSAT: (a v b) & ~a & ~b
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unsat);

    let stats = solver.get_statistics();
    // With UNSAT, we should see some solver activity
    assert!(
        stats.conflicts > 0 || stats.decisions > 0 || stats.propagations > 0,
        "Statistics should show some solver activity"
    );
}

#[test]
fn test_check_sat_with_statistics_returns_populated_stats() {
    // Verify that the convenience API returns both result and non-trivial stats
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let or_ab = solver.or(a, b);
    let not_a = solver.not(a);
    let not_b = solver.not(b);
    solver.assert_term(or_ab);
    solver.assert_term(not_a);
    solver.assert_term(not_b);

    let (result, stats) = solver.check_sat_with_statistics();
    assert_eq!(result, SolveResult::Unsat);
    assert_eq!(
        stats.num_assertions, 3,
        "Statistics should include the solved assertion count",
    );
    assert!(
        stats.conflicts > 0 || stats.decisions > 0 || stats.propagations > 0,
        "Statistics should show solver activity for the same check_sat call"
    );

    let latest = solver.get_statistics();
    assert_eq!(latest.conflicts, stats.conflicts);
    assert_eq!(latest.decisions, stats.decisions);
    assert_eq!(latest.propagations, stats.propagations);
    assert_eq!(latest.restarts, stats.restarts);
}

#[test]
fn test_check_sat_with_details_sat_has_model_validated() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(details.unknown_reason.is_none());
    assert!(details.verification.sat_model_validated);
    assert!(!details.verification.unsat_proof_available);
    assert_eq!(details.verification.unsat_proof_checker_failures, 0);
}

#[test]
fn test_check_sat_with_details_accepts_validated_sat_for_consumers_6852() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.accept_for_consumer(), Ok(SolveResult::Sat));
}

#[test]
fn test_check_sat_with_details_rejects_unvalidated_sat_for_consumers_6852() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(5, 11));
    let r = solver.declare_const("r", Sort::Real);
    let fp_to_real = solver.try_fp_to_real(x).unwrap();
    let eq = solver.eq(r, fp_to_real);
    solver.assert_term(eq);
    let one = solver.real_const(1.0);
    let gt = solver.gt(r, one);
    solver.assert_term(gt);

    let details = solver.check_sat_with_details();
    assert_eq!(
        details.accept_for_consumer(),
        Err(ConsumerAcceptanceError::SatModelNotValidated)
    );
}

/// Regression (#5777): `VerificationSummary` evidence counts are populated
/// with independent/delegated/incomplete provenance after a SAT solve.
#[test]
fn test_check_sat_with_details_evidence_counts_5777() {
    // A trivial QF_LIA formula with one independently-checkable assertion.
    // The evaluator should return Bool(true) for `(= x 5)` when the model
    // assigns x=5. This produces an independent check with zero delegation
    // and zero incomplete evidence.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(
        details.verification.sat_model_validated,
        "simple LIA formula should be model-validated"
    );
    // Independent checks must be > 0 for a validated SAT result.
    assert!(
        details.verification.sat_independent_checks > 0,
        "Expected independent checks > 0, got {}",
        details.verification.sat_independent_checks
    );
    assert_eq!(
        details.verification.sat_delegated_checks, 0,
        "Simple equality should not need theory-delegated evidence"
    );
    // No circular SAT fallback should be needed for a simple equality.
    assert_eq!(
        details.verification.sat_incomplete_checks, 0,
        "Simple equality should not need SAT fallback"
    );
}

/// Regression (#5777): theory-delegated string evidence must not inflate the
/// public independent-check counter.
#[test]
fn test_check_sat_with_details_delegated_string_evidence_5777() {
    let mut solver = Solver::new(Logic::QfS);
    let x = solver.string_var("x");
    let y = solver.string_var("y");
    let eq = solver.eq(x, y);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(
        details.verification.sat_model_validated,
        "simple string equality should validate via delegated string evidence"
    );
    assert_eq!(
        details.verification.sat_independent_checks, 0,
        "Delegated-only string proof must not count as independent evidence"
    );
    assert!(
        details.verification.sat_delegated_checks > 0,
        "Expected delegated string checks > 0, got {}",
        details.verification.sat_delegated_checks
    );
    assert_eq!(
        details.verification.sat_incomplete_checks, 0,
        "Simple delegated string equality should not need incomplete fallback"
    );
}

#[test]
fn test_check_sat_with_details_unsat_basic() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Unsat);
    assert!(details.unknown_reason.is_none());
    assert!(!details.verification.sat_model_validated);
}

#[test]
fn test_check_sat_with_details_unknown_timeout_has_reason() {
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);
    solver.set_timeout(Some(Duration::ZERO));

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Unknown);
    assert_eq!(details.unknown_reason, Some(UnknownReason::Timeout));
    assert_eq!(solver.get_unknown_reason(), Some(UnknownReason::Timeout));
}

#[test]
fn test_check_sat_with_details_statistics_match_get_statistics() {
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let a_or_b = solver.or(a, b);
    let not_a = solver.not(a);
    let not_b = solver.not(b);
    solver.assert_term(a_or_b);
    solver.assert_term(not_a);
    solver.assert_term(not_b);

    let details = solver.check_sat_with_details();
    let latest = solver.get_statistics();
    assert_eq!(details.statistics.conflicts, latest.conflicts);
    assert_eq!(details.statistics.decisions, latest.decisions);
    assert_eq!(details.statistics.propagations, latest.propagations);
    assert_eq!(details.statistics.restarts, latest.restarts);
}

#[test]
fn test_verification_level_from_state_no_proofs() {
    use crate::api::types::VerificationLevel;

    let level = VerificationLevel::from_state(false);
    if cfg!(debug_assertions) {
        assert_eq!(level, VerificationLevel::DebugChecked);
        assert!(level.has_debug_checks());
        assert!(!level.has_proof_checking());
        assert!(!level.is_trusted_only());
    } else {
        assert_eq!(level, VerificationLevel::Trusted);
        assert!(!level.has_debug_checks());
        assert!(!level.has_proof_checking());
        assert!(level.is_trusted_only());
    }
}

#[test]
fn test_verification_level_from_state_with_proofs() {
    use crate::api::types::VerificationLevel;

    let level = VerificationLevel::from_state(true);
    if cfg!(debug_assertions) {
        assert_eq!(level, VerificationLevel::FullyVerified);
        assert!(level.has_debug_checks());
        assert!(level.has_proof_checking());
        assert!(!level.is_trusted_only());
    } else {
        assert_eq!(level, VerificationLevel::ProofChecked);
        assert!(!level.has_debug_checks());
        assert!(level.has_proof_checking());
        assert!(!level.is_trusted_only());
    }
}

#[test]
fn test_verification_level_display() {
    use crate::api::types::VerificationLevel;

    assert_eq!(VerificationLevel::Trusted.to_string(), "trusted");
    assert_eq!(VerificationLevel::DebugChecked.to_string(), "debug-checked");
    assert_eq!(VerificationLevel::ProofChecked.to_string(), "proof-checked");
    assert_eq!(
        VerificationLevel::FullyVerified.to_string(),
        "fully-verified"
    );
}

#[test]
fn test_check_sat_with_details_has_verification_level() {
    use crate::api::types::VerificationLevel;

    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    let expected = VerificationLevel::from_state(false);
    assert_eq!(details.verification_level, expected);
}

#[test]
fn test_check_sat_with_details_proofs_enabled_verification_level() {
    use crate::api::types::VerificationLevel;

    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Unsat);
    let expected = VerificationLevel::from_state(true);
    assert_eq!(details.verification_level, expected);
    assert!(details.verification_level.has_proof_checking());
}

/// Verify that set_random_seed is callable and the solver still produces
/// correct results (#6961).
#[test]
fn test_set_random_seed_api() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_random_seed(42);

    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
}

/// Verify that different seeds don't break UNSAT results (#6961).
#[test]
fn test_set_random_seed_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_random_seed(12345);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unsat);
}

/// Regression (#6740): `try_reset()` must zero `scope_level` so
/// `num_scopes()` reports `0` after a full solver reset.
#[test]
fn test_try_reset_resets_scope_depth_6740() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.try_push().unwrap();
    solver.try_push().unwrap();
    assert_eq!(solver.num_scopes(), 2);

    solver.try_reset().unwrap();
    assert_eq!(solver.num_scopes(), 0);

    // Push after reset must count from zero, not from the stale value.
    solver.try_push().unwrap();
    assert_eq!(solver.num_scopes(), 1);
}
