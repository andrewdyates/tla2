// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::validation::{ValidationObservation, ValidationTarget};
use super::*;
use z4_core::{Symbol, VerificationBoundary, VerificationEvidenceKind, VerificationVerdict};

// ==========================================================================
// #5777: Typed verification contract regression tests
// ==========================================================================
//
// These tests prove the SAT/SMT model-validation contract is typed, not
// string-driven. They pattern-match on `ModelValidationError` variants and
// inspect `VerificationBoundary` values — if the contract reverted to strings,
// these tests would fail to compile.

/// Regression (#5777): an assertion that evaluates to `Unknown` with no model
/// must produce `ModelValidationError::Incomplete` with boundary
/// `SmtGroundAssertion`, not a stringly-typed error.
#[test]
fn test_typed_contract_incomplete_has_boundary_5777() {
    let mut executor = Executor::new();
    // UF predicate with no model → evaluator returns Unknown → Incomplete.
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let p_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    executor.ctx.assertions.push(p_x);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("UF predicate without model must fail validation");

    // Typed match — if the contract were string-based, this wouldn't compile.
    let failure = match err {
        ModelValidationError::Incomplete(ref f) => f,
        ModelValidationError::Violated(_) => {
            panic!("Expected Incomplete, got Violated: {err}");
        }
    };
    assert_eq!(
        failure.boundary,
        VerificationBoundary::SmtGroundAssertion,
        "Incomplete error must carry SmtGroundAssertion boundary"
    );
    assert!(
        !failure.detail.is_empty(),
        "Failure detail must be non-empty"
    );
}

/// Regression (#5777): a definitively false assertion must produce
/// `ModelValidationError::Violated` with boundary `SmtGroundAssertion`.
#[test]
fn test_typed_contract_violated_has_boundary_5777() {
    let mut executor = Executor::new();
    // `(assert false)` → evaluator returns Bool(false) → Violated.
    let false_term = executor.ctx.terms.mk_bool(false);
    executor.ctx.assertions.push(false_term);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("False assertion must fail validation");

    // Typed match — compile-time proof that the contract is enum-based.
    let failure = match err {
        ModelValidationError::Violated(ref f) => f,
        ModelValidationError::Incomplete(_) => {
            panic!("Expected Violated, got Incomplete: {err}");
        }
    };
    assert_eq!(
        failure.boundary,
        VerificationBoundary::SmtGroundAssertion,
        "Violated error must carry SmtGroundAssertion boundary"
    );
    assert!(
        failure.detail.contains("violated"),
        "Violated detail must mention 'violated', got: {}",
        failure.detail
    );
}

/// Regression (#5777): `finalize_sat_model_validation` routes `Incomplete` to
/// `SolveResult::Unknown` and `Violated` to `ExecutorError` — using typed
/// matching, not substring checks.
#[test]
fn test_typed_contract_finalize_routes_correctly_5777() {
    // Part 1: Incomplete → Unknown
    let mut exec_incomplete = Executor::new();
    let x = exec_incomplete.ctx.terms.mk_var("x", Sort::Int);
    let p_x = exec_incomplete
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    exec_incomplete.ctx.assertions.push(p_x);
    exec_incomplete.last_result = Some(SolveResult::Sat);
    exec_incomplete.last_model = Some(empty_model());

    let result = exec_incomplete
        .finalize_sat_model_validation()
        .expect("Incomplete should degrade to Ok(Unknown), not Err");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "Incomplete must route to Unknown"
    );
    assert_eq!(
        exec_incomplete.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );

    // Part 2: Violated → Err(ExecutorError::ModelValidation(_))
    let mut exec_violated = Executor::new();
    let false_term = exec_violated.ctx.terms.mk_bool(false);
    exec_violated.ctx.assertions.push(false_term);
    exec_violated.last_result = Some(SolveResult::Sat);
    exec_violated.last_model = Some(empty_model());

    let err = exec_violated
        .finalize_sat_model_validation()
        .expect_err("Violated must surface as Err");
    match err {
        ExecutorError::ModelValidation(ModelValidationError::Violated(_)) => {}
        other => panic!("Expected ModelValidation(Violated), got: {other}"),
    }
}

/// Regression (#5777): the assumption-validation path uses the same typed
/// `Incomplete` contract, with `SmtAssumption` boundary information.
#[test]
fn test_typed_contract_assumption_incomplete_has_boundary_5777() {
    let mut executor = Executor::new();
    let hello = executor.ctx.terms.mk_string("hello".to_string());
    let uf_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("my_uf_predicate"), vec![hello], Sort::Bool);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_sat_assumptions(&[uf_app])
        .expect_err("UF assumption without model must fail validation");

    let failure = match err {
        ModelValidationError::Incomplete(ref f) => f,
        ModelValidationError::Violated(_) => {
            panic!("Expected Incomplete, got Violated: {err}");
        }
    };
    assert_eq!(
        failure.boundary,
        VerificationBoundary::SmtAssumption,
        "Incomplete assumption error must carry SmtAssumption boundary"
    );
    assert!(
        !failure.detail.is_empty(),
        "Assumption failure detail must be non-empty"
    );
}

/// Regression (#5777): definitively false assumptions must produce typed
/// `Violated` errors with `SmtAssumption` boundary metadata.
#[test]
fn test_typed_contract_assumption_violated_has_boundary_5777() {
    let mut executor = Executor::new();
    let false_term = executor.ctx.terms.mk_bool(false);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_sat_assumptions(&[false_term])
        .expect_err("False assumption must fail validation");

    let failure = match err {
        ModelValidationError::Violated(ref f) => f,
        ModelValidationError::Incomplete(_) => {
            panic!("Expected Violated, got Incomplete: {err}");
        }
    };
    assert_eq!(
        failure.boundary,
        VerificationBoundary::SmtAssumption,
        "Violated assumption error must carry SmtAssumption boundary"
    );
    assert!(
        failure.detail.contains("violated"),
        "Violated assumption detail must mention 'violated', got: {}",
        failure.detail
    );
}

/// Regression (#5777): `finalize_sat_assumption_validation` must preserve the
/// typed `Violated` contract instead of degrading it to `Unknown`.
#[test]
fn test_typed_contract_finalize_assumption_routes_violated_5777() {
    let mut executor = Executor::new();
    let false_term = executor.ctx.terms.mk_bool(false);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .finalize_sat_assumption_validation(&[false_term])
        .expect_err("Violated assumption must surface as Err");

    match err {
        ExecutorError::ModelValidation(ModelValidationError::Violated(ref failure)) => {
            assert_eq!(failure.boundary, VerificationBoundary::SmtAssumption);
        }
        other => panic!("Expected ModelValidation(Violated), got: {other}"),
    }
}

/// Regression (#6703 Category B): pure-Boolean assertions must be accepted
/// from the SAT assignment even when the evaluator cannot reconstruct the
/// intermediate Bool variable values from theory models.
#[test]
fn test_validate_model_accepts_pure_boolean_sat_assignment_without_bool_values() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let q = executor.ctx.terms.mk_var("q", Sort::Bool);
    let iff = executor.ctx.terms.mk_eq(p, q);
    executor.ctx.assertions.push(iff);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(iff, true)]));

    let stats = executor
        .validate_model()
        .expect("pure-Boolean SAT assignment must count as delegated evidence");

    assert_eq!(
        stats.checked, 1,
        "delegated pure-Boolean validation should count"
    );
    assert_eq!(
        stats.sat_fallback_count, 0,
        "this is verified, not fallback"
    );
}

/// Regression (#5970 split audit): assumption validation must preserve the
/// extracted helper's delegated-SAT path instead of reporting an assertion
/// boundary or incomplete failure.
#[test]
fn test_validate_term_observation_delegates_sat_assumption_without_model_values() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    let flags = executor.precompute_term_flags();
    let model = model_with_sat_assignments(&[(a, true)]);

    let observation = executor.validate_term_observation(
        &model,
        a,
        0,
        flags[a.index()],
        false,
        ValidationTarget::Assumption,
    );

    match observation {
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Verified { boundary, evidence },
            dt_only,
        } => {
            assert_eq!(boundary, VerificationBoundary::SmtTheoryDelegation);
            assert_eq!(evidence, VerificationEvidenceKind::DelegatedSolver);
            assert!(
                !dt_only,
                "delegated SAT assumption must not be tagged as DT-only"
            );
        }
        other => panic!("Expected delegated assumption verdict, got: {other:?}"),
    }
}

/// Regression (#5970 split audit): arithmetic assertions mixed with array
/// packets must use the dedicated `ArithArrayMix` skip category when direct
/// evaluation is Unknown.
#[test]
fn test_validate_term_observation_skips_arith_array_mix_for_unknown_arith_assertion() {
    let mut executor = Executor::new();
    // Use (< (f x) 0) with an uninterpreted function f so the evaluator
    // genuinely returns Unknown (plain (< x 0) evaluates to false via
    // zero-default for x).
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let lt_zero = executor.ctx.terms.mk_lt(f_x, zero);
    let flags = executor.precompute_term_flags();

    let observation = executor.validate_term_observation(
        &empty_model(),
        lt_zero,
        0,
        flags[lt_zero.index()],
        true,
        ValidationTarget::GroundAssertion,
    );

    assert_eq!(
        observation,
        ValidationObservation::Skip(validation::ValidationSkipKind::ArithArrayMix),
        "mixed arithmetic/array validation should preserve the dedicated skip category"
    );
}

/// Regression (#7654): when arithmetic evaluation is definitively false only
/// because the extracted LRA model is off, preserve the SAT-backed fallback
/// instead of escalating to a violated assertion.
#[test]
fn test_validate_term_observation_fallbacks_false_arith_assertion_7654() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Real);
    let zero = executor.ctx.terms.mk_rational(BigRational::zero());
    let eq_zero = executor.ctx.terms.mk_eq(x, zero);
    let flags = executor.precompute_term_flags();

    let mut model = model_with_sat_assignments(&[(eq_zero, true)]);
    model.lra_model = Some(LraModel {
        values: HashMap::from([(x, BigRational::one())]),
    });

    let observation = executor.validate_term_observation(
        &model,
        eq_zero,
        0,
        flags[eq_zero.index()],
        false,
        ValidationTarget::GroundAssertion,
    );

    match observation {
        ValidationObservation::Fallback(failure) => {
            assert_eq!(
                failure.boundary,
                VerificationBoundary::SmtCircularSatFallback
            );
            assert!(
                failure.detail.contains("arithmetic evaluation false"),
                "unexpected fallback detail: {}",
                failure.detail
            );
        }
        other => panic!("Expected arithmetic SAT fallback, got: {other:?}"),
    }
}

/// Regression (#7654 follow-up): the Bool(false) arithmetic fallback must stay
/// narrow enough that trivially false ground arithmetic formulas still report
/// hard validation violations.
#[test]
fn test_validate_term_observation_does_not_fallback_ground_false_arith_assertion_7654() {
    let mut executor = Executor::new();
    let one = executor
        .ctx
        .terms
        .mk_rational(BigRational::from(BigInt::from(1)));
    let zero = executor.ctx.terms.mk_rational(BigRational::zero());
    let lt_false = executor.ctx.terms.mk_lt(one, zero);
    let flags = executor.precompute_term_flags();

    let mut model = model_with_sat_assignments(&[(lt_false, true)]);
    model.lra_model = Some(LraModel {
        values: HashMap::new(),
    });

    let observation = executor.validate_term_observation(
        &model,
        lt_false,
        0,
        flags[lt_false.index()],
        false,
        ValidationTarget::GroundAssertion,
    );

    match observation {
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Violated(failure),
            ..
        } => {
            assert_eq!(failure.boundary, VerificationBoundary::SmtGroundAssertion);
            assert!(
                failure.detail.contains("evaluates to false"),
                "unexpected violation detail: {}",
                failure.detail
            );
        }
        other => panic!("Expected hard validation violation, got: {other:?}"),
    }
}

/// Regression (#5777): assertion and assumption validation must share the same
/// private leaf helper and differ only in the boundary they report.
#[test]
fn test_typed_contract_shared_leaf_helper_boundaries_5777() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let p_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let flags = executor.precompute_term_flags();
    let af = flags[p_x.index()];
    let model = empty_model();

    let assertion_observation = executor.validate_term_observation(
        &model,
        p_x,
        0,
        af,
        false,
        ValidationTarget::GroundAssertion,
    );
    let assumption_observation =
        executor.validate_term_observation(&model, p_x, 0, af, false, ValidationTarget::Assumption);

    match assertion_observation {
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Incomplete(ref failure),
            ..
        } => {
            assert_eq!(failure.boundary, VerificationBoundary::SmtGroundAssertion);
        }
        other => panic!("Expected assertion incomplete verdict, got: {other:?}"),
    }

    match assumption_observation {
        ValidationObservation::Verdict {
            verdict: VerificationVerdict::Incomplete(ref failure),
            ..
        } => {
            assert_eq!(failure.boundary, VerificationBoundary::SmtAssumption);
        }
        other => panic!("Expected assumption incomplete verdict, got: {other:?}"),
    }
}

/// Regression (#5777 audit): when SAT validation degrades to `Unknown`, the
/// partial validation stats must survive so `VerificationSummary` can explain
/// why validation failed instead of reporting zero evidence.
#[test]
fn test_typed_contract_finalize_preserves_incomplete_stats_5777() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::String);
    let b = executor.ctx.terms.mk_var("b", Sort::String);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(eq_ab, true)]));

    let result = executor
        .finalize_sat_model_validation()
        .expect("fallback-only validation should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    let stats = executor
        .last_validation_stats
        .as_ref()
        .expect("incomplete validation must preserve partial stats");
    assert_eq!(stats.total, 1);
    assert_eq!(stats.checked, 0);
    assert_eq!(stats.sat_fallback_count, 1);
}

/// Regression (#5777 audit): the consumer-facing provenance counters must
/// separate independent, delegated, and incomplete categories.
#[test]
fn test_verification_evidence_counts_preserve_independent_and_delegated_split_5777() {
    let stats = ValidationStats {
        checked: 5,
        delegated_checks: 2,
        skipped_internal: 1,
        skipped_quantifier: 2,
        skipped_datatype: 3,
        skipped_dtbv: 4,
        skipped_arith_array_mix: 5,
        sat_fallback_count: 6,
        total: 23,
    };

    let (independent, delegated, incomplete) = stats.verification_evidence_counts();
    assert_eq!(independent, 3);
    assert_eq!(delegated, 2);
    assert_eq!(incomplete, 21);
}

// ==========================================================================
// Pre-existing regressions
// ==========================================================================

#[test]
fn test_finalize_sat_assumption_validation_degrades_internal_assumption() {
    // Internal helper terms are not independently checkable assumptions.
    // Returning SAT here would accept a zero-evidence assumption packet.
    let mut executor = Executor::new();
    let list = Sort::Uninterpreted("List".to_string());
    let x = executor.ctx.terms.mk_var("x", list);
    let depth = executor
        .ctx
        .terms
        .mk_app(Symbol::named("__z4_dt_depth_List"), vec![x], Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let assumption = executor.ctx.terms.mk_eq(depth, zero);
    assert!(
        executor.contains_internal_symbol(assumption),
        "assumption must retain the internal helper symbol"
    );

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[assumption])
        .expect("internal assumption should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_model_validation_returns_unknown_for_unevaluable_seq_term() {
    // (#6273, #4057) The public SAT finalizer must degrade skipped_internal-only
    // Seq packets to Unknown, not leave the caller with a false SAT result.
    let mut executor = Executor::new();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));
    let s = executor.ctx.terms.mk_var("s", seq_sort);
    let seq_len = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let assertion = executor.ctx.terms.mk_eq(seq_len, five);
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_model_validation()
        .expect("unevaluable seq term should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}
