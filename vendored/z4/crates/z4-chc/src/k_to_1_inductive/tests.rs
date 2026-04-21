// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcSort, ChcVar, PredicateId};

/// Build a simple transition system: x starts at 0, increments by 1.
/// Property: x >= 0.
fn simple_counter() -> TransitionSystem {
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let x_next = ChcVar::new("x_next".to_string(), ChcSort::Int);
    TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        // init: x = 0
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        // trans: x_next = x + 1
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::Int(1)),
        ),
        // query (bad state): x < 0
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0)),
    )
}

/// Build a counter where x increments by 2 each step.
/// Property: x >= 0.
fn two_step_counter() -> TransitionSystem {
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let x_next = ChcVar::new("x_next".to_string(), ChcSort::Int);
    TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        // init: x = 0
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        // trans: x_next = x + 2
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::Int(2)),
        ),
        // query (bad state): x < 0
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0)),
    )
}

/// Verify that an invariant is 1-inductive for the given transition system.
/// Returns None if valid, Some(reason) if a check fails.
fn verify_1_inductive(ts: &TransitionSystem, inv: &ChcExpr) -> Option<&'static str> {
    let mut ctx = SmtContext::new();

    // 1) init => inv
    let init_violation = ChcExpr::and_all([ts.init.clone(), ChcExpr::not(inv.clone())]);
    match ctx.check_sat(&init_violation) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
        _ => return Some("init => invariant"),
    }

    // 2) inv => ¬query
    ctx.reset();
    let query_violation = ChcExpr::and_all([inv.clone(), ts.query.clone()]);
    match ctx.check_sat(&query_violation) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
        _ => return Some("invariant => not query"),
    }

    // 3) inv(x0) ∧ T(x0,x1) => inv(x1)
    ctx.reset();
    let inv_t0 = ts.send_through_time(inv, 0);
    let inv_t1 = ts.send_through_time(inv, 1);
    let trans = ts.k_transition(1);
    let induct_violation = ChcExpr::and_all([inv_t0, trans, ChcExpr::not(inv_t1)]);
    match ctx.check_sat_with_timeout(&induct_violation, std::time::Duration::from_secs(5)) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => None,
        _ => Some("inductiveness"),
    }
}

/// Verify that an invariant is k-inductive (but not necessarily 1-inductive).
fn verify_k_inductive(ts: &TransitionSystem, inv: &ChcExpr, k: usize) -> Option<&'static str> {
    let mut ctx = SmtContext::new();

    // 1) init => inv (same for all k)
    let init_violation = ChcExpr::and_all([ts.init.clone(), ChcExpr::not(inv.clone())]);
    match ctx.check_sat(&init_violation) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
        _ => return Some("init => invariant"),
    }

    // 2) inv => ¬query
    ctx.reset();
    let query_violation = ChcExpr::and_all([inv.clone(), ts.query.clone()]);
    match ctx.check_sat(&query_violation) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
        _ => return Some("invariant => not query"),
    }

    // 3) k-inductive: inv(x0) ∧ ... ∧ inv(x_{k-1}) ∧ T^k => inv(x_k)
    ctx.reset();
    let mut conjuncts = Vec::new();
    for i in 0..k {
        conjuncts.push(ts.send_through_time(inv, i));
    }
    conjuncts.push(ts.k_transition(k));
    conjuncts.push(ChcExpr::not(ts.send_through_time(inv, k)));
    let k_violation = ChcExpr::and_all(conjuncts);
    match ctx.check_sat_with_timeout(&k_violation, std::time::Duration::from_secs(5)) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => None,
        _ => Some("k-inductiveness"),
    }
}

#[test]
fn k1_passthrough_returns_invariant_unchanged() {
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    let result = convert(&inv, 1, &ts);
    assert!(result.is_some(), "k=1 conversion should succeed");
    assert_eq!(
        result.unwrap(),
        inv,
        "k=1 should return invariant unchanged"
    );
}

#[test]
fn k0_passthrough_returns_invariant_unchanged() {
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    let result = convert(&inv, 0, &ts);
    assert!(result.is_some(), "k=0 conversion should succeed");
    assert_eq!(
        result.unwrap(),
        inv,
        "k=0 should return invariant unchanged"
    );
}

#[test]
fn build_formula_base_case_is_true() {
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    let f = build_formula(0, &inv, &ts);
    assert_eq!(f, ChcExpr::Bool(true));
}

#[test]
fn build_formula_n1_has_init_and_transition() {
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    let f = build_formula(1, &inv, &ts);
    // Should be: Init(x_1) ∨ (true ∧ Inv(x_0) ∧ Trans(x_0, x_1))
    // Verify it's satisfiable (Init side makes it sat with x_1 = 0)
    let mut ctx = SmtContext::new();
    match ctx.check_sat(&f) {
        SmtResult::Sat(_) => {} // expected
        other => panic!("build_formula(1) should be satisfiable, got {other:?}"),
    }
}

#[test]
fn simple_counter_invariant_is_1_inductive() {
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    // x >= 0 should be 1-inductive for x=0, x'=x+1
    assert_eq!(verify_1_inductive(&ts, &inv), None);
}

#[test]
fn convert_k2_invariant_produces_1_inductive_result() {
    // x >= 0 is already 1-inductive, but we pass k=2 to exercise the
    // conversion code path. With disjunction case-splitting (#2753),
    // the interpolation engine can now handle the Init ∨ (Inv ∧ Trans)
    // formulas produced by build_formula.
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    assert_eq!(verify_k_inductive(&ts, &inv, 2), None);

    let result = convert(&inv, 2, &ts);
    let converted = result.expect("k=2 conversion should succeed with disjunction splitting");
    assert_eq!(
        verify_1_inductive(&ts, &converted),
        None,
        "Converted invariant must be 1-inductive"
    );
}

#[test]
fn convert_timeout_returns_none() {
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    let result = convert_with_timeout(&inv, 2, &ts, std::time::Duration::ZERO);
    assert!(
        result.is_none(),
        "zero timeout should force graceful conversion fallback"
    );
}

#[test]
fn convert_k3_invariant_produces_1_inductive_result() {
    // With disjunction case-splitting (#2753), k=3 conversion now works.
    let ts = two_step_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    assert_eq!(verify_k_inductive(&ts, &inv, 3), None);

    let result = convert(&inv, 3, &ts);
    let converted = result.expect("k=3 conversion should succeed with disjunction splitting");
    assert_eq!(
        verify_1_inductive(&ts, &converted),
        None,
        "Converted invariant must be 1-inductive"
    );
}

#[test]
fn halving_and_chained_both_produce_1_inductive_results() {
    // Both strategies now work with disjunction case-splitting (#2753).
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
    let halving_result = unfold_halving(&inv, 2, &ts, deadline);
    let chained_result = unfold_single_query_chained(&inv, 2, &ts, deadline);

    let h = halving_result.expect("halving should succeed with disjunction splitting");
    assert_eq!(
        verify_1_inductive(&ts, &h),
        None,
        "Halving result must be 1-inductive"
    );

    let c = chained_result.expect("chained should succeed with disjunction splitting");
    assert_eq!(
        verify_1_inductive(&ts, &c),
        None,
        "Chained result must be 1-inductive"
    );
}

#[test]
fn halving_k4_multi_round() {
    // k=4 halving: 2 rounds of interpolation. Round 1 succeeds with
    // disjunction splitting, but round 2 uses the strengthened invariant
    // from round 1, producing more complex formulas that may exceed
    // the current interpolation engine's capabilities.
    let ts = simple_counter();
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let inv = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));

    assert_eq!(verify_k_inductive(&ts, &inv, 4), None);

    // convert() tries halving first, then chained fallback
    let result = convert(&inv, 4, &ts);
    if let Some(ref strengthened) = result {
        assert_eq!(
            verify_1_inductive(&ts, strengthened),
            None,
            "k=4 converted result must be 1-inductive"
        );
    }
}
