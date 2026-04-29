// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! extract_nested_ae, nested_ae_extraction, bare_eventually rejection
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::helpers::{action_pred_xprime_eq_x, state_pred_x_eq};
use super::*;
use crate::liveness::LiveExpr;

/// Regression test for #1515: bare <>Action must be rejected, not misclassified
/// as <>[]Action (EA). TLC rejects temporal formulas with actions unless they
/// are in <>[]A or []<>A form.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bare_eventually_action_rejected_from_formula_grouped() {
    let a = action_pred_xprime_eq_x(900);
    // Bare <>Action — not wrapped in <>[]A
    let formula = LiveExpr::eventually(a);
    let result = LivenessChecker::from_formula_grouped(&formula);
    assert!(
        result.is_err(),
        "bare <>Action should be rejected, not misclassified as ea_action"
    );
    let err = result.unwrap_err();
    let err_msg = err.to_string();
    assert!(
        err_msg.contains("must be of the form <>[]A or []<>A"),
        "error should reference the valid forms, got: {}",
        err_msg
    );
}

/// Same as above but for the non-grouped from_formula path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bare_eventually_action_rejected_from_formula() {
    use crate::eval::EvalCtx;
    let a = action_pred_xprime_eq_x(901);
    let formula = LiveExpr::eventually(a);
    let ctx = EvalCtx::new();
    match LivenessChecker::from_formula(&formula, ctx) {
        Ok(_) => panic!("bare <>Action should be rejected, not misclassified as ea_action"),
        Err(err) => {
            let err_msg = err.to_string();
            assert!(
                err_msg.contains("must be of the form <>[]A or []<>A"),
                "error should reference the valid forms, got: {}",
                err_msg
            );
        }
    }
}

/// Verify that <>[]Action (proper EA form) still works correctly after the #1515 fix.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_proper_ea_action_still_classified_correctly() {
    let a = action_pred_xprime_eq_x(902);
    // <>[]A — proper EA form, should be accepted
    let formula = LiveExpr::eventually(LiveExpr::always(a));
    let plans = LivenessChecker::from_formula_grouped(&formula).unwrap();
    assert_eq!(plans.len(), 1);
    assert_eq!(
        plans[0].pems[0].ea_action_idx.len(),
        1,
        "<>[]Action should be classified as ea_action"
    );
}

/// Regression test for #1698: extract_nested_ae must NOT return temporal-level
/// bodies. This verifies the boundary condition at live_expr.rs line 484 where
/// temporal-level []<> bodies are skipped during extraction.
///
/// Formula: <>(P /\ []<>([]Q)) — the nested []<> wraps a temporal body ([]Q).
/// extract_nested_ae should NOT extract []Q as an AE constraint because it has
/// temporal level. Instead, the full term should pass through to the tableau.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_nested_ae_skips_temporal_level_bodies() {
    let p = state_pred_x_eq(1, 950);
    let q = state_pred_x_eq(2, 951);
    // []Q is temporal level
    let always_q = LiveExpr::always(q);
    // []<>([]Q) — the AE pattern wraps a temporal body
    let ae_temporal = LiveExpr::always(LiveExpr::eventually(always_q));
    // <>(P /\ []<>([]Q)) — outer formula with nested AE of temporal body
    let formula = LiveExpr::eventually(LiveExpr::and(vec![p.clone(), ae_temporal]));

    // extract_nested_ae should NOT extract []Q (temporal level)
    let (ae_bodies, _simplified) = formula.extract_nested_ae();
    for body in &ae_bodies {
        assert_ne!(
            body.level(),
            crate::liveness::live_expr::ExprLevel::Temporal,
            "extract_nested_ae must not return temporal-level bodies, got: {:?}",
            body
        );
    }
}

/// Regression test for #1698: from_formula correctly handles formulas where
/// extract_nested_ae extracts state/action-level bodies from nested AE patterns.
/// Verifies no constraints are silently dropped.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_ae_extraction_preserves_state_constraints() {
    use crate::eval::EvalCtx;
    let p = state_pred_x_eq(1, 960);
    let q = state_pred_x_eq(2, 961);
    // []<>Q — nested AE with state-level body
    let ae_q = LiveExpr::always(LiveExpr::eventually(q.clone()));
    // <>(P /\ []<>Q) — extract_nested_ae should extract Q as ae_state
    let formula = LiveExpr::eventually(LiveExpr::and(vec![p.clone(), ae_q]));

    let ctx = EvalCtx::new();
    let checkers = LivenessChecker::from_formula(&formula, ctx)
        .expect("invariant: <>(P /\\ []<>Q) should decompose without error");
    assert_eq!(
        checkers.len(),
        1,
        "single DNF clause should produce 1 checker"
    );
    // Q should have been extracted as an AE state constraint
    assert_eq!(
        checkers[0].constraints().ae_state.len(),
        1,
        "[]<>Q inside <>(P /\\ []<>Q) should extract Q as ae_state constraint"
    );
    assert!(
        checkers[0].constraints().ae_state[0].structurally_equal(&q),
        "extracted ae_state constraint should be Q (tag 961)"
    );
}

/// Same test for the grouped path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_ae_extraction_preserves_state_constraints_grouped() {
    let p = state_pred_x_eq(1, 970);
    let q = state_pred_x_eq(2, 971);
    let ae_q = LiveExpr::always(LiveExpr::eventually(q.clone()));
    let formula = LiveExpr::eventually(LiveExpr::and(vec![p.clone(), ae_q]));

    let plans = LivenessChecker::from_formula_grouped(&formula)
        .expect("invariant: <>(P /\\ []<>Q) should decompose without error in grouped path");
    assert_eq!(plans.len(), 1, "single DNF clause should produce 1 group");
    // Q should appear in check_state and be referenced by ae_state_idx
    let pem = &plans[0].pems[0];
    assert_eq!(
        pem.ae_state_idx.len(),
        1,
        "[]<>Q inside <>(P /\\ []<>Q) should extract Q as ae_state in grouped plan"
    );
    let extracted = &plans[0].check_state[pem.ae_state_idx[0]];
    assert!(
        extracted.structurally_equal(&q),
        "extracted ae_state check should be Q (tag 971)"
    );
}

/// Regression test for #1517: extract_nested_ae must NOT recurse through Not.
///
/// Under negation, temporal operators dualize: ~[]<>P = <>[]~P (AE becomes EA).
/// If extract_nested_ae recurses into Not(Always(Eventually(P))), it would
/// incorrectly extract P as an AE body. The correct behavior is to leave
/// the Not subtree untouched.
///
/// Formula: Not(Always(Eventually(P))) — this is ~[]<>P = <>[]~P (an EA, not AE).
/// extract_nested_ae should NOT extract P.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_nested_ae_does_not_recurse_through_not() {
    let p = state_pred_x_eq(1, 980);
    // ~[]<>P — this is an EA pattern, NOT an AE pattern
    let neg_ae = LiveExpr::not(LiveExpr::always(LiveExpr::eventually(p.clone())));

    let (ae_bodies, simplified) = neg_ae.extract_nested_ae();

    // No AE bodies should be extracted from inside a negation
    assert!(
        ae_bodies.is_empty(),
        "extract_nested_ae must not extract bodies from inside Not; got {:?}",
        ae_bodies
    );
    // The formula should be returned unchanged
    assert!(
        simplified.structurally_equal(&neg_ae),
        "formula under Not should be returned unchanged"
    );
}

/// Regression test for #1517: extract_nested_ea must NOT recurse through Not.
///
/// Under negation, temporal operators dualize: ~<>[]P = []<>~P (EA becomes AE).
/// If extract_nested_ea recurses into Not(Eventually(Always(P))), it would
/// incorrectly extract P as an EA body.
///
/// Formula: Not(Eventually(Always(P))) — this is ~<>[]P = []<>~P (an AE, not EA).
/// extract_nested_ea should NOT extract P.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_nested_ea_does_not_recurse_through_not() {
    let p = state_pred_x_eq(1, 990);
    // ~<>[]P — this is an AE pattern, NOT an EA pattern
    let neg_ea = LiveExpr::not(LiveExpr::eventually(LiveExpr::always(p.clone())));

    let (ea_bodies, simplified) = neg_ea.extract_nested_ea();

    // No EA bodies should be extracted from inside a negation
    assert!(
        ea_bodies.is_empty(),
        "extract_nested_ea must not extract bodies from inside Not; got {:?}",
        ea_bodies
    );
    // The formula should be returned unchanged
    assert!(
        simplified.structurally_equal(&neg_ea),
        "formula under Not should be returned unchanged"
    );
}
