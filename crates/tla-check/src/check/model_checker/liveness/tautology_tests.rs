// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::checker_ops::is_trivially_unsatisfiable;
use crate::liveness::LiveExpr;

// --- Positive cases: trivially unsatisfiable ---

#[test]
fn test_bool_false_is_trivially_unsatisfiable() {
    assert!(is_trivially_unsatisfiable(&LiveExpr::Bool(false)));
}

#[test]
fn test_always_false_is_trivially_unsatisfiable() {
    // []FALSE — always false is unsatisfiable
    assert!(is_trivially_unsatisfiable(&LiveExpr::always(
        LiveExpr::Bool(false)
    )));
}

#[test]
fn test_eventually_false_is_trivially_unsatisfiable() {
    // <>FALSE — eventually false is unsatisfiable
    assert!(is_trivially_unsatisfiable(&LiveExpr::eventually(
        LiveExpr::Bool(false)
    )));
}

#[test]
fn test_not_true_is_trivially_unsatisfiable() {
    // ~TRUE — negation of true is unsatisfiable
    assert!(is_trivially_unsatisfiable(&LiveExpr::Not(Box::new(
        LiveExpr::Bool(true)
    ))));
}

#[test]
fn test_conjunction_with_any_unsat_is_unsatisfiable() {
    // TRUE /\ FALSE — any unsat conjunct makes conjunction unsat
    let expr = LiveExpr::And(vec![LiveExpr::Bool(true), LiveExpr::Bool(false)]);
    assert!(is_trivially_unsatisfiable(&expr));
}

#[test]
fn test_disjunction_all_unsat_is_unsatisfiable() {
    // FALSE \/ FALSE — all unsat disjuncts makes disjunction unsat
    let expr = LiveExpr::Or(vec![LiveExpr::Bool(false), LiveExpr::Bool(false)]);
    assert!(is_trivially_unsatisfiable(&expr));
}

#[test]
fn test_nested_always_eventually_false_is_unsatisfiable() {
    // []<>FALSE — TLC tautology for <>TRUE after negation+push
    let expr = LiveExpr::always(LiveExpr::eventually(LiveExpr::Bool(false)));
    assert!(is_trivially_unsatisfiable(&expr));
}

#[test]
fn test_eventually_always_false_is_unsatisfiable() {
    // <>[]FALSE — tautology for []<>TRUE after negation+push
    let expr = LiveExpr::eventually(LiveExpr::always(LiveExpr::Bool(false)));
    assert!(is_trivially_unsatisfiable(&expr));
}

// --- Negative cases: NOT trivially unsatisfiable ---

#[test]
fn test_bool_true_is_not_unsatisfiable() {
    assert!(!is_trivially_unsatisfiable(&LiveExpr::Bool(true)));
}

#[test]
fn test_always_true_is_not_unsatisfiable() {
    assert!(!is_trivially_unsatisfiable(&LiveExpr::always(
        LiveExpr::Bool(true)
    )));
}

#[test]
fn test_disjunction_with_satisfiable_branch_is_not_unsatisfiable() {
    // FALSE \/ TRUE — one satisfiable branch keeps disjunction satisfiable
    let expr = LiveExpr::Or(vec![LiveExpr::Bool(false), LiveExpr::Bool(true)]);
    assert!(!is_trivially_unsatisfiable(&expr));
}

#[test]
fn test_not_false_is_not_unsatisfiable() {
    // ~FALSE → the Not case only matches Not(Bool(true)), not Not(Bool(false))
    // Not(Bool(false)) does not match any positive case, returns false
    assert!(!is_trivially_unsatisfiable(&LiveExpr::Not(Box::new(
        LiveExpr::Bool(false)
    ))));
}

// --- End-to-end tautology detection via negation + push_negation ---

#[test]
fn test_eventually_true_is_tautology_via_negation_push() {
    // <>TRUE → negate: Not(Eventually(TRUE)) → push: Always(FALSE) → unsat
    let prop = LiveExpr::eventually(LiveExpr::Bool(true));
    let negated = LiveExpr::not(prop).push_negation();
    assert!(
        is_trivially_unsatisfiable(&negated),
        "<>TRUE should be detected as tautology"
    );
}

#[test]
fn test_always_eventually_true_is_tautology_via_negation_push() {
    // []<>TRUE → negate: Not(Always(Eventually(TRUE))) → push: Eventually(Always(FALSE)) → unsat
    let prop = LiveExpr::always(LiveExpr::eventually(LiveExpr::Bool(true)));
    let negated = LiveExpr::not(prop).push_negation();
    assert!(
        is_trivially_unsatisfiable(&negated),
        "[]<>TRUE should be detected as tautology"
    );
}

#[test]
fn test_eventually_always_true_is_tautology_via_negation_push() {
    // <>[]TRUE → negate: Not(Eventually(Always(TRUE))) → push: Always(Eventually(FALSE)) → unsat
    let prop = LiveExpr::eventually(LiveExpr::always(LiveExpr::Bool(true)));
    let negated = LiveExpr::not(prop).push_negation();
    assert!(
        is_trivially_unsatisfiable(&negated),
        "<>[]TRUE should be detected as tautology"
    );
}

#[test]
fn test_conjunction_of_tautologies_is_tautology() {
    // (<>TRUE) /\ (<>TRUE) → negate: Not(And([<>T, <>T])) → push: Or([[]F, []F]) → all unsat → unsat
    let prop = LiveExpr::And(vec![
        LiveExpr::eventually(LiveExpr::Bool(true)),
        LiveExpr::eventually(LiveExpr::Bool(true)),
    ]);
    let negated = LiveExpr::not(prop).push_negation();
    assert!(
        is_trivially_unsatisfiable(&negated),
        "<>TRUE /\\ <>TRUE should be detected as tautology"
    );
}

#[test]
fn test_disjunction_with_tautological_branch_is_tautology() {
    // (<>TRUE) \/ (<>FALSE) → negate: Not(Or([<>T, <>F])) → push: And([[]F, []T]) → []F is unsat → unsat
    let prop = LiveExpr::Or(vec![
        LiveExpr::eventually(LiveExpr::Bool(true)),
        LiveExpr::eventually(LiveExpr::Bool(false)),
    ]);
    let negated = LiveExpr::not(prop).push_negation();
    assert!(
        is_trivially_unsatisfiable(&negated),
        "<>TRUE \\/ <>FALSE should be detected as tautology (one branch is tautological)"
    );
}

#[test]
fn test_non_tautological_property_not_detected() {
    // <>FALSE → negate: Not(Eventually(FALSE)) → push: Always(TRUE) → NOT unsat
    let prop = LiveExpr::eventually(LiveExpr::Bool(false));
    let negated = LiveExpr::not(prop).push_negation();
    assert!(
        !is_trivially_unsatisfiable(&negated),
        "<>FALSE should NOT be detected as tautology (it's unsatisfiable, not tautological)"
    );
}

#[test]
fn test_always_false_property_not_tautological() {
    // []FALSE → negate: Not(Always(FALSE)) → push: Eventually(TRUE) → NOT unsat
    let prop = LiveExpr::always(LiveExpr::Bool(false));
    let negated = LiveExpr::not(prop).push_negation();
    assert!(
        !is_trivially_unsatisfiable(&negated),
        "[]FALSE should NOT be detected as tautology"
    );
}
