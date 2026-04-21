// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId};
/// Create a simple bounded increment problem:
/// x = 0 => Inv(x)
/// Inv(x) /\ x < 10 => Inv(x + 1)
/// Inv(x) /\ x > 10 => false
fn create_bounded_increment() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 10 => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_bounded_increment_flipped_guard() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ 10 > x => Inv(x + 1)  (flipped guard)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::int(10), ChcExpr::var(x.clone()))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_bounded_decrement_flipped_guard() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 10 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ 0 < x => Inv(x - 1)  (flipped guard)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::int(0), ChcExpr::var(x.clone()))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Create a simple multi-predicate bounded increment problem:
/// x = 0 => P(x)
/// P(x) /\ x < 10 => Q(x + 1)
/// Q(x) /\ x < 10 => P(x + 1)
/// Q(x) /\ x > 10 => false
fn create_multi_pred_bounded_increment_cycle() -> (ChcProblem, PredicateId, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) /\ x < 10 => Q(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Q(x) /\ x < 10 => P(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Q(x) /\ x > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    (problem, p, q)
}

#[test]
fn test_detect_bounded_increment() {
    let problem = create_bounded_increment();
    let synth = StructuralSynthesizer::new(&problem);
    let patterns = synth.detect_patterns();

    assert_eq!(patterns.len(), 1);
    let pattern = &patterns[0];
    assert_eq!(pattern.pattern, SynthesisPattern::BoundedIncrement);
    assert_eq!(pattern.stride, 1);
    assert_eq!(pattern.upper_bound, Some(9)); // x < 10 means raw upper is 9 (adjusted to 10 for invariant)
    assert_eq!(pattern.init_value, Some(0));
}

#[test]
fn test_detect_bounded_increment_flipped_guard() {
    let problem = create_bounded_increment_flipped_guard();
    let synth = StructuralSynthesizer::new(&problem);
    let patterns = synth.detect_patterns();

    assert_eq!(patterns.len(), 1);
    let pattern = &patterns[0];
    assert_eq!(pattern.pattern, SynthesisPattern::BoundedIncrement);
    assert_eq!(pattern.stride, 1);
    assert_eq!(pattern.upper_bound, Some(9)); // 10 > x means raw upper is 9
    assert_eq!(pattern.init_value, Some(0));
}

#[test]
fn test_synthesize_bounded_increment() {
    let problem = create_bounded_increment();
    let synth = StructuralSynthesizer::new(&problem);
    let result = synth.try_synthesize();

    let SynthesisResult::Success(inv) = result else {
        panic!("Expected synthesis success: {result:?}");
    };
    assert_eq!(inv.pattern, SynthesisPattern::BoundedIncrement);
    assert!(!inv.interpretations.is_empty());
}

#[test]
fn test_synthesize_bounded_increment_flipped_guard() {
    let problem = create_bounded_increment_flipped_guard();
    let synth = StructuralSynthesizer::new(&problem);
    let result = synth.try_synthesize();

    let SynthesisResult::Success(inv) = result else {
        panic!("Expected synthesis success: {result:?}");
    };
    assert_eq!(inv.pattern, SynthesisPattern::BoundedIncrement);
    assert!(!inv.interpretations.is_empty());
}

#[test]
fn test_synthesize_bounded_decrement_flipped_guard() {
    let problem = create_bounded_decrement_flipped_guard();
    let synth = StructuralSynthesizer::new(&problem);
    let result = synth.try_synthesize();

    let SynthesisResult::Success(inv) = result else {
        panic!("Expected synthesis success: {result:?}");
    };
    assert_eq!(inv.pattern, SynthesisPattern::BoundedDecrement);
    assert!(!inv.interpretations.is_empty());
}

#[test]
fn test_synthesize_multi_pred_bounded_increment_cycle() {
    let (problem, p, q) = create_multi_pred_bounded_increment_cycle();
    let synth = StructuralSynthesizer::new(&problem);
    let result = synth.try_synthesize();

    let SynthesisResult::Success(inv) = result else {
        panic!("Expected synthesis success: {result:?}");
    };
    assert_eq!(inv.pattern, SynthesisPattern::BoundedIncrement);
    assert!(inv.interpretations.contains_key(&p));
    assert!(inv.interpretations.contains_key(&q));
}

/// Test that non-Int predicates are rejected.
#[test]
fn test_non_int_predicate_rejected() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Bool, ChcSort::Int]);
    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    // b = true, x = 0 => Inv(b, x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::Bool(true)),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(b), ChcExpr::var(x)]),
    ));

    let synth = StructuralSynthesizer::new(&problem);
    let result = synth.try_synthesize();

    // Should return NoPattern because Bool args are not supported
    assert!(
        matches!(result, SynthesisResult::NoPattern),
        "Non-Int predicates should be rejected, got {result:?}"
    );
}
