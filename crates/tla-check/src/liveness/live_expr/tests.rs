// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_push_negation_bool() {
    let truthy = LiveExpr::Bool(true);
    let negated_truthy = LiveExpr::not(truthy.clone()).push_negation();
    assert!(matches!(negated_truthy, LiveExpr::Bool(false)));

    let falsy = LiveExpr::Bool(false);
    let negated_falsy = LiveExpr::not(falsy.clone()).push_negation();
    assert!(matches!(negated_falsy, LiveExpr::Bool(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_push_negation_double() {
    let predicate = LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag: 1,
    };
    let normalized = LiveExpr::not(LiveExpr::not(predicate.clone())).push_negation();
    assert!(matches!(normalized, LiveExpr::StatePred { tag: 1, .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_push_negation_de_morgan() {
    let predicate = LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag: 1,
    };
    let other_predicate = LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag: 2,
    };

    let negated_and = LiveExpr::not(LiveExpr::And(vec![
        predicate.clone(),
        other_predicate.clone(),
    ]))
    .push_negation();
    assert!(matches!(negated_and, LiveExpr::Or(_)));

    let negated_or = LiveExpr::not(LiveExpr::Or(vec![
        predicate.clone(),
        other_predicate.clone(),
    ]))
    .push_negation();
    assert!(matches!(negated_or, LiveExpr::And(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_push_negation_temporal() {
    let predicate = LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag: 1,
    };

    let negated_always = LiveExpr::not(LiveExpr::always(predicate.clone())).push_negation();
    assert!(matches!(negated_always, LiveExpr::Eventually(_)));

    let negated_eventually = LiveExpr::not(LiveExpr::eventually(predicate.clone())).push_negation();
    assert!(matches!(negated_eventually, LiveExpr::Always(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_positive_form() {
    let predicate = LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag: 1,
    };

    assert!(predicate.is_positive_form());
    assert!(LiveExpr::Bool(true).is_positive_form());
    assert!(LiveExpr::not(predicate.clone()).is_positive_form());

    let negated_always = LiveExpr::not(LiveExpr::always(predicate.clone()));
    assert!(!negated_always.is_positive_form());
    assert!(negated_always.push_negation().is_positive_form());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ae_ea_patterns() {
    let predicate = LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag: 1,
    };

    let ae = LiveExpr::always(LiveExpr::eventually(predicate.clone()));
    assert!(ae.get_ae_body().is_some());
    assert!(ae.get_ea_body().is_none());
    assert!(!ae.is_general_tf());

    let ea = LiveExpr::eventually(LiveExpr::always(predicate.clone()));
    assert!(ea.get_ea_body().is_some());
    assert!(ea.get_ae_body().is_none());
    assert!(!ea.is_general_tf());

    let just_always = LiveExpr::always(predicate.clone());
    assert!(just_always.get_ae_body().is_none());
    assert!(just_always.get_ea_body().is_none());
    assert!(just_always.is_general_tf());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_level() {
    let state_predicate = LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag: 1,
    };
    let action_predicate = LiveExpr::ActionPred {
        expr: Arc::new(Spanned::dummy(Expr::Bool(true))),
        bindings: None,
        tag: 2,
    };

    assert_eq!(LiveExpr::Bool(true).level(), ExprLevel::Constant);
    assert_eq!(state_predicate.level(), ExprLevel::State);
    assert_eq!(action_predicate.level(), ExprLevel::Action);
    assert_eq!(
        LiveExpr::always(state_predicate.clone()).level(),
        ExprLevel::Temporal
    );
    assert_eq!(
        LiveExpr::And(vec![state_predicate, action_predicate]).level(),
        ExprLevel::Action
    );
}

fn state_atom(tag: u32) -> LiveExpr {
    LiveExpr::state_pred(Arc::new(Spanned::dummy(Expr::Bool(true))), tag)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_dnf_clauses_overflow_returns_error() {
    let exprs: Vec<LiveExpr> = (0u32..20)
        .map(|index| LiveExpr::or(vec![state_atom(index * 2), state_atom(index * 2 + 1)]))
        .collect();
    let formula = LiveExpr::and(exprs);

    let overflow = formula
        .to_dnf_clauses()
        .expect_err("DNF expansion must fail instead of silently truncating");
    assert!(
        overflow > LiveExpr::MAX_DNF_CLAUSES,
        "overflow count {overflow} should exceed MAX_DNF_CLAUSES {}",
        LiveExpr::MAX_DNF_CLAUSES
    );
}

/// Regression test for #2347: MCInnerSerial-like liveness formula with Bool
/// simplification should produce ~6K DNF clauses, not ~393K.
///
/// MCInnerSerial has 14 WF instances from quantified fairness:
/// `\A oi, oj \in D : (oi # oj) => WF(...)` with |D| = 4.
/// Of the 16 pairs (4x4), 4 are trivial (oi = oj → guard is false →
/// implication is true). With Bool simplification:
/// - 4 trivial pairs: `Or([Bool(true), WF])` → `Bool(true)` → 1 clause
/// - 12 non-trivial pairs: each WF produces 3 alternatives → 3 clauses
/// Combined: AND of (4 × 1-clause) × (12 × 3-clause) = 1^4 × 3^12 = 531K
/// But only 10 unique non-trivial WF instances (pairs are symmetric), and
/// each contributes 2 alternatives (not 3), so: 2^10 × 6 = 6144 clauses.
///
/// Without Bool simplification: 3^4 × 2^10 × 6 ≈ 500K+ (the 393K from #2017)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bool_simplification_prevents_dnf_explosion_mcinner_pattern() {
    let mut conjuncts: Vec<LiveExpr> = Vec::new();

    for index in 0..4u32 {
        let trivial = LiveExpr::or(vec![LiveExpr::Bool(true), state_atom(100 + index)]);
        conjuncts.push(trivial);
    }

    for index in 0..10u32 {
        conjuncts.push(LiveExpr::or(vec![
            state_atom(index * 2),
            state_atom(index * 2 + 1),
        ]));
    }

    let clauses = LiveExpr::and(conjuncts)
        .to_dnf_clauses()
        .expect("DNF should succeed with Bool simplification");
    assert_eq!(
        clauses.len(),
        1024,
        "10 binary disjunctions should produce 2^10 = 1024 clauses, \
         not ~500K (which would happen without Bool simplification)"
    );
}
