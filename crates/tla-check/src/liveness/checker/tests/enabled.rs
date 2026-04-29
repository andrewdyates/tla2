// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ENABLED evaluation, caching, fallback paths, error suppression
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::*;
use crate::eval::{BindingChain, BindingValue};
use crate::liveness::test_helpers::{
    constraints_to_grouped_plan, empty_successors, make_checker, make_checker_with_constraints,
    make_checker_with_vars, spanned,
};
use crate::liveness::LiveExpr;
use crate::Value;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tla_core::ast::{Expr, Substitution};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_in_state_consistency() {
    // Build a tableau whose initial node requires ENABLED(x' = x + 1).
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = spanned(Expr::Add(
        Box::new(x),
        Box::new(spanned(Expr::Int(1.into()))),
    ));
    let inc_expr = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x_plus_1))));

    let mut checker = make_checker(LiveExpr::enabled(inc_expr.clone(), 1));

    let s0 = State::from_pairs([("x", Value::int(0))]);

    // Self-loop where Inc is false => ENABLED Inc is false => inconsistent.
    let mut get_successors = |_s: &State| Ok(vec![s0.clone()]);
    let added = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert!(added.is_empty());

    // If there exists a successor satisfying Inc, ENABLED Inc becomes true.
    let mut checker = make_checker(LiveExpr::enabled(inc_expr, 1));
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let mut get_successors = |_s: &State| Ok(vec![s1.clone()]);
    let added = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert!(!added.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_cache_skips_empty_registry_fallback_mode() {
    // Regression test for #2017 follow-up audit:
    // In empty-registry fallback mode, ENABLED uses checker-local successor maps.
    // Reusing (fingerprint, tag) across checker instances must not leak cached results.
    crate::liveness::clear_enabled_cache();

    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = spanned(Expr::Add(
        Box::new(x.clone()),
        Box::new(spanned(Expr::Int(1.into()))),
    ));
    let x_plus_2 = spanned(Expr::Add(
        Box::new(x),
        Box::new(spanned(Expr::Int(2.into()))),
    ));

    let enabled_inc = LiveExpr::enabled(
        Arc::new(spanned(Expr::Eq(
            Box::new(x_prime.clone()),
            Box::new(x_plus_1),
        ))),
        1,
    );
    let enabled_inc_by_two = LiveExpr::enabled(
        Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x_plus_2)))),
        1,
    );

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s0_fp = s0.fingerprint();

    let mut checker_true = make_checker(LiveExpr::Bool(true));
    checker_true
        .state_successors
        .insert(s0_fp, Arc::new(vec![s1.clone()]));
    assert!(
        checker_true
            .eval_check_on_state(&enabled_inc, &s0)
            .expect("eval_check_on_state should not error for valid enabled check"),
        "x' = x + 1 should be ENABLED when successor x=1 exists"
    );

    let mut checker_false = make_checker(LiveExpr::Bool(true));
    checker_false
        .state_successors
        .insert(s0_fp, Arc::new(vec![s1]));
    assert!(
        !checker_false
            .eval_check_on_state(&enabled_inc_by_two, &s0)
            .expect("eval_check_on_state should not error for valid enabled check"),
        "x' = x + 2 should be disabled; stale cache from prior checker must not leak"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_fallback_applies_quantifier_bindings() {
    // Regression for #2122: The checker fallback (empty var_registry) path must apply
    // quantifier bindings via BindingChain. Without this, action expressions
    // that reference quantifier-bound variables (from WF/SF decomposition) would fail
    // with UndefinedVar.
    //
    // Scenario: ENABLED(q = x') where q is a quantifier-bound variable.
    // The action checks if x's successor equals the bound value q.
    // Without bindings applied, q is undefined → eval error.

    // Action: q = x' (quantifier-bound variable compared to primed state var)
    let action_expr = Arc::new(spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "q".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
    )));

    // Create BindingChain: q = 1
    // Part of #2895: Uses BindingChain instead of FastBinding.
    let name_id = tla_core::name_intern::intern_name("q");
    let binding = BindingChain::empty().cons(name_id, BindingValue::eager(Value::int(1)));

    let enabled = LiveExpr::enabled_with_bindings(
        action_expr,
        false, // no require_state_change — simplest path
        None,  // no subscript
        3000,  // unique tag
        Some(binding),
    );

    let current = State::from_pairs([("x", Value::int(0))]);
    let succ_match = State::from_pairs([("x", Value::int(1))]);
    let succ_no_match = State::from_pairs([("x", Value::int(2))]);

    // Case 1: Successor x=1 matches q=1 → ENABLED should be true
    let mut checker = make_checker(LiveExpr::Bool(true));
    checker
        .state_successors
        .insert(current.fingerprint(), Arc::new(vec![succ_match]));
    assert!(
        checker
            .eval_check_on_state(&enabled, &current)
            .expect("ENABLED with bindings should evaluate without UndefinedVar"),
        "ENABLED(q = x') should be true when successor x=1 matches bound q=1"
    );

    // Case 2: Successor x=2 does not match q=1 → ENABLED should be false
    crate::liveness::clear_enabled_cache();
    let mut checker2 = make_checker(LiveExpr::Bool(true));
    checker2
        .state_successors
        .insert(current.fingerprint(), Arc::new(vec![succ_no_match]));
    assert!(
        !checker2
            .eval_check_on_state(&enabled, &current)
            .expect("ENABLED with bindings should evaluate without UndefinedVar"),
        "ENABLED(q = x') should be false when successor x=2 != bound q=1"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_subscripted_fallback_respects_subscript() {
    let enabled = LiveExpr::enabled_with_bindings(
        Arc::new(spanned(Expr::Bool(true))),
        true,
        Some(Arc::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        2111,
        None,
    );

    let current = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);
    let succ_only_y = State::from_pairs([("x", Value::int(0)), ("y", Value::int(1))]);

    let mut checker = make_checker(LiveExpr::Bool(true));
    checker
        .state_successors
        .insert(current.fingerprint(), Arc::new(vec![succ_only_y]));

    assert!(
        !checker
            .eval_check_on_state(&enabled, &current)
            .expect("subscripted ENABLED fallback should evaluate"),
        "ENABLED<<A>>_x must ignore successors that only change non-subscript vars"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_uses_symmetry_witness_successors_for_state_change() {
    // Under symmetry, a reduced self-loop can still represent a concrete
    // non-stuttering transition. ENABLED<<TRUE>>_x must therefore inspect the
    // concrete witness successor, not just the reduced representative.
    let mut checker = make_checker_with_vars(LiveExpr::Bool(true), &["x", "y"]);
    let registry = checker.ctx.var_registry().clone();

    let current = State::from_pairs([("x", Value::int(0)), ("y", Value::int(1))]);
    let witness = State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]);
    let canon_fp = current.fingerprint();

    let mut fp_map = FxHashMap::default();
    fp_map.insert(current.fingerprint(), canon_fp);
    fp_map.insert(witness.fingerprint(), canon_fp);

    let mut succ_witnesses = crate::SuccessorWitnessMap::default();
    succ_witnesses.insert(
        canon_fp,
        vec![(
            canon_fp,
            crate::ArrayState::from_state_with_fp(&witness, &registry),
        )],
    );
    checker.set_successor_maps(Arc::new(fp_map), Some(Arc::new(succ_witnesses)));

    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));

    assert!(
        checker
            .eval_enabled(
                &checker.ctx.clone(),
                &current,
                &action,
                None,
                true,
                Some(&subscript),
            )
            .expect("symmetry witness ENABLED should evaluate"),
        "concrete symmetry witness changes x even though the reduced edge is a self-loop"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_cached_fast_path_re_evaluates_instance_substitution_per_successor() {
    // Regression for #2111:
    // ENABLED fast path iterates cached successors and must re-run INSTANCE substitutions
    // for each candidate transition. Otherwise SUBST_CACHE can pin the first successor's
    // value and incorrectly return false.
    let mut ctx = EvalCtx::new();
    ctx.register_var(Arc::from("x"));
    let ctx = ctx.with_instance_substitutions(vec![Substitution {
        from: spanned("inst_x".to_string()),
        to: spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))))),
    }]);

    let tableau = crate::liveness::Tableau::new(LiveExpr::always(LiveExpr::Bool(true)));
    let mut checker = LivenessChecker::new(tableau, ctx);

    let action = Arc::new(spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "inst_x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(1.into()))),
    )));
    let enabled = LiveExpr::enabled_with_bindings(
        action,
        true,
        Some(Arc::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        2111,
        None,
    );

    let current = State::from_pairs([("x", Value::int(-1))]);
    let succ_false = State::from_pairs([("x", Value::int(0))]);
    let succ_true = State::from_pairs([("x", Value::int(1))]);
    checker.state_successors.insert(
        current.fingerprint(),
        Arc::new(vec![succ_false.clone(), succ_true.clone()]),
    );

    assert!(
        checker
            .eval_check_on_state(&enabled, &current)
            .expect("ENABLED check should evaluate"),
        "second successor should satisfy action via fresh INSTANCE substitution"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_evaluation_in_checks() {
    // Weak fairness style check: []<>(~ENABLED Inc \/ Inc)
    // If Inc is not enabled, the disjunction holds even if Inc never occurs.
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = spanned(Expr::Add(
        Box::new(x),
        Box::new(spanned(Expr::Int(1.into()))),
    ));
    let inc_expr = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x_plus_1))));

    let not_enabled_inc = LiveExpr::not(LiveExpr::enabled(inc_expr.clone(), 1));
    let inc_occurs = LiveExpr::action_pred(inc_expr, 2);
    let wf_body = LiveExpr::or(vec![not_enabled_inc, inc_occurs]);

    let mut checker = make_checker_with_constraints(
        LiveExpr::always(LiveExpr::Bool(true)),
        LivenessConstraints {
            ae_action: vec![wf_body],
            ..Default::default()
        },
    );
    let mut get_successors = empty_successors;

    // One-state system with only a self-loop where Inc is false.
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    let _ = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .unwrap();

    let plan = constraints_to_grouped_plan(checker.constraints());
    let result = checker.check_liveness_grouped(&plan, 0);
    // Verify trace contents — not just the Violated variant.
    match &result {
        LivenessResult::Violated { cycle, .. } => {
            assert!(!cycle.is_empty(), "violation cycle must be non-empty");
            let cycle_has_s0 = cycle
                .iter()
                .any(|(s, _)| s.get("x") == Some(&Value::int(0)));
            assert!(
                cycle_has_s0,
                "cycle should contain s0 (x=0), got: {:?}",
                cycle.iter().map(|(s, _)| s.clone()).collect::<Vec<_>>()
            );
        }
        other => panic!(
            "expected Violated for WF check on self-loop, got {:?}",
            other
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_uses_successor_fingerprints_from_shared_cache() {
    crate::liveness::clear_enabled_cache();

    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = spanned(Expr::Add(
        Box::new(x),
        Box::new(spanned(Expr::Int(1.into()))),
    ));
    let enabled_inc = LiveExpr::enabled(
        Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x_plus_1)))),
        4011,
    );

    let current = State::from_pairs([("x", Value::int(0))]);
    let succ = State::from_pairs([("x", Value::int(1))]);
    let current_fp = current.fingerprint();
    let succ_fp = succ.fingerprint();

    let mut shared = rustc_hash::FxHashMap::default();
    shared.insert(current_fp, current.clone());
    shared.insert(succ_fp, succ);

    let mut checker = make_checker(LiveExpr::Bool(true));
    checker.set_behavior_graph_shared_cache(Arc::new(shared));
    checker
        .state_successor_fps
        .insert(current_fp, Arc::new(vec![succ_fp]));

    assert!(
        checker
            .eval_check_on_state(&enabled_inc, &current)
            .expect("ENABLED should resolve successor fingerprints through the shared cache"),
        "x' = x + 1 should be ENABLED when the successor is only cached by fingerprint"
    );
}
