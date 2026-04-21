// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ENABLED error suppression and state_change tests
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::*;
use crate::liveness::test_helpers::{
    empty_successors, make_checker, make_checker_with_vars, spanned,
};
use crate::liveness::LiveExpr;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::Expr;

/// This tests the error handling at lines 1620-1631.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_eval_error_disables_action() {
    use tla_core::ast::BoundVar;
    // Build an action that will cause NotInDomain error: f[99] where domain is {1,2,3}
    // When eval_enabled encounters this, it should return Ok(false), not propagate error.
    let domain = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(1.into())),
        spanned(Expr::Int(2.into())),
        spanned(Expr::Int(3.into())),
    ]));
    let f_def = spanned(Expr::FuncDef(
        vec![BoundVar {
            name: spanned("n".to_string()),
            domain: Some(Box::new(domain)),
            pattern: None,
        }],
        Box::new(spanned(Expr::Ident(
            "n".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    // Action: x' = f[99] (99 not in domain, will cause NotInDomain error)
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let f_app = spanned(Expr::FuncApply(
        Box::new(f_def),
        Box::new(spanned(Expr::Int(99.into()))),
    ));
    let action = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(f_app))));

    let tableau = Tableau::new(LiveExpr::enabled(action, 1));
    let mut ctx = EvalCtx::new();
    ctx.register_var(Arc::from("x"));
    let mut checker = LivenessChecker::new(tableau, ctx);
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    // This should NOT panic or return error - the NotInDomain error
    // should be caught and treated as action disabled (empty init nodes).
    let init_result = checker.add_initial_state(&s0, &mut get_successors, None);
    assert!(
        init_result.is_ok(),
        "NotInDomain should not propagate as fatal error"
    );
    // Since ENABLED can't be satisfied (action causes error), state is inconsistent with tableau
    assert!(
        init_result.unwrap().is_empty(),
        "Error during ENABLED eval should make state inconsistent"
    );
}

/// Test that DivisionByZero during ENABLED evaluation treats action as disabled.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_division_by_zero_disables_action() {
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    // Action: x' = 10 \div 0 (division by zero)
    let div_zero = spanned(Expr::Div(
        Box::new(spanned(Expr::Int(10.into()))),
        Box::new(spanned(Expr::Int(0.into()))),
    ));
    let action = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(div_zero))));

    let tableau = Tableau::new(LiveExpr::enabled(action, 1));
    let mut ctx = EvalCtx::new();
    ctx.register_var(Arc::from("x"));
    let mut checker = LivenessChecker::new(tableau, ctx);
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_result = checker.add_initial_state(&s0, &mut get_successors, None);
    assert!(
        init_result.is_ok(),
        "DivisionByZero should not propagate as fatal error"
    );
    // Action is disabled due to error, so state is inconsistent with ENABLED tableau
    assert!(init_result.unwrap().is_empty());
}

/// Test that NotInDomain during ENABLED evaluation treats action as disabled.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_index_out_of_bounds_disables_action() {
    // Build action: x' = seq[10] where seq has 3 elements
    let seq = spanned(Expr::Tuple(vec![
        spanned(Expr::Int(1.into())),
        spanned(Expr::Int(2.into())),
        spanned(Expr::Int(3.into())),
    ]));
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let seq_access = spanned(Expr::FuncApply(
        Box::new(seq),
        Box::new(spanned(Expr::Int(10.into()))), // out of bounds
    ));
    let action = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(seq_access))));

    let tableau = Tableau::new(LiveExpr::enabled(action, 1));
    let mut ctx = EvalCtx::new();
    ctx.register_var(Arc::from("x"));
    let mut checker = LivenessChecker::new(tableau, ctx);
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_result = checker.add_initial_state(&s0, &mut get_successors, None);
    assert!(
        init_result.is_ok(),
        "NotInDomain should not propagate as fatal error in ENABLED"
    );
    // Action is disabled due to error
    assert!(init_result.unwrap().is_empty());
}

/// Test that NoSuchField during ENABLED evaluation treats action as disabled.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_no_such_field_disables_action() {
    // Build action: x' = r.badfield where r = [a |-> 1]
    let record = spanned(Expr::Record(vec![(
        spanned("a".to_string()),
        spanned(Expr::Int(1.into())),
    )]));
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let field_access = spanned(Expr::RecordAccess(
        Box::new(record),
        spanned("badfield".to_string()).into(), // non-existent field
    ));
    let action = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(field_access))));

    let tableau = Tableau::new(LiveExpr::enabled(action, 1));
    let mut ctx = EvalCtx::new();
    ctx.register_var(Arc::from("x"));
    let mut checker = LivenessChecker::new(tableau, ctx);
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_result = checker.add_initial_state(&s0, &mut get_successors, None);
    assert!(
        init_result.is_ok(),
        "NoSuchField should not propagate as fatal error"
    );
    // Action is disabled due to error
    assert!(init_result.unwrap().is_empty());
}

/// Regression for #2151: disabled-action errors in the fallback path (empty VarRegistry)
/// must be suppressed just like the fast path. Before the fix, `eval_enabled_fallback`
/// propagated these errors via `?` as hard failures while `fast_path_satisfies_action`
/// correctly caught them.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_fallback_disabled_action_error_suppressed() {
    // Action: x' = 10 \div 0 (division by zero = disabled-action error)
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x)));
    let div_zero = spanned(Expr::Div(
        Box::new(spanned(Expr::Int(10.into()))),
        Box::new(spanned(Expr::Int(0.into()))),
    ));
    let action = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(div_zero))));

    let enabled = LiveExpr::enabled(action, 2151);

    let current = State::from_pairs([("x", Value::int(0))]);
    let successor = State::from_pairs([("x", Value::int(1))]);

    // make_checker uses EvalCtx::new() with empty VarRegistry,
    // so eval_enabled_uncached takes the fallback path.
    let mut checker = make_checker(LiveExpr::Bool(true));
    checker
        .state_successors
        .insert(current.fingerprint(), Arc::new(vec![successor]));

    // DivisionByZero during ENABLED eval in fallback path must be suppressed,
    // returning Ok(false), not propagating as a hard error.
    let result = checker.eval_check_on_state(&enabled, &current);
    assert!(
        result.is_ok(),
        "DivisionByZero in fallback path should not propagate: {:?}",
        result.err()
    );
    assert!(
        !result.unwrap(),
        "ENABLED with disabled action in fallback path should return false"
    );
}

/// Regression for #2151: NotInDomain errors in the fallback path must be suppressed.
/// Same as above but with a different disabled-action error type.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_fallback_not_in_domain_error_suppressed() {
    use tla_core::ast::BoundVar;
    // Action: x' = f[99] where f's domain is {1,2,3} → NotInDomain error
    let domain = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(1.into())),
        spanned(Expr::Int(2.into())),
        spanned(Expr::Int(3.into())),
    ]));
    let f_def = spanned(Expr::FuncDef(
        vec![BoundVar {
            name: spanned("n".to_string()),
            domain: Some(Box::new(domain)),
            pattern: None,
        }],
        Box::new(spanned(Expr::Ident(
            "n".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x)));
    let f_app = spanned(Expr::FuncApply(
        Box::new(f_def),
        Box::new(spanned(Expr::Int(99.into()))),
    ));
    let action = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(f_app))));

    let enabled = LiveExpr::enabled(action, 2152);

    let current = State::from_pairs([("x", Value::int(0))]);
    let successor = State::from_pairs([("x", Value::int(1))]);

    let mut checker = make_checker(LiveExpr::Bool(true));
    checker
        .state_successors
        .insert(current.fingerprint(), Arc::new(vec![successor]));

    let result = checker.eval_check_on_state(&enabled, &current);
    assert!(
        result.is_ok(),
        "NotInDomain in fallback path should not propagate: {:?}",
        result.err()
    );
    assert!(
        !result.unwrap(),
        "ENABLED with NotInDomain in fallback path should return false"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_require_state_change_false_fallback_path() {
    // Tests require_state_change=false in the FALLBACK path (#2572 gap).
    //
    // This exercises eval_enabled_fallback (empty var_registry) where ENABLED
    // checks cached successors via transition_satisfies_action. When
    // require_state_change=false, any successor satisfying the action suffices —
    // including a self-loop.
    //
    // NOTE: This does NOT test the primary path (with registered vars), which
    // calls enabled::eval_enabled_cp instead. See the _primary_path variant below.
    crate::liveness::clear_enabled_cache();

    // Action: x' = x (identity — always enabled, never changes state)
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let identity_action = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x))));

    let current = State::from_pairs([("x", Value::int(5))]);

    // Case 1: require_state_change=false — self-loop should satisfy ENABLED
    let enabled_no_change = LiveExpr::enabled_with_bindings(
        identity_action.clone(),
        false, // require_state_change=false: WF case, no state change needed
        None,
        2572,
        None,
    );

    let mut checker = make_checker(LiveExpr::Bool(true));
    checker.state_successors.insert(
        current.fingerprint(),
        Arc::new(vec![current.clone()]), // self-loop only
    );
    assert!(
        checker
            .eval_check_on_state(&enabled_no_change, &current)
            .expect("ENABLED with require_state_change=false should not error"),
        "ENABLED(x' = x) with require_state_change=false must be true: \
         the action is satisfiable (self-loop matches x' = x)"
    );

    // Case 2: require_state_change=true with subscript — self-loop should NOT satisfy
    crate::liveness::clear_enabled_cache();
    let enabled_with_change = LiveExpr::enabled_with_bindings(
        identity_action,
        true, // require_state_change=true: SF case, state change required
        Some(Arc::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        2573,
        None,
    );

    let mut checker2 = make_checker(LiveExpr::Bool(true));
    checker2.state_successors.insert(
        current.fingerprint(),
        Arc::new(vec![current.clone()]), // self-loop only
    );
    assert!(
        !checker2
            .eval_check_on_state(&enabled_with_change, &current)
            .expect("ENABLED with require_state_change=true should not error"),
        "ENABLED(x' = x) with require_state_change=true must be false: \
         self-loop does not change subscript variable x"
    );

    // Case 3: require_state_change=false with UNSATISFIABLE action — should be false.
    // Guards against a fallback bug that returns true for all require_state_change=false.
    crate::liveness::clear_enabled_cache();
    let x3 = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x3_prime = spanned(Expr::Prime(Box::new(x3.clone())));
    // Action: x' = x + 1 (cannot be satisfied by a self-loop x→x)
    let increment_action = Arc::new(spanned(Expr::Eq(
        Box::new(x3_prime),
        Box::new(spanned(Expr::Add(
            Box::new(x3),
            Box::new(spanned(Expr::Int(1.into()))),
        ))),
    )));
    let enabled_unsatisfiable = LiveExpr::enabled_with_bindings(
        increment_action,
        false, // require_state_change=false, but action itself is unsatisfiable
        None,
        2575,
        None,
    );
    let mut checker3 = make_checker(LiveExpr::Bool(true));
    checker3.state_successors.insert(
        current.fingerprint(),
        Arc::new(vec![current.clone()]), // self-loop only — x'=x+1 is not satisfiable
    );
    assert!(
        !checker3
            .eval_check_on_state(&enabled_unsatisfiable, &current)
            .expect("ENABLED with unsatisfiable action should not error"),
        "ENABLED(x' = x + 1) with only self-loop successor must be false: \
         the action x'=x+1 cannot be satisfied by x→x"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_require_state_change_false_primary_path_preserves_state_env() {
    // Verifies that eval_enabled_uncached correctly snapshots state_env BEFORE
    // clearing it (Part of #2755). Previously, state_env was cleared before
    // eval_enabled_cp could call snapshot_state_pairs, causing a panic.
    //
    // The identity action (x' = x) with require_state_change=false and the
    // current state as the sole successor should evaluate ENABLED to true.
    crate::liveness::clear_enabled_cache();

    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let identity_action = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x))));
    let current = State::from_pairs([("x", Value::int(5))]);

    let enabled = LiveExpr::enabled_with_bindings(identity_action, false, None, 2574, None);

    let mut checker = make_checker_with_vars(LiveExpr::Bool(true), &["x"]);
    checker
        .state_successors
        .insert(current.fingerprint(), Arc::new(vec![current.clone()]));

    let result = checker.eval_check_on_state(&enabled, &current);
    assert!(
        result.expect("eval_check_on_state should succeed after state_env fix"),
        "ENABLED(x' = x) with require_state_change=false should be true"
    );
}
