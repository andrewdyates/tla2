// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};

fn make_test_system() -> TransitionSystem {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        // init: x = 0
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        // trans: x_next = x + 1
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        // query: x >= 10
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10)),
    )
}

fn make_high_arity_linear_problem(arity: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int; arity]);

    let fact_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(1)))
        .collect();
    problem.add_clause(HornClause::fact(ChcExpr::Bool(true), inv, fact_args));

    let body_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(2)))
        .collect();
    let head_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(3)))
        .collect();
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, body_args)]),
        ClauseHead::Predicate(inv, head_args),
    ));

    let query_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(4)))
        .collect();
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv, query_args,
    )])));

    problem
}

fn assert_flat_and_arity(expr: &ChcExpr, expected_arity: usize, label: &str) {
    let args = match expr {
        ChcExpr::Op(ChcOp::And, args) => args,
        other => panic!("{label} should be an n-ary And, got {other:?}"),
    };

    assert_eq!(
        args.len(),
        expected_arity,
        "{label} conjunction arity mismatch"
    );
    assert!(
        args.iter()
            .all(|arg| !matches!(arg.as_ref(), ChcExpr::Op(ChcOp::And, _))),
        "{label} should not contain nested And nodes"
    );
}

fn contains_var_equality(expr: &ChcExpr, lhs: &ChcVar, rhs: &ChcVar) -> bool {
    fn visit(expr: &ChcExpr, lhs: &ChcExpr, rhs: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let left = args[0].as_ref();
                let right = args[1].as_ref();
                (left == lhs && right == rhs) || (left == rhs && right == lhs)
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args.iter().any(|arg| visit(arg, lhs, rhs)),
            ChcExpr::ConstArray(_ks, value) => visit(value, lhs, rhs),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => false,
        }
    }

    visit(expr, &ChcExpr::var(lhs.clone()), &ChcExpr::var(rhs.clone()))
}

#[test]
fn test_version_var() {
    let x = ChcVar::new("x", ChcSort::Int);

    // Time 0 should return original
    let v0 = TransitionSystem::version_var(&x, 0);
    assert_eq!(v0.name, "x");

    // Time 1 should suffix
    let v1 = TransitionSystem::version_var(&x, 1);
    assert_eq!(v1.name, "x_1");

    // Time 5 should suffix
    let v5 = TransitionSystem::version_var(&x, 5);
    assert_eq!(v5.name, "x_5");
}

#[test]
fn test_k_transition_zero() {
    let ts = make_test_system();
    let unrolled = ts.k_transition(0);
    assert_eq!(unrolled, ChcExpr::Bool(true));
}

#[test]
fn test_k_transition_one() {
    let ts = make_test_system();
    let unrolled = ts.k_transition(1);

    // Should be: x_1 = x + 1
    // Variables in the formula
    let vars = unrolled.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(var_names.contains(&"x"));
    assert!(var_names.contains(&"x_1"));
}

#[test]
fn test_k_transition_multiple() {
    let ts = make_test_system();
    let unrolled = ts.k_transition(3);

    // Should contain variables at times 0, 1, 2, 3
    let vars = unrolled.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(var_names.contains(&"x"));
    assert!(var_names.contains(&"x_1"));
    assert!(var_names.contains(&"x_2"));
    assert!(var_names.contains(&"x_3"));
}

#[test]
fn test_transition_at_keeps_numeric_suffix_next_var_canonical() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_1 = ChcVar::new("x_1", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::eq(
            ChcExpr::var(x_1),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
        ),
        ChcExpr::Bool(false),
    );

    let transition = ts.transition_at(0);
    let var_names: FxHashSet<_> = transition.vars().into_iter().map(|v| v.name).collect();

    assert!(var_names.contains("x"));
    assert!(var_names.contains("x_1"));
    assert!(
        !var_names.contains("x_1__t0"),
        "numeric-suffix next-state var must not be renamed as a local: {transition:?}"
    );
}

#[test]
fn test_transition_at_versions_local_vars_per_timestep() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::and_all([
            ChcExpr::eq(
                ChcExpr::var(x_next),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y.clone())),
            ),
            ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(0)),
        ]),
        ChcExpr::Bool(false),
    );

    let transition_0 = ts.transition_at(0);
    let vars_0: FxHashSet<_> = transition_0.vars().into_iter().map(|v| v.name).collect();
    assert!(vars_0.contains("y__t0"));
    assert!(!vars_0.contains("y"));

    let transition_1 = ts.transition_at(1);
    let vars_1: FxHashSet<_> = transition_1.vars().into_iter().map(|v| v.name).collect();
    assert!(vars_1.contains("y__t1"));
    assert!(!vars_1.contains("y"));

    let unrolled = ts.k_transition(2);
    let unrolled_vars: FxHashSet<_> = unrolled.vars().into_iter().map(|v| v.name).collect();
    assert!(unrolled_vars.contains("y__t0"));
    assert!(unrolled_vars.contains("y__t1"));
    assert!(!unrolled_vars.contains("y"));
}

#[test]
fn test_init_and_neg_init_version_local_vars_per_timestep() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::eq(
            ChcExpr::var(x),
            ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1)),
        ),
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
    );

    let init_0 = ts.init_at(0);
    let init_vars_0: FxHashSet<_> = init_0.vars().into_iter().map(|v| v.name).collect();
    assert!(init_vars_0.contains("y__i0"));
    assert!(!init_vars_0.contains("y"));

    let neg_init_2 = ts.neg_init_at(2);
    let neg_init_vars_2: FxHashSet<_> = neg_init_2.vars().into_iter().map(|v| v.name).collect();
    assert!(neg_init_vars_2.contains("y__ni2"));
    assert!(!neg_init_vars_2.contains("y"));
}

#[test]
fn test_query_and_neg_query_version_local_vars_per_timestep() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::and_all([
            ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)),
            ChcExpr::gt(
                ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
                ChcExpr::int(5),
            ),
        ]),
    );

    let query_1 = ts.query_at(1);
    let query_vars_1: FxHashSet<_> = query_1.vars().into_iter().map(|v| v.name).collect();
    assert!(query_vars_1.contains("y__q1"));
    assert!(!query_vars_1.contains("y"));

    let neg_query_3 = ts.neg_query_at(3);
    let neg_query_vars_3: FxHashSet<_> = neg_query_3.vars().into_iter().map(|v| v.name).collect();
    assert!(neg_query_vars_3.contains("y__nq3"));
    assert!(!neg_query_vars_3.contains("y"));
}

#[test]
fn test_init_at() {
    let ts = make_test_system();

    // init at time 0: x = 0
    let init0 = ts.init_at(0);
    let vars = init0.vars();
    assert!(vars.iter().any(|v| v.name == "x"));

    // init at time 2: x_2 = 0
    let init2 = ts.init_at(2);
    let vars = init2.vars();
    assert!(vars.iter().any(|v| v.name == "x_2"));
}

#[test]
fn test_state_var_names() {
    let ts = make_test_system();
    let names = ts.state_var_names();
    assert!(names.contains("x"));
    assert_eq!(names.len(), 1);
}

#[test]
fn test_shift_versioned_state_vars() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // x_2 shifted by +1 should become x_3
    let x2 = ChcVar::new("x_2", ChcSort::Int);
    let expr = ChcExpr::var(x2);
    let shifted = ts.shift_versioned_state_vars(&expr, 1);
    let vars = shifted.vars();
    assert!(vars.iter().any(|v| v.name == "x_3"));

    // x shifted by +1 should become x_1
    let expr = ChcExpr::var(x);
    let shifted = ts.shift_versioned_state_vars(&expr, 1);
    let vars = shifted.vars();
    assert!(vars.iter().any(|v| v.name == "x_1"));

    // x shifted by -1 should stay x (clamped at 0)
    let shifted = ts.shift_versioned_state_vars(&expr, -1);
    let vars = shifted.vars();
    assert!(vars.iter().any(|v| v.name == "x"));
}

#[test]
fn test_rename_state_vars_at_time1_to_time2() {
    // TPA "shift_only_next": v1 → v2, keep v0 fixed
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // Expression with all three time versions: x + x_1 + x_2
    let x0 = ChcVar::new("x", ChcSort::Int);
    let x1 = ChcVar::new("x_1", ChcSort::Int);
    let x2 = ChcVar::new("x_2", ChcSort::Int);
    let expr = ChcExpr::add(
        ChcExpr::add(ChcExpr::var(x0), ChcExpr::var(x1)),
        ChcExpr::var(x2),
    );

    // rename_state_vars_at(1, 2): x_1 → x_2, but x and x_2 unchanged
    let shifted = ts.rename_state_vars_at(&expr, 1, 2);
    let vars = shifted.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();

    // x should remain (time 0 unchanged)
    assert!(var_names.contains(&"x"), "time-0 var should be unchanged");
    // x_1 should become x_2
    assert!(!var_names.contains(&"x_1"), "x_1 should have been renamed");
    // x_2 appears (both original x_2 and renamed x_1)
    assert!(var_names.contains(&"x_2"), "should contain x_2");
}

#[test]
fn test_rename_state_vars_at_time2_to_time1() {
    // TPA "clean_interpolant": v2 → v1
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // Expression with time-2 vars: x_2 >= 0
    let x2 = ChcVar::new("x_2", ChcSort::Int);
    let expr = ChcExpr::ge(ChcExpr::var(x2), ChcExpr::int(0));

    // rename_state_vars_at(2, 1): x_2 → x_1
    let shifted = ts.rename_state_vars_at(&expr, 2, 1);
    let vars = shifted.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();

    assert!(!var_names.contains(&"x_2"), "x_2 should have been renamed");
    assert!(var_names.contains(&"x_1"), "should now contain x_1");
}

#[test]
fn test_rename_state_vars_at_same_timestep() {
    // Noop case: rename_state_vars_at(1, 1) should return identical expression
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    let x1 = ChcVar::new("x_1", ChcSort::Int);
    let expr = ChcExpr::var(x1);
    let shifted = ts.rename_state_vars_at(&expr, 1, 1);

    let vars = shifted.vars();
    assert!(vars.iter().any(|v| v.name == "x_1"), "should be unchanged");
}

#[test]
fn test_rename_state_vars_at_time0_to_time1() {
    // Can also shift time-0 to time-1 if needed
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // x >= 0 (time-0)
    let expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    // rename_state_vars_at(0, 1): x → x_1
    let shifted = ts.rename_state_vars_at(&expr, 0, 1);
    let vars = shifted.vars();

    assert!(
        !vars.iter().any(|v| v.name == "x"),
        "x should have been renamed"
    );
    assert!(
        vars.iter().any(|v| v.name == "x_1"),
        "should now contain x_1"
    );
}

#[test]
fn test_rename_state_vars_at_multiple_vars() {
    // Test with multiple state variables
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x, y],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // x_1 + y_1 = 0
    let x1 = ChcVar::new("x_1", ChcSort::Int);
    let y1 = ChcVar::new("y_1", ChcSort::Int);
    let expr = ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(x1), ChcExpr::var(y1)),
        ChcExpr::int(0),
    );

    // rename_state_vars_at(1, 2): x_1 → x_2, y_1 → y_2
    let shifted = ts.rename_state_vars_at(&expr, 1, 2);
    let vars = shifted.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();

    assert!(!var_names.contains(&"x_1"), "x_1 should be renamed");
    assert!(!var_names.contains(&"y_1"), "y_1 should be renamed");
    assert!(var_names.contains(&"x_2"), "should contain x_2");
    assert!(var_names.contains(&"y_2"), "should contain y_2");
}

#[test]
fn test_extract_transition_with_expression_body_args() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);

    // Init: Inv(0, 1)
    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::int(0), ChcExpr::int(1)],
    ));

    let x = ChcVar::new("x", ChcSort::Int);

    // Trans: Inv(x, x + 1) => Inv(x + 1, x + 2)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![
                ChcExpr::var(x.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
            ],
        ),
    ));

    // Query: Inv(0, 1) => false
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv,
        vec![ChcExpr::int(0), ChcExpr::int(1)],
    )])));

    let ts = TransitionSystem::from_chc_problem(&problem).unwrap();

    // Transition should use canonical vars (v0, v1, v0_next, v1_next), not user var `x`.
    let trans_vars = ts.transition.vars();
    let var_names: Vec<_> = trans_vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        !var_names.contains(&"x"),
        "transition should not contain user var 'x': {:?}",
        ts.transition
    );
}

#[test]
fn test_extract_transition_adds_equality_for_shared_body_and_head_var_issue_4729() {
    let problem = make_shared_body_head_var_problem_issue_4729();
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("single-predicate linear problem should extract");
    let current_f = ChcVar::new("v2", ChcSort::Int);
    let next_f = ChcVar::new("v2_next", ChcSort::Int);

    assert!(
        contains_var_equality(&ts.transition, &next_f, &current_f),
        "transition must constrain shared arg with v2_next = v2; got {:?}",
        ts.transition
    );
}

fn make_shared_body_head_var_problem_issue_4729() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate(
        "inv",
        vec![ChcSort::Int, ChcSort::Int, ChcSort::Int, ChcSort::Int],
    );
    let zeros = vec![ChcExpr::int(0); 4];

    problem.add_clause(HornClause::fact(ChcExpr::Bool(true), inv, zeros.clone()));

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let f = ChcVar::new("F", ChcSort::Int);
    let g = ChcVar::new("G", ChcSort::Int);

    // F appears in both body arg 2 and head arg 2. Without the #4729 fix,
    // body substitution consumes F first and head substitution becomes a no-op.
    let transition_constraint = ChcExpr::and_all([
        ChcExpr::eq(
            ChcExpr::var(d.clone()),
            ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(e.clone()),
            ChcExpr::add(ChcExpr::var(c.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(g.clone()),
            ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::var(f.clone())),
        ),
    ]);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![
                    ChcExpr::var(b),
                    ChcExpr::var(c),
                    ChcExpr::var(f.clone()),
                    ChcExpr::var(a),
                ],
            )],
            Some(transition_constraint),
        ),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::var(d),
                ChcExpr::var(e),
                ChcExpr::var(f),
                ChcExpr::var(g),
            ],
        ),
    ));

    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv, zeros,
    )])));

    problem
}

#[test]
fn test_from_chc_problem_high_arity_constraints_flat_and_drop_safe() {
    // #2508: high-arity argument lists must build flat n-ary conjunctions.
    // If this regresses to chained binary And nodes, dropping these formulas can overflow.
    const ARITY: usize = 4_096;

    let problem = make_high_arity_linear_problem(ARITY);
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("high-arity linear problem should extract");

    assert_flat_and_arity(&ts.init, ARITY, "init");
    assert_flat_and_arity(&ts.transition, ARITY * 2, "transition");
    assert_flat_and_arity(&ts.query, ARITY, "query");

    // Exercise normal recursive ownership teardown without leak workarounds.
    drop(ts);
}
