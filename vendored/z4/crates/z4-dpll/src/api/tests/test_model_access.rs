// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for model and value extraction: declared_variables, get_model_map,
//! try_get_model*, try_get_value*, backward-compatible option-returning getters.

use num_bigint::BigInt;

use crate::api::*;

#[test]
fn test_declared_variables_excludes_fresh_vars() {
    let mut solver = Solver::new(Logic::QfLia);
    let _x = solver.declare_const("x", Sort::Int);
    let _y = solver.declare_const("y", Sort::Bool);
    let _fresh = solver.fresh_var("tmp", Sort::Int);

    let mut names: Vec<_> = solver
        .declared_variables()
        .map(|(name, _)| name.to_string())
        .collect();
    names.sort_unstable();
    assert_eq!(names, vec!["x".to_string(), "y".to_string()]);
}

#[test]
fn test_get_model_map_returns_structured_assignments() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let seven = solver.int_const(7);
    let nine = solver.int_const(9);
    let x_eq_7 = solver.eq(x, seven);
    let y_eq_9 = solver.eq(y, nine);
    solver.assert_term(x_eq_7);
    solver.assert_term(y_eq_9);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model_map = solver
        .get_model_map()
        .expect("SAT should provide model map");
    assert_eq!(
        model_map.get("x"),
        Some(&ModelValue::Int(BigInt::from(7))),
        "x should be assigned"
    );
    assert_eq!(
        model_map.get("y"),
        Some(&ModelValue::Int(BigInt::from(9))),
        "y should be assigned"
    );
}

#[test]
fn test_get_model_map_returns_none_when_last_result_not_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert_eq!(solver.check_sat(), SolveResult::Unsat);
    assert!(solver.get_model_map().is_none());
}

#[test]
fn test_try_get_model_no_result() {
    let solver = Solver::new(Logic::QfLia);
    let err = solver.try_get_model().unwrap_err();
    assert!(
        matches!(err, SolverError::NoResult),
        "expected NoResult, got {err:?}"
    );
}

#[test]
fn test_try_get_model_str_no_result() {
    let solver = Solver::new(Logic::QfLia);
    let err = solver.try_get_model_str().unwrap_err();
    assert!(
        matches!(err, SolverError::NoResult),
        "expected NoResult, got {err:?}"
    );
}

#[test]
fn test_try_get_model_map_no_result() {
    let solver = Solver::new(Logic::QfLia);
    let err = solver.try_get_model_map().unwrap_err();
    assert!(
        matches!(err, SolverError::NoResult),
        "expected NoResult, got {err:?}"
    );
}

#[test]
fn test_try_get_model_after_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let err = solver.try_get_model().unwrap_err();
    assert!(
        matches!(err, SolverError::NotSat),
        "expected NotSat, got {err:?}"
    );
}

#[test]
fn test_try_get_model_str_after_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let err = solver.try_get_model_str().unwrap_err();
    assert!(
        matches!(err, SolverError::NotSat),
        "expected NotSat, got {err:?}"
    );
}

#[test]
fn test_try_get_model_map_after_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let err = solver.try_get_model_map().unwrap_err();
    assert!(
        matches!(err, SolverError::NotSat),
        "expected NotSat, got {err:?}"
    );
}

#[test]
fn test_try_get_model_after_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver.try_get_model().expect("should succeed after SAT");
    assert!(!model.model().is_empty());
}

#[test]
fn test_try_get_model_str_after_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model_str = solver
        .try_get_model_str()
        .expect("should succeed after SAT");
    assert!(model_str.contains("define-fun"));
}

#[test]
fn test_try_get_model_map_after_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model_map = solver
        .try_get_model_map()
        .expect("should succeed after SAT");
    assert_eq!(model_map.get("x"), Some(&ModelValue::Int(BigInt::from(5))));
}

#[test]
fn test_try_get_values_no_result() {
    let solver = Solver::new(Logic::QfLia);
    let err = solver.try_get_values(&[]).unwrap_err();
    assert!(
        matches!(err, SolverError::NoResult),
        "expected NoResult, got {err:?}"
    );
}

#[test]
fn test_try_get_values_after_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert_eq!(solver.check_sat(), SolveResult::Unsat);

    let err = solver.try_get_values(&[x]).unwrap_err();
    assert!(
        matches!(err, SolverError::NotSat),
        "expected NotSat, got {err:?}"
    );
}

#[test]
fn test_try_get_value_after_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let value = solver.try_get_value(x).expect("should succeed after SAT");
    assert_eq!(value, ModelValue::Int(BigInt::from(5)));
}

#[test]
fn test_try_get_values_produce_models_disabled() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_option(":produce-models", "false");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    solver.assert_term(x_gt_0);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let err = solver.try_get_values(&[x]).unwrap_err();
    match err {
        SolverError::ModelGenerationFailed(msg) => assert!(
            msg.contains("model generation is not enabled"),
            "unexpected message: {msg}"
        ),
        other => panic!("expected ModelGenerationFailed, got {other:?}"),
    }
}

#[test]
fn test_try_get_model_map_empty_model_produce_models_disabled() {
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_option(":produce-models", "false");
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let err = solver.try_get_model_map().unwrap_err();
    match err {
        SolverError::ModelGenerationFailed(msg) => assert!(
            msg.contains("model generation is not enabled"),
            "unexpected message: {msg}"
        ),
        other => panic!("expected ModelGenerationFailed, got {other:?}"),
    }
}

#[test]
fn test_get_model_backward_compat_delegates_to_try() {
    // Verify that the Option-returning get_model() still works after refactor
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // Option path still works
    assert!(solver.get_model().is_some());
    assert!(solver.get_model_str().is_some());
    assert!(solver.get_model_map().is_some());
}

#[test]
fn test_get_model_backward_compat_none_before_check_sat() {
    let solver = Solver::new(Logic::QfLia);
    assert!(solver.get_model().is_none());
    assert!(solver.get_model_str().is_none());
    assert!(solver.get_model_map().is_none());
}

#[test]
fn test_assert_after_check_sat_invalidates_model_access() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    let eq_one = solver.eq(x, one);
    solver.assert_term(eq_one);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
    assert!(solver.get_model().is_some());
    assert!(solver.get_model_str().is_some());
    assert!(solver.get_model_map().is_some());

    let eq_two = solver.eq(x, two);
    solver.assert_term(eq_two);

    let model_err = solver.try_get_model().unwrap_err();
    assert!(
        matches!(model_err, SolverError::NoResult),
        "expected NoResult after post-solve assertion, got {model_err:?}"
    );

    let model_str_err = solver.try_get_model_str().unwrap_err();
    assert!(
        matches!(model_str_err, SolverError::NoResult),
        "expected NoResult after post-solve assertion, got {model_str_err:?}"
    );

    let model_map_err = solver.try_get_model_map().unwrap_err();
    assert!(
        matches!(model_map_err, SolverError::NoResult),
        "expected NoResult after post-solve assertion, got {model_map_err:?}"
    );
}
