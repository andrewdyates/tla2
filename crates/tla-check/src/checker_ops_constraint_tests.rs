// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for constraint checking functions in `crate::checker_ops`.
//!
//! Part of #2683: adds unit test coverage for eval_constraint_bool,
//! check_constraints_in_bound_scope, check_state_constraints_array,
//! check_action_constraints_array, and check_constraints_for_successor_array.

use super::*;
use crate::config::TerminalSpec;
use crate::eval::EvalCtx;
use crate::state::ArrayState;
use crate::var_index::VarRegistry;
use crate::EvalCheckError;
use crate::Value;

/// Helper to parse a TLA+ module and set up EvalCtx with variables registered.
/// Returns (ctx, variable_names_in_order) for use in constraint tests.
fn setup_for_constraints(src: &str) -> (EvalCtx, Vec<String>) {
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let tla_core::ast::Unit::Variable(vars) = &unit.node {
            for var in vars {
                ctx.register_var(Arc::from(var.node.as_str()));
                var_names.push(var.node.clone());
            }
        }
    }

    (ctx, var_names)
}

// ===========================================================================
// eval_constraint_bool tests
// ===========================================================================

#[test]
fn eval_constraint_bool_returns_true_for_true_operator() {
    let src = r#"
---- MODULE ConstraintTrue ----
VARIABLE x
Constr == TRUE
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let _guard = ctx.bind_state_env_guard(arr.env_ref());

    let result = eval_constraint_bool(&mut ctx, "Constr");
    assert!(result.unwrap(), "TRUE constraint should evaluate to true");
}

#[test]
fn eval_constraint_bool_returns_false_for_false_operator() {
    let src = r#"
---- MODULE ConstraintFalse ----
VARIABLE x
Constr == FALSE
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let _guard = ctx.bind_state_env_guard(arr.env_ref());

    let result = eval_constraint_bool(&mut ctx, "Constr");
    assert!(
        !result.unwrap(),
        "FALSE constraint should evaluate to false"
    );
}

#[test]
fn eval_constraint_bool_errors_on_non_boolean_result() {
    let src = r#"
---- MODULE ConstraintNonBool ----
VARIABLE x
Constr == 42
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let _guard = ctx.bind_state_env_guard(arr.env_ref());

    let result = eval_constraint_bool(&mut ctx, "Constr");
    match result {
        Err(CheckError::Eval(EvalCheckError::ConstraintNotBoolean(name))) => {
            assert_eq!(name, "Constr", "error should name the constraint operator");
        }
        other => panic!("expected ConstraintNotBoolean, got {:?}", other),
    }
}

#[test]
fn eval_constraint_bool_errors_on_unknown_operator() {
    let src = r#"
---- MODULE ConstraintMissing ----
VARIABLE x
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let _guard = ctx.bind_state_env_guard(arr.env_ref());

    let result = eval_constraint_bool(&mut ctx, "NonexistentConstraint");
    assert!(
        matches!(result, Err(CheckError::Eval(EvalCheckError::Eval(_)))),
        "expected EvalError for unknown operator, got {:?}",
        result
    );
}

// ===========================================================================
// check_constraints_in_bound_scope tests
// ===========================================================================

#[test]
fn check_constraints_in_bound_scope_all_pass() {
    let src = r#"
---- MODULE ConstraintAllPass ----
VARIABLE x
ConstrA == TRUE
ConstrB == TRUE
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let _guard = ctx.bind_state_env_guard(arr.env_ref());

    let constraints = vec!["ConstrA".to_string(), "ConstrB".to_string()];
    let result = check_constraints_in_bound_scope(&mut ctx, &constraints);
    assert!(result.unwrap(), "all-true constraints should pass");
}

#[test]
fn check_constraints_in_bound_scope_short_circuits_on_false() {
    let src = r#"
---- MODULE ConstraintShortCircuit ----
VARIABLE x
ConstrA == TRUE
ConstrB == FALSE
ConstrC == TRUE
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let _guard = ctx.bind_state_env_guard(arr.env_ref());

    let constraints = vec![
        "ConstrA".to_string(),
        "ConstrB".to_string(),
        "ConstrC".to_string(),
    ];
    let result = check_constraints_in_bound_scope(&mut ctx, &constraints);
    assert!(
        !result.unwrap(),
        "should return false on first failing constraint"
    );
}

// ===========================================================================
// check_state_constraints_array tests
// ===========================================================================

#[test]
fn check_state_constraints_array_empty_constraints_returns_true() {
    let mut ctx = EvalCtx::new();
    let arr = ArrayState::from_values(vec![]);
    let result = check_state_constraints_array(&mut ctx, &[], &arr);
    assert!(result.unwrap(), "empty constraints should always pass");
}

#[test]
fn check_state_constraints_array_passing_constraint() {
    let src = r#"
---- MODULE StateConstrPass ----
EXTENDS Integers
VARIABLE x
Constr == x >= 0
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let arr = ArrayState::from_values(vec![Value::int(5)]);
    let constraints = vec!["Constr".to_string()];
    let result = check_state_constraints_array(&mut ctx, &constraints, &arr);
    assert!(result.unwrap(), "x=5 should satisfy x >= 0");
}

#[test]
fn check_state_constraints_array_failing_constraint() {
    let src = r#"
---- MODULE StateConstrFail ----
EXTENDS Integers
VARIABLE x
Constr == x >= 0
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let arr = ArrayState::from_values(vec![Value::int(-1)]);
    let constraints = vec!["Constr".to_string()];
    let result = check_state_constraints_array(&mut ctx, &constraints, &arr);
    assert!(!result.unwrap(), "x=-1 should fail x >= 0");
}

#[test]
fn check_state_constraints_array_multi_variable_conjunction() {
    let src = r#"
---- MODULE StateConstrMultiVar ----
EXTENDS Integers
VARIABLE x, y
Constr == x >= 0 /\ y >= 0
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let constraints = vec!["Constr".to_string()];

    // Both positive: should pass
    let arr_pass = ArrayState::from_values(vec![Value::int(3), Value::int(7)]);
    let result = check_state_constraints_array(&mut ctx, &constraints, &arr_pass);
    assert!(result.unwrap(), "x=3, y=7 should satisfy x >= 0 /\\ y >= 0");

    // First negative: should fail
    let arr_fail_x = ArrayState::from_values(vec![Value::int(-1), Value::int(5)]);
    let result = check_state_constraints_array(&mut ctx, &constraints, &arr_fail_x);
    assert!(!result.unwrap(), "x=-1, y=5 should fail x >= 0 /\\ y >= 0");

    // Second negative: should fail
    let arr_fail_y = ArrayState::from_values(vec![Value::int(2), Value::int(-3)]);
    let result = check_state_constraints_array(&mut ctx, &constraints, &arr_fail_y);
    assert!(!result.unwrap(), "x=2, y=-3 should fail x >= 0 /\\ y >= 0");
}

// ===========================================================================
// check_action_constraints_array tests
// ===========================================================================

#[test]
fn check_action_constraints_array_empty_returns_true() {
    let mut ctx = EvalCtx::new();
    let current = ArrayState::from_values(vec![]);
    let succ = ArrayState::from_values(vec![]);
    let result = check_action_constraints_array(&mut ctx, &[], &current, &succ);
    assert!(result.unwrap(), "empty action constraints should pass");
}

#[test]
fn check_action_constraints_array_primed_expression_passing() {
    let src = r#"
---- MODULE ActionConstrPrimePass ----
EXTENDS Integers
VARIABLE x
ActionConstr == x' > x
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let current = ArrayState::from_values(vec![Value::int(5)]);
    let succ = ArrayState::from_values(vec![Value::int(10)]);
    let constraints = vec!["ActionConstr".to_string()];
    let result = check_action_constraints_array(&mut ctx, &constraints, &current, &succ);
    assert!(result.unwrap(), "x=5 -> x'=10 should satisfy x' > x");
}

#[test]
fn check_action_constraints_array_primed_expression_failing() {
    let src = r#"
---- MODULE ActionConstrPrimeFail ----
EXTENDS Integers
VARIABLE x
ActionConstr == x' > x
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let current = ArrayState::from_values(vec![Value::int(10)]);
    let succ = ArrayState::from_values(vec![Value::int(3)]);
    let constraints = vec!["ActionConstr".to_string()];
    let result = check_action_constraints_array(&mut ctx, &constraints, &current, &succ);
    assert!(!result.unwrap(), "x=10 -> x'=3 should fail x' > x");
}

// ===========================================================================
// check_constraints_for_successor_array tests
// ===========================================================================

#[test]
fn check_constraints_for_successor_array_state_constraint_fails() {
    let src = r#"
---- MODULE SuccConstrStateFails ----
EXTENDS Integers
VARIABLE x
StateConstr == x >= 0
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let current = ArrayState::from_values(vec![Value::int(5)]);
    let succ = ArrayState::from_values(vec![Value::int(-1)]);
    let state_constraints = vec!["StateConstr".to_string()];
    let result =
        check_constraints_for_successor_array(&mut ctx, &state_constraints, &[], &current, &succ);
    assert!(
        !result.unwrap(),
        "successor with x=-1 should fail state constraint x >= 0"
    );
}

#[test]
fn check_constraints_for_successor_array_all_pass() {
    let src = r#"
---- MODULE SuccConstrAllPass ----
EXTENDS Integers
VARIABLE x
StateConstr == x >= 0
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let current = ArrayState::from_values(vec![Value::int(0)]);
    let succ = ArrayState::from_values(vec![Value::int(1)]);
    let state_constraints = vec!["StateConstr".to_string()];
    let result =
        check_constraints_for_successor_array(&mut ctx, &state_constraints, &[], &current, &succ);
    assert!(
        result.unwrap(),
        "successor with x=1 should pass state constraint x >= 0"
    );
}

#[test]
fn check_constraints_for_successor_array_state_pass_action_fail() {
    let src = r#"
---- MODULE SuccConstrMixed ----
EXTENDS Integers
VARIABLE x
StateConstr == x >= 0
ActionConstr == x' > x
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let current = ArrayState::from_values(vec![Value::int(5)]);
    // Successor passes state constraint (x=3 >= 0) but fails action constraint (3 > 5 is false)
    let succ = ArrayState::from_values(vec![Value::int(3)]);
    let state_constraints = vec!["StateConstr".to_string()];
    let action_constraints = vec!["ActionConstr".to_string()];
    let result = check_constraints_for_successor_array(
        &mut ctx,
        &state_constraints,
        &action_constraints,
        &current,
        &succ,
    );
    assert!(
        !result.unwrap(),
        "successor x=3 passes state (>=0) but fails action (3 > 5), should return false"
    );
}

#[test]
fn check_constraints_for_successor_array_both_pass() {
    let src = r#"
---- MODULE SuccConstrBothPass ----
EXTENDS Integers
VARIABLE x
StateConstr == x >= 0
ActionConstr == x' > x
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let current = ArrayState::from_values(vec![Value::int(5)]);
    let succ = ArrayState::from_values(vec![Value::int(10)]);
    let state_constraints = vec!["StateConstr".to_string()];
    let action_constraints = vec!["ActionConstr".to_string()];
    let result = check_constraints_for_successor_array(
        &mut ctx,
        &state_constraints,
        &action_constraints,
        &current,
        &succ,
    );
    assert!(
        result.unwrap(),
        "successor x=10 passes state (>=0) and action (10 > 5), should return true"
    );
}

// ===========================================================================
// check_terminal_array_state tests
// ===========================================================================

#[test]
fn check_terminal_array_state_none_returns_false() {
    let mut ctx = EvalCtx::new();
    let registry = VarRegistry::new();
    let arr = ArrayState::from_values(vec![]);
    let result = check_terminal_array_state(&mut ctx, None, &registry, &arr);
    assert!(!result.unwrap(), "None terminal should always return false");
}

#[test]
fn check_terminal_array_state_predicate_match_returns_true() {
    let mut ctx = EvalCtx::new();
    let mut registry = VarRegistry::new();
    registry.register("state");
    // TLC config syntax: quoted strings → parse_constant_value produces Value::string
    let terminal = TerminalSpec::Predicates(vec![("state".to_string(), "\"SAT\"".to_string())]);
    let arr = ArrayState::from_values(vec![Value::string("SAT")]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr);
    assert!(result.unwrap(), "state=SAT should match terminal predicate");
}

#[test]
fn check_terminal_array_state_predicate_no_match_returns_false() {
    let mut ctx = EvalCtx::new();
    let mut registry = VarRegistry::new();
    registry.register("state");
    let terminal = TerminalSpec::Predicates(vec![("state".to_string(), "\"SAT\"".to_string())]);
    let arr = ArrayState::from_values(vec![Value::string("UNSAT")]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr);
    assert!(
        !result.unwrap(),
        "state=UNSAT should not match terminal predicate for SAT"
    );
}

#[test]
fn check_terminal_array_state_predicate_integer_match() {
    let mut ctx = EvalCtx::new();
    let mut registry = VarRegistry::new();
    registry.register("count");
    let terminal = TerminalSpec::Predicates(vec![("count".to_string(), "0".to_string())]);
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr);
    assert!(result.unwrap(), "count=0 should match terminal predicate 0");
}

#[test]
fn check_terminal_array_state_predicate_unknown_var_returns_false() {
    let mut ctx = EvalCtx::new();
    let registry = VarRegistry::new();
    let terminal =
        TerminalSpec::Predicates(vec![("nonexistent".to_string(), "\"SAT\"".to_string())]);
    let arr = ArrayState::from_values(vec![]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr);
    assert!(
        !result.unwrap(),
        "predicate for unknown variable should return false"
    );
}

#[test]
fn check_terminal_array_state_predicate_any_match_in_list() {
    let mut ctx = EvalCtx::new();
    let mut registry = VarRegistry::new();
    registry.register("x");
    registry.register("y");
    // TLC config syntax: quoted strings for string comparison
    let terminal = TerminalSpec::Predicates(vec![
        ("x".to_string(), "\"done\"".to_string()),
        ("y".to_string(), "\"finished\"".to_string()),
    ]);
    // x doesn't match but y does
    let arr = ArrayState::from_values(vec![Value::string("running"), Value::string("finished")]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr);
    assert!(
        result.unwrap(),
        "should return true when any predicate matches"
    );
}

#[test]
fn check_terminal_array_state_operator_true_returns_true() {
    let src = r#"
---- MODULE TermOp ----
VARIABLE x
IsTerminal == TRUE
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let registry = VarRegistry::new();
    let terminal = TerminalSpec::Operator("IsTerminal".to_string());
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr);
    assert!(
        result.unwrap(),
        "TRUE operator should mark state as terminal"
    );
}

#[test]
fn check_terminal_array_state_operator_false_returns_false() {
    let src = r#"
---- MODULE TermOpFalse ----
VARIABLE x
IsTerminal == FALSE
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let registry = VarRegistry::new();
    let terminal = TerminalSpec::Operator("IsTerminal".to_string());
    let arr = ArrayState::from_values(vec![Value::int(0)]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr);
    assert!(
        !result.unwrap(),
        "FALSE operator should not mark state as terminal"
    );
}

#[test]
fn check_terminal_array_state_operator_state_dependent() {
    let src = r#"
---- MODULE TermOpState ----
EXTENDS Integers
VARIABLE x
IsTerminal == x = 42
===="#;
    let (mut ctx, _vars) = setup_for_constraints(src);
    let registry = VarRegistry::new();
    let terminal = TerminalSpec::Operator("IsTerminal".to_string());

    let arr_yes = ArrayState::from_values(vec![Value::int(42)]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr_yes);
    assert!(result.unwrap(), "x=42 should be terminal");

    let arr_no = ArrayState::from_values(vec![Value::int(10)]);
    let result = check_terminal_array_state(&mut ctx, Some(&terminal), &registry, &arr_no);
    assert!(!result.unwrap(), "x=10 should not be terminal");
}
