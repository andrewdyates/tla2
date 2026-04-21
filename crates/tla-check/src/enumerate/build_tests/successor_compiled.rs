// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compiled action path tests: error fallback (#649, #1552), and SetPred
//! domain centralization for PrimeInSet and Exists.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_649_compiled_action_error_does_not_silently_drop_successors() {
    // Regression test for #649:
    // If compiled action evaluation errors (e.g., DivisionByZero/TypeError in a disabled
    // disjunct), the enumerator must NOT treat the whole action as disabled. It must fall
    // back so that the AST path can enumerate successors.
    //
    // Fix #1552: TLC propagates DivisionByZero fatally from Or disjuncts.
    // The error in the second disjunct terminates model checking — TLC does NOT
    // silently disable the disjunct and continue with the first.
    let src = r#"
---- MODULE Test649 ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next ==
  \/ x' = x + 1
  \/ x = 0 /\ x' = 1 \div 0
====
"#;

    let (module, mut ctx, vars) = setup_module(src);

    let next_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .unwrap();

    let current_array = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());

    let result =
        enumerate_successors_array_as_diffs(&mut ctx, next_def, &current_array, &vars, None);

    let err = result
        .expect_err("#1552: DivisionByZero in Or disjunct must propagate fatally (TLC behavior)");
    assert!(
        matches!(err, EvalError::DivisionByZero { .. }),
        "#1634: expected DivisionByZero, got {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiled_action_prime_in_set_with_setpred_domain() {
    // Regression for SetPred centralization: PrimeInSet must enumerate lazy
    // SetPred domains via eval_iter_set rather than raw iter_set().
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
VARIABLE x
Init == x = {}
Next == x' \in {s \in SUBSET {1, 2, 3} : Cardinality(s) = 1}
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::set([]))]);

    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let next_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Next" => Some(def.clone()),
            _ => None,
        })
        .expect("invariant: Next operator should exist");

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars)
        .expect("PrimeInSet over lazy SetPred domain should enumerate successfully");

    assert_eq!(
        successors.len(),
        3,
        "expected one successor per singleton subset of {{1,2,3}}"
    );

    let mut x_values: Vec<Value> = successors
        .iter()
        .map(|s| s.get("x").expect("successor must bind x").clone())
        .collect();
    x_values.sort();
    assert_eq!(
        x_values,
        vec![
            Value::set([Value::int(1)]),
            Value::set([Value::int(2)]),
            Value::set([Value::int(3)]),
        ]
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_successors_use_explicit_current_value_slice() {
    let src = r#"
---- MODULE TestCurrentSlice ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let next_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("invariant: Next operator should exist");

    let current_array = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let worker_current_values = vec![Value::SmallInt(1)];

    let diffs = enumerate_successors_array_as_diffs_with_current_values(
        &mut ctx,
        next_def,
        &current_array,
        &worker_current_values,
        &vars,
        None,
    )
    .expect("successor enumeration should succeed")
    .expect("successor enumeration should produce successors");

    assert_eq!(diffs.len(), 1, "expected exactly one successor");
    assert_eq!(
        diffs[0].changes.as_slice(),
        &[(VarIndex(0), Value::SmallInt(2))],
        "successor enumeration should read the explicit current-value slice"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_successors_use_explicit_current_value_slice() {
    let src = r#"
---- MODULE TestCurrentSliceUnchanged ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let next_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("invariant: Next operator should exist");

    let registry = ctx.var_registry().clone();
    let x_idx = registry
        .get("x")
        .expect("invariant: x should be registered");
    let current_array = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let worker_current_values = vec![Value::SmallInt(1)];

    let diffs = enumerate_successors_array_as_diffs_with_current_values(
        &mut ctx,
        next_def,
        &current_array,
        &worker_current_values,
        &vars,
        None,
    )
    .expect("successor enumeration should succeed")
    .expect("UNCHANGED should still produce a stuttering successor");

    assert_eq!(diffs.len(), 1, "expected exactly one successor");
    assert_eq!(
        diffs[0].changes.as_slice(),
        &[(x_idx, Value::SmallInt(1))],
        "UNCHANGED must preserve the explicit current-value slice, not the base array"
    );

    let materialized = diffs[0].materialize(&current_array, &registry);
    assert_eq!(
        materialized.get(x_idx),
        Value::SmallInt(1),
        "materialized successor should use the worker-local current value"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiled_action_exists_with_setpred_domain() {
    // Regression for SetPred centralization: Exists domain splitting must treat
    // SetPred domains as enumerable when evaluated with context.
    let src = r#"
---- MODULE Test ----
EXTENDS FiniteSets
VARIABLE x
Init == x = {}
Next == \E v \in {s \in SUBSET {1, 2, 3} : Cardinality(s) = 1}: x' = v
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::set([]))]);

    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let next_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Next" => Some(def.clone()),
            _ => None,
        })
        .expect("invariant: Next operator should exist");

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars)
        .expect("Exists over lazy SetPred domain should enumerate successfully");

    assert_eq!(
        successors.len(),
        3,
        "expected one successor per singleton subset of {{1,2,3}}"
    );

    let mut x_values: Vec<Value> = successors
        .iter()
        .map(|s| s.get("x").expect("successor must bind x").clone())
        .collect();
    x_values.sort();
    assert_eq!(
        x_values,
        vec![
            Value::set([Value::int(1)]),
            Value::set([Value::int(2)]),
            Value::set([Value::int(3)]),
        ]
    );
}
