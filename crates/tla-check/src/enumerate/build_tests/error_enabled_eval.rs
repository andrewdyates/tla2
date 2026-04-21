// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// ENABLED evaluation tests
// ========================================================================

/// Test that eval_enabled returns true when action produces successors.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_returns_true_when_action_enabled() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = crate::enabled::eval_enabled_cp(&mut ctx, &next_def.body, &vars);
    assert!(result.is_ok());
    assert!(result.unwrap(), "Action should be enabled");
}

/// Test that eval_enabled returns false when action is guarded out.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_returns_false_when_action_guarded() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x > 100 /\ x' = x + 1  \* Guard prevents action
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = crate::enabled::eval_enabled_cp(&mut ctx, &next_def.body, &vars);
    assert!(result.is_ok());
    assert!(!result.unwrap(), "Action should be disabled due to guard");
}

/// Test that eval_enabled returns false when action has runtime error (TLC semantics).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_returns_false_on_runtime_error() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
f == [n \in {1, 2} |-> n * 10]
Init == x = 0
Next == x' = f[42]  \* NotInDomain - action treated as disabled
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = crate::enabled::eval_enabled_cp(&mut ctx, &next_def.body, &vars);
    assert!(result.is_ok(), "Runtime error should be caught");
    assert!(
        !result.unwrap(),
        "Action should be disabled due to runtime error"
    );
}

/// Regression test for #1103: ENABLED should short-circuit OR once one
/// branch produces a successor, just like TLC's enabled() implementation.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_short_circuits_or_after_first_enabled_branch() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Good == x' = x + 1
Bad == Assert(FALSE, "right branch must not run") /\ x' = x
Next == Good \/ Bad
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = crate::enabled::eval_enabled_cp(&mut ctx, &next_def.body, &vars);
    assert!(result.is_ok(), "Right OR branch should not be evaluated");
    assert!(result.unwrap(), "Left OR branch enables the action");
}

/// Regression test for #1103: ENABLED should short-circuit EXISTS once it
/// finds one witness that yields a successor.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_short_circuits_exists_after_first_successor() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == \E i \in {1, 2} :
          IF i = 1
          THEN x' = x + 1
          ELSE (Assert(FALSE, "second EXISTS witness must not run") /\ x' = x)
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = crate::enabled::eval_enabled_cp(&mut ctx, &next_def.body, &vars);
    assert!(
        result.is_ok(),
        "Later EXISTS witnesses should not be evaluated"
    );
    assert!(result.unwrap(), "First EXISTS witness enables the action");
}

/// Regression test for #1103: nested ENABLED inside an OR branch should
/// not clear the outer early-exit flag.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_nested_enabled_preserves_outer_or_short_circuit() {
    // Install ENABLED hook so nested ENABLED(x' = x + 1) inside Inner can be
    // evaluated via the unified enumerator's catch-all → eval() → hook path.
    // In production this is done at checker startup (parallel/checker.rs:562).
    crate::eval::set_enabled_hook(crate::enabled::eval_enabled_cp);

    let src = r#"
---- MODULE Test ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Inner == ENABLED (x' = x + 1)
Good == Inner /\ x' = x + 1
Bad == Assert(FALSE, "right branch must not run after nested ENABLED") /\ x' = x
Next == Good \/ Bad
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = crate::enabled::eval_enabled_cp(&mut ctx, &next_def.body, &vars);
    assert!(
        result.is_ok(),
        "Right OR branch should still be skipped after nested ENABLED"
    );
    assert!(result.unwrap(), "Left OR branch enables the action");
}
