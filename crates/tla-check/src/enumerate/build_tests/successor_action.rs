// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `enumerate_action_successors` tests: basic actions, disabled guards, UNCHANGED,
//! ModuleRef, UNCHANGED tuple, and bind/unbind enumeration patterns (#104).

use super::*;

// ========================================================================
// Regression tests for #55: ENABLED evaluation via fresh enumeration
// ========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_action_successors_basic() {
    // Test that enumerate_action_successors finds successors for a simple action
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Action == x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0))]);

    // Bind current state variables to context (as enumerate_successors does)
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    // Find the Action operator
    let action_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Action" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let successors =
        enumerate_action_successors(&mut ctx, &action_def.body, &current_state, &vars).unwrap();

    assert_eq!(successors.len(), 1);
    assert_eq!(
        successors[0].get("x").and_then(tla_value::Value::as_i64),
        Some(1)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_action_successors_disabled() {
    // Test that a disabled action (guard fails) returns empty successors
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Action == x > 100 /\ x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0))]);

    // Bind current state variables to context
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let action_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Action" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let successors =
        enumerate_action_successors(&mut ctx, &action_def.body, &current_state, &vars).unwrap();

    // Action is disabled because x = 0, not > 100
    assert!(
        successors.is_empty(),
        "Disabled action should return no successors"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_action_successors_multiple() {
    // Test that enumerate_action_successors finds all successors for non-deterministic action
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Action == x' \in {1, 2, 3}
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0))]);

    // Bind current state variables to context
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let action_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Action" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let successors =
        enumerate_action_successors(&mut ctx, &action_def.body, &current_state, &vars).unwrap();

    // Should find 3 successors: x=1, x=2, x=3
    assert_eq!(successors.len(), 3);

    let mut values: Vec<i64> = successors
        .iter()
        .filter_map(|s| s.get("x").and_then(tla_value::Value::as_i64))
        .collect();
    values.sort_unstable();
    assert_eq!(values, vec![1, 2, 3]);
}

// ========================================================================
// Regression tests for #54/#61: ModuleRef handling in enumerate_next_rec_inner
// ========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_module_ref_simple() {
    // Test that ModuleRef (INSTANCE operator calls) are properly enumerated
    // This is a simplified version of the AllocatorImplementation bug
    let src = r#"
---- MODULE Inner ----
VARIABLE v
InnerAction == v' = v + 1
====
"#;
    // Note: Testing INSTANCE requires more setup. For now, test the basic
    // enumeration path works for regular actions (the ModuleRef code path
    // is tested via integration tests in test_tlaplus_examples.py)

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("v", Value::int(0))]);

    // Bind current state variables to context
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let action_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "InnerAction" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let successors =
        enumerate_action_successors(&mut ctx, &action_def.body, &current_state, &vars).unwrap();

    assert_eq!(successors.len(), 1);
    assert_eq!(
        successors[0].get("v").and_then(tla_value::Value::as_i64),
        Some(1)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_unchanged_in_action() {
    // Test that UNCHANGED is properly handled during action enumeration
    // Relevant to #54/#61 where UNCHANGED <<unsat, alloc>> was mishandled
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Action == x' = x + 1 /\ UNCHANGED y
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(5))]);

    // Bind current state variables to context
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let action_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Action" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let successors =
        enumerate_action_successors(&mut ctx, &action_def.body, &current_state, &vars).unwrap();

    assert_eq!(successors.len(), 1);
    // x should be incremented
    assert_eq!(
        successors[0].get("x").and_then(tla_value::Value::as_i64),
        Some(1)
    );
    // y should be UNCHANGED (still 5)
    assert_eq!(
        successors[0].get("y").and_then(tla_value::Value::as_i64),
        Some(5)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_unchanged_tuple() {
    // Test UNCHANGED <<a, b>> syntax (tuple unchanged)
    let src = r#"
---- MODULE Test ----
VARIABLE a, b, c
Init == a = 0 /\ b = 0 /\ c = 0
Action == c' = c + 1 /\ UNCHANGED <<a, b>>
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([
        ("a", Value::int(1)),
        ("b", Value::int(2)),
        ("c", Value::int(0)),
    ]);

    // Bind current state variables to context
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let action_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Action" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let successors =
        enumerate_action_successors(&mut ctx, &action_def.body, &current_state, &vars).unwrap();

    assert_eq!(successors.len(), 1);
    // a and b should be unchanged
    assert_eq!(
        successors[0].get("a").and_then(tla_value::Value::as_i64),
        Some(1)
    );
    assert_eq!(
        successors[0].get("b").and_then(tla_value::Value::as_i64),
        Some(2)
    );
    // c should be incremented
    assert_eq!(
        successors[0].get("c").and_then(tla_value::Value::as_i64),
        Some(1)
    );
}

// ============================================================================
// Bind/Unbind Enumeration Tests (Issue #104 - Test Gap)
// ============================================================================

/// Test bind/unbind enumeration with x' \in S pattern.
/// This was the key bug fixed in #101 - continuation wasn't processed for each element.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bind_unbind_in_set_membership() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' \in {1, 2, 3}
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

    let successors =
        enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars).unwrap();

    // Should produce 3 successors: x=1, x=2, x=3
    assert_eq!(successors.len(), 3);
    let x_values: std::collections::BTreeSet<i64> = successors
        .iter()
        .filter_map(|s| s.get("x").and_then(tla_value::Value::as_i64))
        .collect();
    assert_eq!(x_values, [1, 2, 3].into_iter().collect());
}

/// Test bind/unbind with x' \in S /\ y' = f(x') pattern.
/// This tests the continuation handling - each element of S must process
/// the subsequent conjunct y' = f(x').
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bind_unbind_in_with_dependent_assignment() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' \in {1, 2, 3} /\ y' = x' * 2
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);

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

    let successors =
        enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars).unwrap();

    // Should produce 3 successors: (x=1,y=2), (x=2,y=4), (x=3,y=6)
    assert_eq!(successors.len(), 3);

    let xy_pairs: std::collections::BTreeSet<(i64, i64)> = successors
        .iter()
        .filter_map(|s| {
            let x = s.get("x").and_then(tla_value::Value::as_i64)?;
            let y = s.get("y").and_then(tla_value::Value::as_i64)?;
            Some((x, y))
        })
        .collect();

    assert_eq!(xy_pairs, [(1, 2), (2, 4), (3, 6)].into_iter().collect());
}

/// Test disjunctive next with dependent assignments across OR branches.
/// Verifies correct successor count and values for a multi-branch action
/// that includes `x' \in S /\ y' = f(x')` patterns.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disjunctive_dependent_assignment() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x, y
Init == x = 0 /\ y = 0
Next ==
    \/ x' \in {1, 2} /\ y' = x' + 10
    \/ x' = 100 /\ y' = 200
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);

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

    let successors =
        enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars).unwrap();

    // 3 successors: (x=1,y=11), (x=2,y=12), (x=100,y=200)
    assert_eq!(successors.len(), 3);

    let xy_pairs: std::collections::BTreeSet<(i64, i64)> = successors
        .iter()
        .filter_map(|s| {
            let x = s.get("x").and_then(tla_value::Value::as_i64)?;
            let y = s.get("y").and_then(tla_value::Value::as_i64)?;
            Some((x, y))
        })
        .collect();

    assert_eq!(
        xy_pairs,
        [(1, 11), (2, 12), (100, 200)].into_iter().collect()
    );
}
