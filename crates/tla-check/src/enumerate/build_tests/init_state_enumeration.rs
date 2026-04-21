// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_simple() {
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 1
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .unwrap()
        .unwrap();

    assert_eq!(states.len(), 1);
    let state = &states[0];

    // Check state values
    let state_vars: Vec<_> = state.vars().collect();
    assert_eq!(state_vars.len(), 2);
    assert_eq!(state.get("x"), Some(&Value::int(0)));
    assert_eq!(state.get("y"), Some(&Value::int(1)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_membership() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {1, 2, 3}
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .unwrap()
        .unwrap();

    assert_eq!(states.len(), 3);
    // Verify actual values, not just count
    let x_values: Vec<_> = states.iter().map(|s| s.get("x").unwrap().clone()).collect();
    assert!(x_values.contains(&Value::int(1)));
    assert!(x_values.contains(&Value::int(2)));
    assert!(x_values.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_combination() {
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x \in {0, 1} /\ y \in {2, 3}
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .unwrap()
        .unwrap();

    // 2 choices for x * 2 choices for y = 4 states
    assert_eq!(states.len(), 4);
    // Verify all (x,y) pairs are present
    let pairs: Vec<_> = states
        .iter()
        .map(|s| (s.get("x").unwrap().clone(), s.get("y").unwrap().clone()))
        .collect();
    assert!(pairs.contains(&(Value::int(0), Value::int(2))));
    assert!(pairs.contains(&(Value::int(0), Value::int(3))));
    assert!(pairs.contains(&(Value::int(1), Value::int(2))));
    assert!(pairs.contains(&(Value::int(1), Value::int(3))));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_disjunctive_init() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0 \/ x = 1
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .unwrap()
        .unwrap();

    assert_eq!(states.len(), 2);
    // Verify actual values, not just count
    let x_values: Vec<_> = states.iter().map(|s| s.get("x").unwrap().clone()).collect();
    assert!(x_values.contains(&Value::int(0)));
    assert!(x_values.contains(&Value::int(1)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_conjunction_intersection() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {0, 1} /\ x \in {1, 2}
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .unwrap()
        .unwrap();

    assert_eq!(states.len(), 1);
    assert_eq!(states[0].get("x"), Some(&Value::int(1)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_conjunction_contradiction() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0 /\ x = 1
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .unwrap()
        .unwrap();

    assert!(states.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_nested_or_and() {
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == (x = 0 \/ x = 1) /\ y = 2
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    assert_eq!(branches.len(), 2);

    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .unwrap()
        .unwrap();
    assert_eq!(states.len(), 2);
    // Verify actual state values — a count-only check would miss a bug that
    // produces 2 states with wrong x or y values (e.g., y=0 instead of y=2).
    let mut pairs: Vec<(i64, i64)> = states
        .iter()
        .map(|s| {
            let x = s
                .get("x")
                .and_then(tla_value::Value::as_i64)
                .expect("x should be int");
            let y = s
                .get("y")
                .and_then(tla_value::Value::as_i64)
                .expect("y should be int");
            (x, y)
        })
        .collect();
    pairs.sort_unstable();
    assert_eq!(pairs, vec![(0, 2), (1, 2)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_operator_inlining() {
    // Test that Init can refer to helper operators
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
TypeInit == x \in {0, 1} /\ y \in {10, 20}
Init == TypeInit /\ x = 0
====
"#;
    let (module, ctx, vars) = setup_module(src);

    let init_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Init" {
                    return Some(def);
                }
            }
            None
        })
        .unwrap();

    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
        .unwrap()
        .unwrap();

    // TypeInit gives x \in {0,1} and y \in {10,20}
    // But Init also requires x = 0
    // So x is intersected to {0}, giving 2 states: (0,10), (0,20)
    assert_eq!(states.len(), 2);

    // Verify all states have x = 0
    for state in &states {
        let x_val = state
            .vars()
            .find(|(n, _)| n.as_ref() == "x")
            .map(|(_, v)| v.clone());
        assert_eq!(x_val, Some(Value::int(0)));
    }
}
