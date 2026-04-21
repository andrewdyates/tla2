// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_if_then_else_constant_condition() {
    // IF-THEN-ELSE with a condition that evaluates to a constant
    let src = r#"
---- MODULE Test ----
VARIABLE x
Enabled == TRUE
Init == IF Enabled THEN x = 1 ELSE x = 0
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

    // Enabled is TRUE, so we take the THEN branch: x = 1
    assert_eq!(states.len(), 1);
    assert_eq!(states[0].get("x"), Some(&Value::int(1)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_if_then_else_false_condition() {
    // IF-THEN-ELSE with FALSE condition
    let src = r#"
---- MODULE Test ----
VARIABLE x
Disabled == FALSE
Init == IF Disabled THEN x = 1 ELSE x = 0
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

    // Disabled is FALSE, so we take the ELSE branch: x = 0
    assert_eq!(states.len(), 1);
    assert_eq!(states[0].get("x"), Some(&Value::int(0)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_if_then_else_with_constraint_condition() {
    // IF-THEN-ELSE where condition is a constraint on a variable
    // Init == x \in {0, 1} /\ IF x = 0 THEN y = 10 ELSE y = 20
    // This should expand to: (x = 0 /\ y = 10) \/ (x \in {0,1} /\ y = 20)
    // After intersection: (x = 0, y = 10) \/ (x \in {0,1}, y = 20)
    // which gives states: (0, 10), (0, 20), (1, 20)
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x \in {0, 1} /\ IF x = 0 THEN y = 10 ELSE y = 20
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

    // With proper negation support, we get:
    // - Branch from condition x=0 + then y=10: (x=0 ∩ {0,1}, y=10) => (0, 10)
    // - Branch from ~condition x/=0 + else y=20: (x∈{0,1} ∩ x/=0, y=20) => (1, 20)
    // So exactly 2 states: (0, 10) and (1, 20)
    assert_eq!(states.len(), 2);

    // Verify the states
    let mut state_pairs: Vec<(i64, i64)> = states
        .iter()
        .map(|s| {
            let x: i64 = s.get("x").and_then(tla_value::Value::as_i64).unwrap();
            let y: i64 = s.get("y").and_then(tla_value::Value::as_i64).unwrap();
            (x, y)
        })
        .collect();
    state_pairs.sort_unstable();
    assert_eq!(state_pairs, vec![(0, 10), (1, 20)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_nested_if_then_else() {
    // Nested IF-THEN-ELSE with constant conditions
    let src = r#"
---- MODULE Test ----
VARIABLE x
A == TRUE
B == FALSE
Init == IF A THEN (IF B THEN x = 1 ELSE x = 2) ELSE x = 3
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

    // A is TRUE, so we enter IF B THEN x=1 ELSE x=2
    // B is FALSE, so we get x = 2
    assert_eq!(states.len(), 1);
    assert_eq!(states[0].get("x"), Some(&Value::int(2)));
}
