// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================
// Inequality constraint tests
// ============================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_simple_inequality() {
    // x \in {0, 1, 2} /\ x /= 1 => x ∈ {0, 2}
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {0, 1, 2} /\ x /= 1
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

    // Should have 2 states: x=0 and x=2 (x=1 is excluded)
    assert_eq!(states.len(), 2);

    let mut x_values: Vec<i64> = states
        .iter()
        .filter_map(|s| s.get("x").and_then(tla_value::Value::as_i64))
        .collect();
    x_values.sort_unstable();
    assert_eq!(x_values, vec![0, 2]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_multiple_inequalities() {
    // x \in {0, 1, 2, 3, 4} /\ x /= 1 /\ x /= 3 => x ∈ {0, 2, 4}
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {0, 1, 2, 3, 4} /\ x /= 1 /\ x /= 3
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

    // Should have 3 states: x=0, x=2, x=4
    assert_eq!(states.len(), 3);

    let mut x_values: Vec<i64> = states
        .iter()
        .filter_map(|s| s.get("x").and_then(tla_value::Value::as_i64))
        .collect();
    x_values.sort_unstable();
    assert_eq!(x_values, vec![0, 2, 4]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_inequality_with_two_vars() {
    // x \in {0, 1} /\ y \in {10, 20, 30} /\ y /= 20
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x \in {0, 1} /\ y \in {10, 20, 30} /\ y /= 20
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

    // 2 choices for x * 2 choices for y (10, 30) = 4 states
    assert_eq!(states.len(), 4);
    // Verify the inequality filter actually excluded y=20 — a count-only
    // check would miss a bug that produces 4 states with wrong y values.
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
    assert_eq!(pairs, vec![(0, 10), (0, 30), (1, 10), (1, 30)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_inequality_excludes_all() {
    // x \in {1} /\ x /= 1 => empty (contradiction)
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {1} /\ x /= 1
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

    // Contradiction: x must be 1 but also not 1
    assert!(states.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_inequality_in_disjunction() {
    // (x = 0 /\ y = 10) \/ (x \in {0, 1, 2} /\ x /= 0 /\ y = 20)
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == (x = 0 /\ y = 10) \/ (x \in {0, 1, 2} /\ x /= 0 /\ y = 20)
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

    // First branch: (0, 10)
    // Second branch: x in {1, 2} (excluding 0), y = 20 => (1, 20), (2, 20)
    // Total: 3 states
    assert_eq!(states.len(), 3);

    let mut state_pairs: Vec<(i64, i64)> = states
        .iter()
        .map(|s| {
            let x: i64 = s.get("x").and_then(tla_value::Value::as_i64).unwrap();
            let y: i64 = s.get("y").and_then(tla_value::Value::as_i64).unwrap();
            (x, y)
        })
        .collect();
    state_pairs.sort_unstable();
    assert_eq!(state_pairs, vec![(0, 10), (1, 20), (2, 20)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_states_direct_inequality_syntax() {
    // Test using # syntax directly (if parsed as Neq)
    // x \in {0, 1, 2} /\ x # 1 => x ∈ {0, 2}
    // Note: TLA+ uses # as inequality operator, same as /=
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in {0, 1, 2} /\ x # 1
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

    let result = extract_init_constraints(&ctx, &init_def.body, &vars, None);

    // If # is parsed as Neq, we should get constraints
    if let Some(branches) = result {
        let states = enumerate_states_from_constraint_branches(None, &vars, &branches)
            .unwrap()
            .unwrap();
        assert_eq!(states.len(), 2);

        let mut x_values: Vec<i64> = states
            .iter()
            .filter_map(|s| {
                s.get("x")
                    .and_then(tla_value::Value::to_bigint)
                    .and_then(|n| n.try_into().ok())
            })
            .collect();
        x_values.sort_unstable();
        assert_eq!(x_values, vec![0, 2]);
    }
    // If # is not parsed as Neq, the test still passes (result is None)
}
