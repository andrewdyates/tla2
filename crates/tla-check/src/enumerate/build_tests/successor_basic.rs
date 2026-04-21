// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core `enumerate_successors` tests: primed assignments, UNCHANGED, disjunction,
//! set membership, existential quantifiers, and nested Exists accumulation.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_primed_assignments() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    // Set up current state
    let current_state = State::from_pairs([("x", Value::int(0))]);

    // Find Next definition
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

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars).unwrap();

    assert_eq!(successors.len(), 1);
    // x should be 1 in successor
    let succ_vars: Vec<_> = successors[0].vars().collect();
    assert_eq!(succ_vars.len(), 1);
    assert_eq!(succ_vars[0].1, &Value::int(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_unchanged() {
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ UNCHANGED y
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(5))]);

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

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars).unwrap();

    assert_eq!(successors.len(), 1);
    // Check x = 1, y = 5 (unchanged)
    for (name, value) in successors[0].vars() {
        if name.as_ref() == "x" {
            assert_eq!(value, &Value::int(1));
        } else if name.as_ref() == "y" {
            assert_eq!(value, &Value::int(5));
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_disjunction() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 \/ x' = x + 2
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0))]);

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

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars).unwrap();

    // Should have 2 successors: x=1 and x=2
    assert_eq!(successors.len(), 2);
    // Verify actual successor values — a count-only check would miss wrong
    // arithmetic (e.g., x+0 and x+0 producing two identical no-ops).
    let mut x_values: Vec<i64> = successors
        .iter()
        .filter_map(|s| s.get("x").and_then(tla_value::Value::as_i64))
        .collect();
    x_values.sort_unstable();
    assert_eq!(x_values, vec![1, 2]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_in_set() {
    // Test x' \in S where S is a set of possible values
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' \in {x + 1, x + 2, x + 3}
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0))]);

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

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars).unwrap();

    // Should have 3 successors: x=1, x=2, x=3
    assert_eq!(successors.len(), 3);

    // Collect successor x values
    let mut x_values: Vec<i64> = successors
        .iter()
        .filter_map(|s| {
            s.vars()
                .find(|(n, _)| n.as_ref() == "x")
                .and_then(|(_, v)| v.as_i64())
        })
        .collect();
    x_values.sort_unstable();
    assert_eq!(x_values, vec![1, 2, 3]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_in_set_with_unchanged() {
    // Test x' \in S combined with UNCHANGED y
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 10
Next == x' \in {x + 1, x + 2} /\ UNCHANGED y
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(10))]);

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

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars).unwrap();

    // Should have 2 successors
    assert_eq!(successors.len(), 2);

    // All successors should have y=10
    for succ in &successors {
        let y_val = succ
            .vars()
            .find(|(n, _)| n.as_ref() == "y")
            .map(|(_, v)| v.clone());
        assert_eq!(y_val, Some(Value::int(10)));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_multiple_in_set() {
    // Test both x' \in S and y' \in T (cartesian product)
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' \in {1, 2} /\ y' \in {10, 20}
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);

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

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars).unwrap();

    // Should have 2 * 2 = 4 successors (cartesian product)
    assert_eq!(successors.len(), 4);

    // Verify all combinations exist
    let mut combinations: Vec<(i64, i64)> = successors
        .iter()
        .map(|s| {
            let x: i64 = s
                .vars()
                .find(|(n, _)| n.as_ref() == "x")
                .and_then(|(_, v)| v.as_i64())
                .unwrap();
            let y: i64 = s
                .vars()
                .find(|(n, _)| n.as_ref() == "y")
                .and_then(|(_, v)| v.as_i64())
                .unwrap();
            (x, y)
        })
        .collect();
    combinations.sort_unstable();
    assert_eq!(combinations, vec![(1, 10), (1, 20), (2, 10), (2, 20)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_exists_in_conjunction() {
    // Regression: existential quantifiers inside conjunctions must be enumerated.
    // Pattern appears in PlusCal translations (e.g. ChangRoberts' n1(self)).
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = {}
Next == /\ x = 0
        /\ \E id \in {1, 2}:
             y' = y \cup {id}
        /\ x' = x
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::empty_set())]);

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

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars).unwrap();
    assert_eq!(successors.len(), 2);

    for succ in &successors {
        assert_eq!(succ.get("x").and_then(tla_value::Value::as_i64), Some(0));
    }

    let mut ys: Vec<Vec<i64>> = successors
        .iter()
        .map(|s| {
            let set = s.get("y").and_then(|v| v.as_set()).unwrap();
            let mut elems: Vec<i64> = set.iter().map(|v| v.as_i64().unwrap()).collect();
            elems.sort_unstable();
            elems
        })
        .collect();
    ys.sort();
    assert_eq!(ys, vec![vec![1], vec![2]]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inline_apply_with_exists_in_conjunction() {
    // Test the pattern from bcastFolklore: Op(x) /\ disjunction
    // where Op(x) contains \E inside its body
    // This should properly inline the operator to expose the Exists
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x, y

\* Operator that contains an existential quantifier
Receive(self) ==
  /\ \E val \in {1, 2}:
        /\ x' = val
        /\ y' = self

\* Step combines the operator with a disjunction
Step(self) ==
  /\ Receive(self)
  /\ TRUE

Init == x = 0 /\ y = 0

Next == \E self \in {10, 20}: Step(self)
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

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

    // Start from initial state
    let init_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);

    let successors = enumerate_successors(&mut ctx, &next_def, &init_state, &vars).unwrap();

    // Should find successors for:
    // - self=10, val=1 -> x'=1, y'=10
    // - self=10, val=2 -> x'=2, y'=10
    // - self=20, val=1 -> x'=1, y'=20
    // - self=20, val=2 -> x'=2, y'=20
    // Total: 4 successor states
    assert_eq!(
        successors.len(),
        4,
        "Expected 4 successor states from nested Exists in Apply. Got: {:?}",
        successors
    );
}

/// Regression test for #1280: Nested Exists over 3+ domain values must
/// accumulate ALL successors, not just from the last binding.
///
/// The bug was that `results.retain()` in the And handler of
/// `enumerate_unified` operated on ALL accumulated results (including
/// those from prior Exists iterations), filtering valid successors
/// whose hidden-prime validation doesn't match the current binding.
///
/// This test uses 3 outer Exists values to ensure the fix handles
/// arbitrary domain sizes, not just pairs.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_exists_apply_accumulates_all_successors_1280() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x, y

\* Operator with hidden primes (contains \E with primed assignments)
Choose(self) ==
  \E val \in {1, 2}: /\ x' = val /\ y' = self

Next == \E self \in {10, 20, 30}: /\ Choose(self) /\ TRUE
Init == x = 0 /\ y = 0
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
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

    let init_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);

    let successors = enumerate_successors(&mut ctx, &next_def, &init_state, &vars).unwrap();

    // 3 outer values × 2 inner values = 6 successors
    // Before fix: only 2 (last binding only); after fix: all 6
    assert_eq!(
        successors.len(),
        6,
        "Expected 6 successors (3 outer × 2 inner). Got {} — results.retain \
             may be filtering earlier Exists bindings. States: {:?}",
        successors.len(),
        successors
    );

    // Verify all 3 outer bindings are represented
    let y_values: std::collections::HashSet<i64> = successors
        .iter()
        .filter_map(|s| s.get("y").and_then(tla_value::Value::as_i64))
        .collect();
    assert_eq!(
        y_values,
        [10i64, 20, 30].into_iter().collect(),
        "All outer Exists bindings must produce successors"
    );
}
