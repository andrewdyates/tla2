// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for call-by-name substitution when an operator body primes one of its
//! formal parameters. Without the `expr_has_primed_param` check, these operators
//! would incorrectly use call-by-value, breaking state enumeration.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_top_level_apply_with_primed_param_uses_call_by_name() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE q, y

DropOne(seq) ==
  /\ \E i \in 1..Len(seq) :
       seq' = [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]
  /\ UNCHANGED y

Init == /\ q = <<1, 2>>
        /\ y = 0

Next == DropOne(q)
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
        .expect("invariant: Next operator must exist in test module");

    let init_state = State::from_pairs([
        ("q", Value::seq([Value::int(1), Value::int(2)])),
        ("y", Value::int(0)),
    ]);
    let successors = enumerate_successors(&mut ctx, &next_def, &init_state, &vars)
        .expect("enumerate should succeed");

    let mut q_values: Vec<Value> = successors
        .iter()
        .map(|state| state.get("q").cloned().expect("successor missing q"))
        .collect();
    q_values.sort();

    assert_eq!(
        q_values,
        vec![Value::seq([Value::int(1)]), Value::seq([Value::int(2)])],
        "top-level Apply must substitute state-level args when the operator primes its parameter"
    );
    assert!(
        successors
            .iter()
            .all(|state| state.get("y") == Some(&Value::int(0))),
        "UNCHANGED y should survive top-level Apply substitution"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conjunct_apply_with_primed_param_uses_call_by_name() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE q, y

DropOnly(seq) ==
  \E i \in 1..Len(seq) :
    seq' = [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Init == /\ q = <<1, 2>>
        /\ y = 0

Next == /\ DropOnly(q)
        /\ UNCHANGED y
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
        .expect("invariant: Next operator must exist in test module");

    let init_state = State::from_pairs([
        ("q", Value::seq([Value::int(1), Value::int(2)])),
        ("y", Value::int(0)),
    ]);
    let successors = enumerate_successors(&mut ctx, &next_def, &init_state, &vars)
        .expect("enumerate should succeed");

    let mut q_values: Vec<Value> = successors
        .iter()
        .map(|state| state.get("q").cloned().expect("successor missing q"))
        .collect();
    q_values.sort();

    assert_eq!(
        q_values,
        vec![Value::seq([Value::int(1)]), Value::seq([Value::int(2)])],
        "conjunct Apply must substitute state-level args when the operator primes its parameter"
    );
    assert!(
        successors
            .iter()
            .all(|state| state.get("y") == Some(&Value::int(0))),
        "UNCHANGED y should survive conjunct Apply substitution"
    );
}
