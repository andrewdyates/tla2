// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_if_with_operator_reference() {
    // Regression test for #89: IF condition with operator reference containing primed vars
    //
    // Pattern:
    //   ActionX == x < 1 /\ x' = x + 1
    //   TNext == y' = IF ActionX THEN 5 ELSE y
    //   Next == (ActionX \/ UNCHANGED x) /\ TNext
    //
    // The fix ensures that when evaluating y' = IF ActionX THEN 5 ELSE y,
    // the topological sort correctly identifies that y' depends on x' (via ActionX).
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x, y

Init == x = 0 /\ y = 0

ActionX == x < 1 /\ x' = x + 1
TNext == y' = IF ActionX THEN 5 ELSE y

Next == /\ (ActionX \/ UNCHANGED x)
        /\ TNext
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);

    // Bind current state to context
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

    let successors = enumerate_successors(&mut ctx, &next_def, &current_state, &vars).unwrap();

    // Should have 2 successors:
    // 1. {x=1, y=5} - ActionX taken, so y' = IF TRUE THEN 5 = 5
    // 2. {x=0, y=0} - UNCHANGED x, so y' = IF FALSE THEN 5 ELSE y = y = 0 (stuttering)
    assert_eq!(
        successors.len(),
        2,
        "Expected 2 successors (ActionX branch + UNCHANGED branch)"
    );

    // Check that we found {x=1, y=5}
    let action_x_state = successors
        .iter()
        .find(|s| {
            s.vars()
                .find(|(n, _)| n.as_ref() == "x")
                .map(|(_, v)| v.as_i64())
                == Some(Some(1))
        })
        .expect("Should find ActionX branch successor");
    let y_val = action_x_state
        .vars()
        .find(|(n, _)| n.as_ref() == "y")
        .map(|(_, v)| v.as_i64())
        .expect("Should have y value");
    assert_eq!(
        y_val,
        Some(5),
        "ActionX branch: y should be 5 (from IF TRUE)"
    );

    // Check that we found {x=0, y=0}
    let unchanged_state = successors
        .iter()
        .find(|s| {
            s.vars()
                .find(|(n, _)| n.as_ref() == "x")
                .map(|(_, v)| v.as_i64())
                == Some(Some(0))
        })
        .expect("Should find UNCHANGED branch successor");
    let y_val = unchanged_state
        .vars()
        .find(|(n, _)| n.as_ref() == "y")
        .map(|(_, v)| v.as_i64())
        .expect("Should have y value");
    assert_eq!(
        y_val,
        Some(0),
        "UNCHANGED branch: y should be 0 (from IF FALSE)"
    );
}

// ── symbolic_assignments unit tests (Part of #1214) ──────────────────

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_topological_sort_assignments_cycle_fallback() {
    // Test: mutual dependency (x' depends on y', y' depends on x')
    // should fall back to original order since Kahn's can't complete.
    use tla_core::{Span, Spanned};

    let span = Span::dummy();

    // x' = y' + 1 (depends on y')
    let y_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let one1 = Spanned::new(Expr::Int(1.into()), span);
    let x_rhs = Spanned::new(Expr::Add(Box::new(y_prime), Box::new(one1)), span);

    // y' = x' + 1 (depends on x')
    let x_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let one2 = Spanned::new(Expr::Int(1.into()), span);
    let y_rhs = Spanned::new(Expr::Add(Box::new(x_prime), Box::new(one2)), span);

    let assignments = vec![
        SymbolicAssignment::Expr(Arc::from("x"), x_rhs, Vec::new()),
        SymbolicAssignment::Expr(Arc::from("y"), y_rhs, Vec::new()),
    ];

    let sorted = topological_sort_assignments(None, &assignments);
    assert_eq!(sorted.len(), 2);

    // Cycle detected → original order preserved: x, y
    let names: Vec<&str> = sorted
        .iter()
        .map(|s| match s {
            SymbolicAssignment::Expr(name, _, _) => name.as_ref(),
            _ => panic!("Expected Expr"),
        })
        .collect();
    assert_eq!(
        names,
        vec!["x", "y"],
        "cycle should preserve original order"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_topological_sort_assignments_empty() {
    let sorted = topological_sort_assignments(None, &[]);
    assert!(sorted.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_topological_sort_assignments_single() {
    // Single assignment: should be returned as-is.
    let assignments = vec![SymbolicAssignment::Value(Arc::from("x"), Value::int(42))];
    let sorted = topological_sort_assignments(None, &assignments);
    assert_eq!(sorted.len(), 1);
    match &sorted[0] {
        SymbolicAssignment::Value(name, v) => {
            assert_eq!(name.as_ref(), "x");
            assert_eq!(*v, Value::int(42));
        }
        _ => panic!("Expected Value assignment"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_topological_sort_assignments_unchanged_no_deps() {
    // UNCHANGED assignments have no primed references, so they should
    // remain in their original relative order regardless of other deps.
    let assignments = vec![
        SymbolicAssignment::Unchanged(Arc::from("a")),
        SymbolicAssignment::Value(Arc::from("b"), Value::int(1)),
        SymbolicAssignment::Unchanged(Arc::from("c")),
    ];
    let sorted = topological_sort_assignments(None, &assignments);
    let names: Vec<&str> = sorted
        .iter()
        .map(|s| match s {
            SymbolicAssignment::Unchanged(n) => n.as_ref(),
            SymbolicAssignment::Value(n, _) => n.as_ref(),
            _ => panic!("unexpected variant"),
        })
        .collect();
    assert_eq!(names, vec!["a", "b", "c"]);
}
