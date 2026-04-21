// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evaluate_symbolic_assignments_conflict_detection() {
    // Two conflicting Value assignments for the same variable should
    // return an empty result (conflict = no valid successors).
    let ctx = EvalCtx::new();

    let assignments = vec![
        SymbolicAssignment::Value(Arc::from("x"), Value::int(1)),
        SymbolicAssignment::Value(Arc::from("x"), Value::int(2)),
    ];

    let result = evaluate_symbolic_assignments(&ctx, &assignments, None).unwrap();
    assert!(
        result.is_empty(),
        "conflicting assignments should produce empty result"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evaluate_symbolic_assignments_redundant_same_value() {
    // Two identical Value assignments for the same variable should NOT
    // conflict - the second is redundant but valid.
    let ctx = EvalCtx::new();

    let assignments = vec![
        SymbolicAssignment::Value(Arc::from("x"), Value::int(5)),
        SymbolicAssignment::Value(Arc::from("x"), Value::int(5)),
    ];

    let result = evaluate_symbolic_assignments(&ctx, &assignments, None).unwrap();
    assert_eq!(
        result.len(),
        1,
        "redundant same-value assignments should produce one result"
    );
    // Verify the content, not just the count — a value-corruption bug
    // would pass a length-only check.
    match &result[0] {
        crate::enumerate::PrimedAssignment::Assign(name, val) => {
            assert_eq!(name.as_ref(), "x");
            assert_eq!(*val, Value::int(5));
        }
        other => panic!("Expected Assign(x, 5), got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evaluate_symbolic_unchanged_produces_assign_with_current_value() {
    // Part of #3354: UNCHANGED x now produces PrimedAssignment::Assign(x, current)
    // instead of Unchanged. This ensures the diff builder sees the actual value,
    // which is required when current_values differs from the base ArrayState
    // (parallel worker split-array mode).
    let mut ctx = EvalCtx::new();
    ctx.bind_mut(Arc::from("x"), Value::int(10));

    let assignments = vec![SymbolicAssignment::Unchanged(Arc::from("x"))];

    let result = evaluate_symbolic_assignments(&ctx, &assignments, None).unwrap();
    assert_eq!(result.len(), 1);
    match &result[0] {
        crate::enumerate::PrimedAssignment::Assign(name, value) => {
            assert_eq!(name.as_ref(), "x");
            assert_eq!(*value, Value::int(10));
        }
        other => panic!("Expected Assign(x, 10), got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_symbolic_assignments_eq_prime() {
    // Integration test: parse a spec with x' = 42 and verify extraction
    // produces the correct SymbolicAssignment.
    let src = r#"
---- MODULE TestExtract ----
VARIABLE x

Init == x = 0
Next == x' = 42
====
"#;
    let (_module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    // Build the Next expression
    let next_expr = {
        use tla_core::{Span, Spanned};
        let span = Span::dummy();
        let x_prime = Spanned::new(
            Expr::Prime(Box::new(Spanned::new(
                Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
                span,
            ))),
            span,
        );
        let forty_two = Spanned::new(Expr::Int(42.into()), span);
        Spanned::new(Expr::Eq(Box::new(x_prime), Box::new(forty_two)), span)
    };

    let mut assignments = Vec::new();
    extract_symbolic_assignments(&ctx, &next_expr, &vars, &mut assignments).unwrap();

    assert_eq!(assignments.len(), 1, "should extract one assignment");
    match &assignments[0] {
        SymbolicAssignment::Value(name, val) => {
            assert_eq!(name.as_ref(), "x");
            assert_eq!(*val, Value::int(42));
        }
        other => panic!("Expected Value assignment, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_symbolic_assignments_unchanged() {
    // Integration test: UNCHANGED x should produce SymbolicAssignment::Unchanged
    let src = r#"
---- MODULE TestUnchanged ----
VARIABLE x

Init == x = 0
Next == UNCHANGED x
====
"#;
    let (_module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let next_expr = {
        use tla_core::{Span, Spanned};
        let span = Span::dummy();
        Spanned::new(
            Expr::Unchanged(Box::new(Spanned::new(
                Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
                span,
            ))),
            span,
        )
    };

    let mut assignments = Vec::new();
    extract_symbolic_assignments(&ctx, &next_expr, &vars, &mut assignments).unwrap();

    assert_eq!(assignments.len(), 1, "should extract one UNCHANGED");
    match &assignments[0] {
        SymbolicAssignment::Unchanged(name) => {
            assert_eq!(name.as_ref(), "x");
        }
        other => panic!("Expected Unchanged, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_symbolic_assignments_conjunction() {
    // Conjunction: x' = 1 /\ y' = 2 should extract two assignments.
    let src = r#"
---- MODULE TestConj ----
VARIABLE x, y

Init == x = 0 /\ y = 0
Next == x' = 1 /\ y' = 2
====
"#;
    let (_module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let next_expr = {
        use tla_core::{Span, Spanned};
        let span = Span::dummy();
        let x_prime = Spanned::new(
            Expr::Prime(Box::new(Spanned::new(
                Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
                span,
            ))),
            span,
        );
        let one = Spanned::new(Expr::Int(1.into()), span);
        let lhs = Spanned::new(Expr::Eq(Box::new(x_prime), Box::new(one)), span);

        let y_prime = Spanned::new(
            Expr::Prime(Box::new(Spanned::new(
                Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
                span,
            ))),
            span,
        );
        let two = Spanned::new(Expr::Int(2.into()), span);
        let rhs = Spanned::new(Expr::Eq(Box::new(y_prime), Box::new(two)), span);

        Spanned::new(Expr::And(Box::new(lhs), Box::new(rhs)), span)
    };

    let mut assignments = Vec::new();
    extract_symbolic_assignments(&ctx, &next_expr, &vars, &mut assignments).unwrap();

    assert_eq!(
        assignments.len(),
        2,
        "should extract two assignments from conjunction"
    );
    // Verify both names AND values — a value-swap bug (x=2, y=1) would
    // pass a name-only check but produce incorrect successor states.
    let mut found_x = false;
    let mut found_y = false;
    for a in &assignments {
        match a {
            SymbolicAssignment::Value(name, val) if name.as_ref() == "x" => {
                assert_eq!(*val, Value::int(1), "x should be assigned 1");
                found_x = true;
            }
            SymbolicAssignment::Value(name, val) if name.as_ref() == "y" => {
                assert_eq!(*val, Value::int(2), "y should be assigned 2");
                found_y = true;
            }
            other => panic!("Unexpected assignment: {:?}", other),
        }
    }
    assert!(found_x, "x assignment missing from conjunction extraction");
    assert!(found_y, "y assignment missing from conjunction extraction");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_extract_symbolic_assignments_unchanged_tuple() {
    // UNCHANGED <<x, y>> should produce two Unchanged assignments,
    // one per variable in the tuple. This is the common TLA+ idiom
    // for multi-variable UNCHANGED; the single-variable test above
    // only covers the simple case.
    let src = r#"
---- MODULE TestUnchangedTuple ----
VARIABLE x, y

Init == x = 0 /\ y = 0
Next == UNCHANGED <<x, y>>
====
"#;
    let (_module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let next_expr = {
        use tla_core::{Span, Spanned};
        let span = Span::dummy();
        let x_ident = Spanned::new(
            Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        );
        let y_ident = Spanned::new(
            Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        );
        Spanned::new(
            Expr::Unchanged(Box::new(Spanned::new(
                Expr::Tuple(vec![x_ident, y_ident]),
                span,
            ))),
            span,
        )
    };

    let mut assignments = Vec::new();
    extract_symbolic_assignments(&ctx, &next_expr, &vars, &mut assignments).unwrap();

    assert_eq!(
        assignments.len(),
        2,
        "UNCHANGED <<x, y>> should extract two assignments"
    );
    let mut found_x = false;
    let mut found_y = false;
    for a in &assignments {
        match a {
            SymbolicAssignment::Unchanged(name) if name.as_ref() == "x" => found_x = true,
            SymbolicAssignment::Unchanged(name) if name.as_ref() == "y" => found_y = true,
            other => panic!("Expected Unchanged, got {:?}", other),
        }
    }
    assert!(found_x, "x missing from UNCHANGED <<x, y>> extraction");
    assert!(found_y, "y missing from UNCHANGED <<x, y>> extraction");
}
