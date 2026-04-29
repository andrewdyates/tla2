// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Regression tests for #62: Topological sort of symbolic assignments
// ========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_primed_var_refs_simple() {
    // Test: x' references nothing (it's a definition, not a reference)
    // Test: expr referencing count' should return {"count"}
    use tla_core::{Span, Spanned};

    let span = Span::dummy();

    // Simple expression: count' (this is a Prime wrapping an Ident)
    let count_prime = Expr::Prime(Box::new(Spanned::new(
        Expr::Ident("count".to_string(), tla_core::name_intern::NameId::INVALID),
        span,
    )));
    let refs = get_primed_var_refs(&count_prime);
    assert_eq!(refs.len(), 1);
    assert!(refs.contains(&Arc::from("count")));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_primed_var_refs_complex_expr() {
    // Test: announced' = (count' >= VT) should reference count'
    // The expression `count' >= VT` contains a primed reference
    use tla_core::{Span, Spanned};

    let span = Span::dummy();

    // Build: count' >= VT (a Geq expression)
    let count_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("count".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let vt = Spanned::new(
        Expr::Ident("VT".to_string(), tla_core::name_intern::NameId::INVALID),
        span,
    );
    let geq_expr = Expr::Geq(Box::new(count_prime), Box::new(vt));

    let refs = get_primed_var_refs(&geq_expr);
    assert_eq!(refs.len(), 1);
    assert!(refs.contains(&Arc::from("count")));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_primed_var_refs_multiple() {
    // Test: x' + y' should return {"x", "y"}
    use tla_core::{Span, Spanned};

    let span = Span::dummy();

    let x_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let y_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    // Build x' + y' as an Add expression
    let add_expr = Expr::Add(Box::new(x_prime), Box::new(y_prime));

    let refs = get_primed_var_refs(&add_expr);
    assert_eq!(refs.len(), 2);
    assert!(refs.contains(&Arc::from("x")));
    assert!(refs.contains(&Arc::from("y")));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_primed_var_refs_no_primes() {
    // Test: x + y (no primes) should return empty set
    use tla_core::{Span, Spanned};

    let span = Span::dummy();

    let x = Spanned::new(
        Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        span,
    );
    let y = Spanned::new(
        Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
        span,
    );
    let add_expr = Expr::Add(Box::new(x), Box::new(y));

    let refs = get_primed_var_refs(&add_expr);
    assert!(refs.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_topological_sort_assignments_independent() {
    // Test: independent assignments should remain in original order
    // x' = 1, y' = 2 -> no dependencies, order preserved
    let assignments = vec![
        SymbolicAssignment::Value(Arc::from("x"), Value::int(1)),
        SymbolicAssignment::Value(Arc::from("y"), Value::int(2)),
    ];

    let sorted = topological_sort_assignments(None, &assignments);
    assert_eq!(sorted.len(), 2);

    // Order should be preserved for independent assignments
    match &sorted[0] {
        SymbolicAssignment::Value(name, _) => assert_eq!(name.as_ref(), "x"),
        _ => panic!("Expected Value assignment"),
    }
    match &sorted[1] {
        SymbolicAssignment::Value(name, _) => assert_eq!(name.as_ref(), "y"),
        _ => panic!("Expected Value assignment"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_topological_sort_assignments_dependency() {
    // Regression test for #62: Prisoner spec bug
    // announced' = (count' >= VT) depends on count'
    // count' = count + 1 defines count'
    // The sort should put count' definition BEFORE announced' definition
    use tla_core::{Span, Spanned};

    let span = Span::dummy();

    // Build: announced' = (count' >= 3)
    // This references count' in its RHS
    let count_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("count".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let three = Spanned::new(Expr::Int(3.into()), span);
    let announced_rhs = Spanned::new(Expr::Geq(Box::new(count_prime), Box::new(three)), span);

    // Build: count' = count + 1
    // This does NOT reference any primed vars
    let count = Spanned::new(
        Expr::Ident("count".to_string(), tla_core::name_intern::NameId::INVALID),
        span,
    );
    let one = Spanned::new(Expr::Int(1.into()), span);
    let count_rhs = Spanned::new(Expr::Add(Box::new(count), Box::new(one)), span);

    // Put them in WRONG order (announced before count)
    // This was the bug: document order had announced first
    let assignments = vec![
        SymbolicAssignment::Expr(Arc::from("announced"), announced_rhs, Vec::new()),
        SymbolicAssignment::Expr(Arc::from("count"), count_rhs, Vec::new()),
    ];

    let sorted = topological_sort_assignments(None, &assignments);
    assert_eq!(sorted.len(), 2);

    // After sort: count should come FIRST because announced depends on count'
    match &sorted[0] {
        SymbolicAssignment::Expr(name, _, _) => {
            assert_eq!(name.as_ref(), "count", "count' should be defined first");
        }
        _ => panic!("Expected Expr assignment"),
    }
    match &sorted[1] {
        SymbolicAssignment::Expr(name, _, _) => {
            assert_eq!(
                name.as_ref(),
                "announced",
                "announced' should be defined second"
            );
        }
        _ => panic!("Expected Expr assignment"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_topological_sort_assignments_chain() {
    // Test: x' depends on y', y' depends on z'
    // z' = 1, y' = z' + 1, x' = y' + 1
    // Correct order: z, y, x
    use tla_core::{Span, Spanned};

    let span = Span::dummy();

    // z' = 1 (no dependencies)
    let z_rhs = Spanned::new(Expr::Int(1.into()), span);

    // y' = z' + 1 (depends on z')
    let z_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("z".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let one1 = Spanned::new(Expr::Int(1.into()), span);
    let y_rhs = Spanned::new(Expr::Add(Box::new(z_prime), Box::new(one1)), span);

    // x' = y' + 1 (depends on y')
    let y_prime = Spanned::new(
        Expr::Prime(Box::new(Spanned::new(
            Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
            span,
        ))),
        span,
    );
    let one2 = Spanned::new(Expr::Int(1.into()), span);
    let x_rhs = Spanned::new(Expr::Add(Box::new(y_prime), Box::new(one2)), span);

    // Put in reverse order (x, y, z) - wrong order
    let assignments = vec![
        SymbolicAssignment::Expr(Arc::from("x"), x_rhs, Vec::new()),
        SymbolicAssignment::Expr(Arc::from("y"), y_rhs, Vec::new()),
        SymbolicAssignment::Expr(Arc::from("z"), z_rhs, Vec::new()),
    ];

    let sorted = topological_sort_assignments(None, &assignments);
    assert_eq!(sorted.len(), 3);

    // After sort: z, y, x
    let names: Vec<&str> = sorted
        .iter()
        .map(|s| match s {
            SymbolicAssignment::Expr(name, _, _) => name.as_ref(),
            _ => panic!("Expected Expr"),
        })
        .collect();
    assert_eq!(names, vec!["z", "y", "x"]);
}
