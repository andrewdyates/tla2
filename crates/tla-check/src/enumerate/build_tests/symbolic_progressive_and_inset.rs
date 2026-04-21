// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use tla_core::name_intern::NameId;

// ── Performance proof tests (Part of #2370, #1564) ───────────────────

/// Performance proof: progressive next_state correctness with many variables.
///
/// This test exercises the `evaluate_symbolic_assignments` hot path with N=20
/// variables where each variable depends on the previous one's primed value.
/// It verifies correctness of the progressive next_state context — that
/// `next_state.clone() + Arc::new()` on line 1306 of symbolic_assignments.rs
/// produces correct results through the full dependency chain.
///
/// The O(N²) cost of repeated HashMap clones (E3 in #2370) is a known
/// performance issue but the results MUST be correct. This test ensures
/// any future optimization (e.g., bind/unbind or incremental Arc) doesn't
/// break the progressive evaluation chain.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_progressive_next_state_many_variables_chain() {
    use tla_core::{Span, Spanned};

    let span = Span::dummy();

    // Build a chain: v0' = 100, v1' = v0' + 1, v2' = v1' + 1, ..., v19' = v18' + 1
    // Expected: v0 = 100, v1 = 101, v2 = 102, ..., v19 = 119
    let n = 20;
    let mut assignments = Vec::with_capacity(n);

    // v0' = 100 (base case — no primed dependency)
    assignments.push(SymbolicAssignment::Value(Arc::from("v0"), Value::int(100)));

    // v1..v19: each depends on previous variable's primed value
    for i in 1..n {
        let prev_name = format!("v{}", i - 1);
        let prev_prime = Spanned::new(
            Expr::Prime(Box::new(Spanned::new(
                Expr::Ident(prev_name, NameId::INVALID),
                span,
            ))),
            span,
        );
        let one = Spanned::new(Expr::Int(1.into()), span);
        let rhs = Spanned::new(Expr::Add(Box::new(prev_prime), Box::new(one)), span);
        assignments.push(SymbolicAssignment::Expr(
            Arc::from(format!("v{}", i).as_str()),
            rhs,
            Vec::new(),
        ));
    }

    // Set up context with current state (all zeros — shouldn't matter since
    // the chain is fully determined by v0' = 100)
    let mut ctx = EvalCtx::new();
    for i in 0..n {
        ctx.bind_mut(Arc::from(format!("v{}", i).as_str()), Value::int(0));
    }

    let result = evaluate_symbolic_assignments(&ctx, &assignments, None).unwrap();

    // All 20 assignments should evaluate successfully
    assert_eq!(
        result.len(),
        n,
        "all {} assignments should produce results",
        n
    );

    // Verify the chain: v0=100, v1=101, ..., v19=119
    for (i, assign) in result.iter().enumerate() {
        match assign {
            crate::enumerate::PrimedAssignment::Assign(name, val) => {
                let expected = 100 + i as i64;
                assert_eq!(
                    val.as_i64(),
                    Some(expected),
                    "v{} should be {} (progressive chain), got {:?}",
                    name,
                    expected,
                    val
                );
            }
            crate::enumerate::PrimedAssignment::Unchanged(name) => {
                panic!("v{}: expected Assign, got Unchanged", name);
            }
            other => {
                panic!("v{}: unexpected assignment type: {:?}", i, other);
            }
        }
    }
}

/// Performance proof: topological sort handles reverse-ordered chains correctly.
///
/// When all N assignments are in reverse dependency order (worst case for
/// topological sort), Kahn's algorithm must reorder them all. This exercises
/// the O(V+E) Kahn implementation in `topological_sort_assignments` and
/// verifies it doesn't degrade for large N.
///
/// Related: #1564 (topo sort allocates 7+ collections per-state).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_topological_sort_many_variables_reverse_chain() {
    use tla_core::{Span, Spanned};

    let span = Span::dummy();
    let n = 15;

    // Build assignments in REVERSE order: v14' = v13'+1, ..., v1' = v0'+1, v0' = 1
    // Correct order after sort: v0, v1, ..., v14
    let mut assignments = Vec::with_capacity(n);

    for i in (1..n).rev() {
        let prev_name = format!("v{}", i - 1);
        let prev_prime = Spanned::new(
            Expr::Prime(Box::new(Spanned::new(
                Expr::Ident(prev_name, NameId::INVALID),
                span,
            ))),
            span,
        );
        let one = Spanned::new(Expr::Int(1.into()), span);
        let rhs = Spanned::new(Expr::Add(Box::new(prev_prime), Box::new(one)), span);
        assignments.push(SymbolicAssignment::Expr(
            Arc::from(format!("v{}", i).as_str()),
            rhs,
            Vec::new(),
        ));
    }
    // v0' = 1 (no dependency) — added LAST (worst case position)
    let v0_rhs = Spanned::new(Expr::Int(1.into()), span);
    assignments.push(SymbolicAssignment::Expr(
        Arc::from("v0"),
        v0_rhs,
        Vec::new(),
    ));

    let sorted = topological_sort_assignments(None, &assignments);
    assert_eq!(sorted.len(), n);

    // After sort: v0 must come first, then v1, ..., v14
    let names: Vec<String> = sorted
        .iter()
        .map(|s| match s {
            SymbolicAssignment::Expr(name, _, _) => name.to_string(),
            SymbolicAssignment::Value(name, _) => name.to_string(),
            _ => panic!("unexpected variant"),
        })
        .collect();

    for (i, name) in names.iter().enumerate().take(n) {
        assert_eq!(
            name,
            &format!("v{}", i),
            "position {} should be v{}, got {}",
            i,
            i,
            name
        );
    }
}

/// Performance proof: evaluate_symbolic_assignments InSet constraint intersection.
///
/// Verifies that when two InSet constraints on the same variable intersect,
/// the result correctly contains only the common elements. This exercises
/// the HashSet-based intersection (fix for E1 in #2370, line 1220-1223).
///
/// Prior to the fix, this was O(n*m); now it should be O(n+m).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evaluate_symbolic_inset_intersection_correctness() {
    use tla_core::{Span, Spanned};

    let span = Span::dummy();
    let ctx = EvalCtx::new();

    // Two InSet assignments for the same variable with overlapping domains:
    // x' \in {1, 2, 3, 4, 5}
    // x' \in {3, 4, 5, 6, 7}
    // Expected: x' \in {3, 4, 5} (intersection)
    let set1 = Spanned::new(
        Expr::SetEnum(vec![
            Spanned::new(Expr::Int(1.into()), span),
            Spanned::new(Expr::Int(2.into()), span),
            Spanned::new(Expr::Int(3.into()), span),
            Spanned::new(Expr::Int(4.into()), span),
            Spanned::new(Expr::Int(5.into()), span),
        ]),
        span,
    );
    let set2 = Spanned::new(
        Expr::SetEnum(vec![
            Spanned::new(Expr::Int(3.into()), span),
            Spanned::new(Expr::Int(4.into()), span),
            Spanned::new(Expr::Int(5.into()), span),
            Spanned::new(Expr::Int(6.into()), span),
            Spanned::new(Expr::Int(7.into()), span),
        ]),
        span,
    );

    let assignments = vec![
        SymbolicAssignment::InSet(Arc::from("x"), set1, Vec::new()),
        SymbolicAssignment::InSet(Arc::from("x"), set2, Vec::new()),
    ];

    let result = evaluate_symbolic_assignments(&ctx, &assignments, None).unwrap();
    assert_eq!(
        result.len(),
        1,
        "intersected InSet should produce one result"
    );

    match &result[0] {
        crate::enumerate::PrimedAssignment::InSet(name, values) => {
            assert_eq!(name.as_ref(), "x");
            // Intersection should contain exactly {3, 4, 5}
            assert_eq!(
                values.len(),
                3,
                "intersection of {{1..5}} and {{3..7}} should be {{3,4,5}}, got {:?}",
                values
            );
            let int_vals: Vec<i64> = values.iter().filter_map(tla_value::Value::as_i64).collect();
            assert!(int_vals.contains(&3), "intersection should contain 3");
            assert!(int_vals.contains(&4), "intersection should contain 4");
            assert!(int_vals.contains(&5), "intersection should contain 5");
        }
        other => panic!("Expected InSet result, got {:?}", other),
    }
}

/// Performance proof: conflict detection between Value and InSet constraints.
///
/// When a variable has a specific Value assignment AND an InSet constraint,
/// the Value must be in the InSet or it's a conflict (empty result).
/// Tests both the compatible and incompatible cases.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evaluate_symbolic_value_inset_conflict() {
    use tla_core::{Span, Spanned};

    let span = Span::dummy();
    let ctx = EvalCtx::new();

    // Case 1: Value x' = 3, then InSet x' \in {1, 2, 3} — compatible
    let set_expr = Spanned::new(
        Expr::SetEnum(vec![
            Spanned::new(Expr::Int(1.into()), span),
            Spanned::new(Expr::Int(2.into()), span),
            Spanned::new(Expr::Int(3.into()), span),
        ]),
        span,
    );
    let assignments_compat = vec![
        SymbolicAssignment::Value(Arc::from("x"), Value::int(3)),
        SymbolicAssignment::InSet(Arc::from("x"), set_expr.clone(), Vec::new()),
    ];
    let result = evaluate_symbolic_assignments(&ctx, &assignments_compat, None).unwrap();
    assert_eq!(
        result.len(),
        1,
        "Value(3) + InSet({{1,2,3}}) should be compatible"
    );

    // Case 2: Value x' = 99, then InSet x' \in {1, 2, 3} — conflict
    let assignments_conflict = vec![
        SymbolicAssignment::Value(Arc::from("x"), Value::int(99)),
        SymbolicAssignment::InSet(Arc::from("x"), set_expr, Vec::new()),
    ];
    let result = evaluate_symbolic_assignments(&ctx, &assignments_conflict, None).unwrap();
    assert!(
        result.is_empty(),
        "Value(99) + InSet({{1,2,3}}) should conflict (empty result)"
    );
}

// ── Property-based tests (Part of #2370, #1564) ──────────────────────

proptest::proptest! {
    /// Property: progressive next_state evaluation is correct for arbitrary chain
    /// lengths. Each variable v_i depends on v_{i-1}', forming a chain where
    /// v0' = BASE, v1' = v0' + 1, ..., v_n' = v_{n-1}' + 1.
    ///
    /// Expected result: v_i = BASE + i for all i.
    ///
    /// This exercises the O(N^2) HashMap clone path in evaluate_symbolic_assignments
    /// (next_state.clone() per variable, E3 in #2370) and verifies correctness
    /// holds across varying N. The O(N^2) cost is the known performance issue;
    /// this test ensures correctness regardless of chain length.
    #[test]
    fn prop_progressive_chain_correctness(n in 2usize..50, base in 0i64..1000) {
        use tla_core::{Span, Spanned};

        let span = Span::dummy();
        let mut assignments = Vec::with_capacity(n);

        // v0' = base (no dependency)
        assignments.push(SymbolicAssignment::Value(Arc::from("v0"), Value::int(base)));

        // v1..v_{n-1}: each depends on previous variable's primed value
        for i in 1..n {
            let prev_name = format!("v{}", i - 1);
            let prev_prime = Spanned::new(
                Expr::Prime(Box::new(Spanned::new(Expr::Ident(prev_name, NameId::INVALID), span))),
                span,
            );
            let one = Spanned::new(Expr::Int(1.into()), span);
            let rhs = Spanned::new(Expr::Add(Box::new(prev_prime), Box::new(one)), span);
            assignments.push(SymbolicAssignment::Expr(
                Arc::from(format!("v{}", i).as_str()),
                rhs,
                Vec::new(),
            ));
        }

        // Context with current state (all zeros — chain is fully determined by v0'=base)
        let mut ctx = EvalCtx::new();
        for i in 0..n {
            ctx.bind_mut(Arc::from(format!("v{}", i).as_str()), Value::int(0));
        }

        let result = evaluate_symbolic_assignments(&ctx, &assignments, None).unwrap();
        proptest::prop_assert_eq!(result.len(), n, "all {} assignments should produce results", n);

        for (i, assign) in result.iter().enumerate() {
            match assign {
                crate::enumerate::PrimedAssignment::Assign(name, val) => {
                    let expected = base + i as i64;
                    proptest::prop_assert_eq!(
                        val.as_i64(),
                        Some(expected),
                        "{} should be {} (chain with base={})",
                        name, expected, base
                    );
                }
                crate::enumerate::PrimedAssignment::Unchanged(name) => {
                    proptest::prop_assert!(false, "{}: expected Assign, got Unchanged", name);
                }
                other => {
                    proptest::prop_assert!(false, "unexpected variant: {:?}", other);
                }
            }
        }
    }

    /// Property: topological sort produces correct ordering for reverse-ordered chains
    /// of arbitrary length. Verifies O(V+E) Kahn's algorithm against arbitrary N.
    #[test]
    fn prop_topological_sort_reverse_chain(n in 2usize..50) {
        use tla_core::{Span, Spanned};

        let span = Span::dummy();
        let mut assignments = Vec::with_capacity(n);

        // Build assignments in REVERSE order: v_{n-1}' = v_{n-2}'+1, ..., v0' = 1
        for i in (1..n).rev() {
            let prev_name = format!("v{}", i - 1);
            let prev_prime = Spanned::new(
                Expr::Prime(Box::new(Spanned::new(Expr::Ident(prev_name, NameId::INVALID), span))),
                span,
            );
            let one = Spanned::new(Expr::Int(1.into()), span);
            let rhs = Spanned::new(Expr::Add(Box::new(prev_prime), Box::new(one)), span);
            assignments.push(SymbolicAssignment::Expr(
                Arc::from(format!("v{}", i).as_str()),
                rhs,
                Vec::new(),
            ));
        }
        // v0' = 1 (base) — added LAST for worst-case input ordering
        let v0_rhs = Spanned::new(Expr::Int(1.into()), span);
        assignments.push(SymbolicAssignment::Expr(
            Arc::from("v0"),
            v0_rhs,
            Vec::new(),
        ));

        let sorted = topological_sort_assignments(None, &assignments);
        proptest::prop_assert_eq!(sorted.len(), n);

        // After sort: v0 must come first, then v1, ..., v_{n-1}
        let names: Vec<String> = sorted
            .iter()
            .map(|s| match s {
                SymbolicAssignment::Expr(name, _, _) => name.to_string(),
                SymbolicAssignment::Value(name, _) => name.to_string(),
                _ => panic!("unexpected variant"),
            })
            .collect();

        for (i, name) in names.iter().enumerate().take(n) {
            proptest::prop_assert_eq!(
                name,
                &format!("v{}", i),
                "position {} should be v{}, got {}",
                i, i, name
            );
        }
    }
}
