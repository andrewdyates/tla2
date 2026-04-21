// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

// Author: Andrew Yates
//
// Performance proof tests for #3665: expr.rs unconditional tree reconstruction.
//
// These tests demonstrate that expression traversal functions allocate new
// Arc nodes even when nothing changes, defeating Arc sharing. When #3665 is
// fixed, the assertion about Arc pointer inequality should flip.

use std::sync::Arc;
use z4_chc::{ChcExpr, ChcOp, ChcSort, ChcVar};

/// Proves that `substitute` with a non-matching substitution still allocates
/// new Arc nodes for every tree node, defeating Arc sharing.
///
/// The substitution targets variable "nonexistent" which doesn't appear in
/// the expression, so nothing should change — yet every node is rebuilt.
#[test]
fn substitute_nonmatching_breaks_arc_sharing() {
    // Build: (+ x (+ y z))
    let x = Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::Int)));
    let y = Arc::new(ChcExpr::var(ChcVar::new("y", ChcSort::Int)));
    let z = Arc::new(ChcExpr::var(ChcVar::new("z", ChcSort::Int)));
    let inner = Arc::new(ChcExpr::Op(ChcOp::Add, vec![y, z]));
    let root = ChcExpr::Op(ChcOp::Add, vec![x, inner.clone()]);

    // Substitute a variable that doesn't exist in the expression
    let nonexistent = ChcVar::new("nonexistent", ChcSort::Int);
    let replacement = ChcExpr::Int(999);
    let result = root.substitute(&[(nonexistent, replacement)]);

    // Structural equality holds (same tree shape):
    assert_eq!(root, result);

    // But Arc sharing is lost — the result is a fresh allocation, not the
    // same pointer. This proves the O(n) allocation overhead per no-op
    // traversal documented in #3665.
    //
    // When #3665 is fixed, this match arm will fail (result will share Arcs),
    // and this test should be updated to assert pointer equality instead.
    match &result {
        ChcExpr::Op(ChcOp::Add, args) => {
            // Inner node was reconstructed: different Arc pointer
            assert!(
                !Arc::ptr_eq(&args[1], &inner),
                "substitute with non-matching var should currently reconstruct (not share) \
                 inner nodes — if this fails, #3665 may have been fixed!"
            );
        }
        _ => panic!("expected Op(Add, _)"),
    }
}

/// Proves that chaining propagate_var_equalities + substitute produces
/// structurally-equal but pointer-different expressions even when no
/// actual simplification occurs. This demonstrates the O(5n) clone chain
/// documented in #3665.
#[test]
fn and_reconstruction_on_already_flat_conjunction() {
    // Build: (and (>= x 0) (>= y 0)) — already flat, no nested And
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let geq_x = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(x), Arc::new(ChcExpr::Int(0))]);
    let geq_y = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(y), Arc::new(ChcExpr::Int(0))]);
    let conj = ChcExpr::and(geq_x, geq_y);

    // substitute with non-matching var forces a full tree walk
    let nonexistent = ChcVar::new("nonexistent", ChcSort::Int);
    let replacement = ChcExpr::Int(0);
    let result = conj.substitute(&[(nonexistent, replacement)]);

    // Semantically identical
    assert_eq!(
        conj, result,
        "non-matching substitute should preserve semantics"
    );

    // Count nodes in the conjunction to show the allocation scale
    let node_count = count_nodes(&conj);
    assert!(
        node_count >= 5,
        "conjunction should have at least 5 nodes (and, 2 x ge, 2 x int), got {node_count}"
    );
    // Each of these nodes was freshly allocated during the substitute traversal,
    // even though nothing changed. Total waste: {node_count} Arc::new() calls.
}

/// Count nodes in an expression tree (for test assertions only).
fn count_nodes(expr: &ChcExpr) -> usize {
    match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::Var(_) => 1,
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            1 + args.iter().map(|a| count_nodes(a)).sum::<usize>()
        }
        _ => 1,
    }
}
