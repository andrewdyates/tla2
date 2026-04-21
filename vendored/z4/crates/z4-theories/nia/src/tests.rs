// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// SMOKE TEST: Verifies NiaSolver can be created without panicking.
/// This validates the constructor and basic type instantiation.
#[test]
fn test_nia_solver_creation() {
    let terms = TermStore::new();
    let mut solver = NiaSolver::new(&terms);
    // Verify solver is in a valid initial state
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "fresh solver should not be in conflict, got {result:?}"
    );
}

#[test]
fn test_nonlinear_term_detection() {
    let mut terms = TermStore::new();

    // Create x, y as integer variables
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    // Create nonlinear term x * y
    let xy = terms.mk_mul(vec![x, y]);

    // Create comparison x * y >= 0
    let zero = terms.mk_int(BigInt::from(0));
    let ge_atom = terms.mk_ge(xy, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(ge_atom, true);

    // Check that the nonlinear term was detected and registered
    let mut sorted_vars = vec![x, y];
    sorted_vars.sort_by_key(|t| t.0);
    assert!(
        solver.monomials.contains_key(&sorted_vars),
        "Nonlinear term x*y should be registered"
    );

    // The auxiliary variable should be the multiplication term itself
    let mon = solver
        .monomials
        .get(&sorted_vars)
        .expect("monomial registered");
    assert_eq!(mon.aux_var, xy);
    assert!(mon.is_binary());
}

#[test]
fn test_linear_term_not_registered() {
    let mut terms = TermStore::new();

    // Create x as integer variable
    let x = terms.mk_var("x", Sort::Int);

    // Create linear term 2 * x (constant * variable)
    let two = terms.mk_int(BigInt::from(2));
    let two_x = terms.mk_mul(vec![two, x]);

    // Create comparison 2*x >= 0
    let zero = terms.mk_int(BigInt::from(0));
    let ge_atom = terms.mk_ge(two_x, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(ge_atom, true);

    // Check that no nonlinear term was registered (2*x is linear)
    assert!(
        solver.monomials.is_empty(),
        "Linear term 2*x should not be registered as nonlinear"
    );
}

#[test]
fn test_square_term_detection() {
    let mut terms = TermStore::new();

    // Create x as integer variable
    let x = terms.mk_var("x", Sort::Int);

    // Create square term x * x
    let x_sq = terms.mk_mul(vec![x, x]);

    // Create comparison x*x >= 0
    let zero = terms.mk_int(BigInt::from(0));
    let ge_atom = terms.mk_ge(x_sq, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(ge_atom, true);

    // Check that the square term was detected
    let vars = vec![x, x];
    assert!(
        solver.monomials.contains_key(&vars),
        "Square term x*x should be registered"
    );

    let mon = solver
        .monomials
        .get(&vars)
        .expect("square monomial registered");
    assert!(mon.is_square());
}

#[test]
fn test_nested_nonlinear_detection() {
    let mut terms = TermStore::new();

    // Create x, y, z as integer variables
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);

    // Create x * y + z (nonlinear in x*y, linear in z)
    let xy = terms.mk_mul(vec![x, y]);
    let xy_plus_z = terms.mk_add(vec![xy, z]);

    // Create comparison x*y + z >= 0
    let zero = terms.mk_int(BigInt::from(0));
    let ge_atom = terms.mk_ge(xy_plus_z, zero);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(ge_atom, true);

    // Check that x*y was detected
    let mut sorted_vars = vec![x, y];
    sorted_vars.sort_by_key(|t| t.0);
    assert!(
        solver.monomials.contains_key(&sorted_vars),
        "Nested nonlinear term x*y should be registered"
    );
}

#[test]
fn test_nia_push_pop() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_int(BigInt::from(0));
    let ge_atom = terms.mk_ge(xy, zero);
    let le_atom = terms.mk_le(xy, zero);

    let mut solver = NiaSolver::new(&terms);

    // Assert at level 0
    solver.assert_literal(ge_atom, true);
    assert_eq!(solver.asserted.len(), 1);

    // Push and assert more
    solver.push();
    solver.assert_literal(le_atom, true);
    assert_eq!(solver.asserted.len(), 2);

    // Pop should restore state
    solver.pop();
    assert_eq!(solver.asserted.len(), 1);
}

/// Regression test: monomials must be removed on pop (#3735)
#[test]
fn test_nia_push_pop_monomials_scoped() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    // Create all terms before borrowing terms in solver
    let xy = terms.mk_mul(vec![x, y]);
    let xy_ge_zero = terms.mk_ge(xy, zero);
    let yz = terms.mk_mul(vec![y, z]);
    let yz_ge_zero = terms.mk_ge(yz, zero);

    let mut solver = NiaSolver::new(&terms);

    // Level 0: assert x*y >= 0 (registers monomial x*y)
    solver.assert_literal(xy_ge_zero, true);

    let monomials_0 = solver.monomials.len();
    let aux_0 = solver.aux_to_monomial.len();
    assert_eq!(monomials_0, 1, "one monomial registered at level 0");

    // Push, then register a new monomial y*z at deeper scope
    solver.push();
    solver.assert_literal(yz_ge_zero, true);

    assert_eq!(solver.monomials.len(), 2, "two monomials at level 1");
    assert_eq!(solver.aux_to_monomial.len(), 2);

    // Pop should remove the scoped monomial y*z
    solver.pop();
    assert_eq!(
        solver.monomials.len(),
        monomials_0,
        "monomials must be restored to level 0 count after pop"
    );
    assert_eq!(
        solver.aux_to_monomial.len(),
        aux_0,
        "aux_to_monomial must be restored after pop"
    );

    // Verify the base-level monomial x*y still exists
    let mut sorted_xy = vec![x, y];
    sorted_xy.sort_by_key(|t| t.0);
    assert!(
        solver.monomials.contains_key(&sorted_xy),
        "base-level monomial x*y must survive pop"
    );
}

/// Regression test: sign_constraints must be restored on pop (#3523)
#[test]
fn test_nia_push_pop_sign_constraints() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    // x > 0 → sign constraint Positive on x
    let x_gt_zero = terms.mk_gt(x, zero);
    // y > 0 → sign constraint Positive on y
    let y_gt_zero = terms.mk_gt(y, zero);

    // x*y to register a monomial so sign constraints are tracked
    let xy = terms.mk_mul(vec![x, y]);
    let xy_ge_zero = terms.mk_ge(xy, zero);

    let mut solver = NiaSolver::new(&terms);

    // Level 0: assert x*y >= 0 (registers monomial) and x > 0
    solver.assert_literal(xy_ge_zero, true);
    solver.assert_literal(x_gt_zero, true);

    let sign_count_0 = solver.var_sign_constraints.len();
    let x_constraints_0 = solver
        .var_sign_constraints
        .get(&x)
        .cloned()
        .expect("x sign constraint should exist at level 0");
    assert_eq!(
        x_constraints_0,
        vec![(SignConstraint::Positive, x_gt_zero)],
        "level-0 x sign constraint should be recorded exactly once"
    );
    assert!(
        !solver.var_sign_constraints.contains_key(&y),
        "y should not have sign constraints before scoped assertion"
    );

    // Push, then assert y > 0 at deeper scope
    solver.push();
    solver.assert_literal(y_gt_zero, true);

    let sign_count_1 = solver.var_sign_constraints.len();
    assert!(
        sign_count_1 >= sign_count_0,
        "deeper scope should have at least as many sign constraints"
    );
    assert!(
        solver.var_sign_constraints.contains_key(&y),
        "scoped y constraint should be present before pop"
    );

    // Pop should restore sign constraints
    solver.pop();
    assert_eq!(
        solver.var_sign_constraints.len(),
        sign_count_0,
        "sign constraints should be restored after pop"
    );
    assert_eq!(
        solver.var_sign_constraints.get(&x),
        Some(&x_constraints_0),
        "level-0 x sign constraints must be restored exactly after pop"
    );
    assert!(
        !solver.var_sign_constraints.contains_key(&y),
        "scoped y sign constraints must be removed on pop"
    );
}
