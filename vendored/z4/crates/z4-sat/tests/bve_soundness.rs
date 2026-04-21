// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BVE soundness integration tests (Part of #3292).
//!
//! These tests verify that BVE (bounded variable elimination) produces correct
//! results at the solver API level. BVE is currently disabled due to #3292
//! (reconstruction soundness bug). When re-enabled, these tests serve as the
//! soundness regression gate.
//!
//! A companion unit test `test_bve_resolvents_are_irredundant` in
//! `solver/tests.rs` verifies the internal invariant that BVE resolvents
//! are marked irredundant (the #3292 root cause).

use z4_sat::{Literal, SatResult, Solver, Variable};

/// Verify that solving a SAT formula with BVE enabled produces a correct model.
///
/// When BVE is re-enabled, this test exercises the full elimination →
/// reconstruction → model-check pipeline. Currently BVE is disabled
/// (should_bve() returns false), so this serves as a regression gate.
#[test]
fn test_bve_enabled_sat_formula_produces_valid_model() {
    let mut solver = Solver::new(5);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);
    let x3 = Variable::new(3);
    let x4 = Variable::new(4);

    // Formula with a variable (x0) that has bounded resolution.
    // Positive occurrences of x0:
    //   C0: (x0 ∨ x1 ∨ x2)
    //   C1: (x0 ∨ x3)
    // Negative occurrences of x0:
    //   C2: (¬x0 ∨ x2 ∨ x4)
    //   C3: (¬x0 ∨ x1)
    // BVE on x0 would produce resolvents:
    //   R(C0,C2): (x1 ∨ x2 ∨ x4)
    //   R(C0,C3): (x1 ∨ x2)
    //   R(C1,C2): (x3 ∨ x2 ∨ x4)
    //   R(C1,C3): (x3 ∨ x1)
    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x3)]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::positive(x2),
        Literal::positive(x4),
    ]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x1)]);

    // Additional clause to constrain the solution space
    solver.add_clause(vec![Literal::positive(x4)]);

    solver.set_bve_enabled(true);

    let original_clauses: [&[Literal]; 5] = [
        &[
            Literal::positive(x0),
            Literal::positive(x1),
            Literal::positive(x2),
        ],
        &[Literal::positive(x0), Literal::positive(x3)],
        &[
            Literal::negative(x0),
            Literal::positive(x2),
            Literal::positive(x4),
        ],
        &[Literal::negative(x0), Literal::positive(x1)],
        &[Literal::positive(x4)],
    ];

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            // Verify model satisfies all original clauses
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|lit| {
                    let var_idx = lit.variable().index();
                    if var_idx >= model.len() {
                        return false;
                    }
                    if lit.is_positive() {
                        model[var_idx]
                    } else {
                        !model[var_idx]
                    }
                });
                assert!(
                    satisfied,
                    "BVE soundness: model violates original clause #{ci}: {clause:?}"
                );
            }
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Verify that solving a known-UNSAT formula with BVE enabled returns UNSAT.
///
/// This tests the BVE → empty resolvent → UNSAT derivation path.
#[test]
fn test_bve_enabled_unsat_formula_returns_unsat() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    // Unit clauses force x1=T, x2=T
    solver.add_clause(vec![Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x2)]);

    // BVE on x0 produces resolvent (¬x1 ∨ ¬x2), which conflicts with x1=T, x2=T
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(x2)]);

    solver.set_bve_enabled(true);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "Expected UNSAT, got {result:?}");
}
