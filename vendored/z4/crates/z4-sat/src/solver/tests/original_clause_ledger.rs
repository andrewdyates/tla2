// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the immutable original clause ledger.

use super::*;

#[test]
fn test_decompose_keeps_original_clause_ledger_immutable() {
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // x0 <-> x1 via binary implications. Decompose should rewrite the working
    // clause DB around this equivalence, but `original_clauses` must stay in
    // the user-visible variable space.
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x1), Literal::positive(x0)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x2)]);
    solver.initialize_watches();

    let original_before = solver.cold.original_ledger.to_vec_of_vecs();
    let reconstruction_before = solver.inproc.reconstruction.len();

    solver.decompose();

    assert_eq!(
        solver.cold.original_ledger.to_vec_of_vecs(),
        original_before,
        "decompose must not rewrite original_ledger"
    );
    assert!(
        solver.inproc.reconstruction.len() > reconstruction_before,
        "decompose should still record equivalence reconstruction entries"
    );
}
