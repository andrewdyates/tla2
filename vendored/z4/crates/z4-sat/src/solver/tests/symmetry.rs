// Copyright 2026 Andrew Yates.
// Author: AI Model
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_preprocess_symmetry_adds_binary_order_clause_for_swap_pair() {
    let mut solver = Solver::new(3);

    let x0 = Variable(0);
    let x1 = Variable(1);
    let z = Variable(2);

    // x0 and x1 are interchangeable in this formula.
    assert!(solver.add_clause(vec![Literal::positive(x0), Literal::positive(z),]));
    assert!(solver.add_clause(vec![Literal::positive(x1), Literal::positive(z),]));
    assert!(solver.add_clause(vec![Literal::negative(x0), Literal::negative(z),]));
    assert!(solver.add_clause(vec![Literal::negative(x1), Literal::negative(z),]));

    let before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat, "symmetry preprocessing should not derive UNSAT");
    assert!(changed, "symmetry preprocessing should emit an SBP");
    assert_eq!(
        solver.arena.active_clause_count(),
        before + 1,
        "expected one binary SBP clause",
    );

    let expected = vec![Literal::positive(x0), Literal::negative(x1)];
    let found = solver
        .arena
        .active_indices()
        .filter(|&clause_idx| !solver.arena.is_learned(clause_idx))
        .map(|clause_idx| {
            let mut lits = solver.arena.literals(clause_idx).to_vec();
            lits.sort_unstable_by_key(|lit| lit.raw());
            lits
        })
        .any(|lits| lits == expected);

    assert!(found, "expected symmetry SBP clause {expected:?} in arena",);
    assert_eq!(solver.cold.symmetry_stats.pairs_detected, 1);
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 1);
}

#[test]
fn test_preprocess_symmetry_skips_proof_mode() {
    let mut solver = Solver::with_proof(2, Vec::<u8>::new());
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(!changed);
    assert_eq!(
        solver.cold.symmetry_stats.last_skipped_reason,
        Some(crate::symmetry::SymmetrySkipReason::ProofMode),
    );
}
