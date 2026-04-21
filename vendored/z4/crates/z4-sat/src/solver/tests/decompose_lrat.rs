// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_decompose_lrat_rewrite_includes_root_false_literal_proof() {
    let proof = ProofOutput::lrat_text(Vec::new(), 5);
    let mut solver: Solver = Solver::with_proof_output(5, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let a = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));
    let z = Literal::positive(Variable(4));

    // a and (¬a ∨ ¬y) propagate y=false at level 0, but y's proof ID is not a
    // unit input clause. Decompose must materialize that derived unit before
    // using it as an LRAT hint for the rewritten clause.
    solver.add_clause(vec![a]);
    solver.add_clause(vec![a.negated(), y.negated()]);

    // x0 ≡ x1, so (x1 ∨ y ∨ z) rewrites to (x0 ∨ z) after dropping y.
    solver.add_clause(vec![x1.negated(), x0]);
    solver.add_clause(vec![x0.negated(), x1]);
    solver.add_clause(vec![x1, y, z]);

    solver.initialize_watches();
    assert!(
        solver.process_initial_clauses().is_none(),
        "initial units should not conflict"
    );
    assert!(
        !solver.propagate_check_unsat(),
        "root propagation should assign y=false without conflict"
    );
    assert_eq!(
        solver.get_var_assignment(y.variable().index()),
        Some(false),
        "setup must establish the root-false literal used by decompose"
    );

    solver.decompose();

    let rewritten_exists = solver.arena.indices().any(|idx| {
        solver.arena.is_active(idx) && solver.arena.len_of(idx) == 2 && {
            let lits = solver.arena.literals(idx);
            lits.contains(&x0) && lits.contains(&z)
        }
    });
    assert!(
        rewritten_exists,
        "decompose should rewrite (x1 ∨ y ∨ z) into an active binary (x0 ∨ z)"
    );
}
