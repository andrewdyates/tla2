// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn is_redundant_cached_keep_overrides_poison() {
    let mut solver = Solver::new(2);
    let pos_lit = Literal::positive(Variable(0));
    let neg_lit = Literal::negative(Variable(0));

    solver.decision_level = 1;
    solver.enqueue(pos_lit, None);
    solver.min.minimize_flags[0] |= MIN_KEEP;
    solver.min.minimize_flags[0] |= MIN_POISON;

    assert!(
        solver.is_redundant_cached(neg_lit, 1),
        "minimize_keep must take precedence over minimize_poison"
    );
}

#[test]
fn is_literal_removable_for_shrink_keep_overrides_poison() {
    let mut solver = Solver::new(2);
    let pos_lit = Literal::positive(Variable(0));
    let neg_lit = Literal::negative(Variable(0));

    solver.decision_level = 1;
    solver.enqueue(pos_lit, None);
    solver.min.minimize_flags[0] |= MIN_KEEP;
    solver.min.minimize_flags[0] |= MIN_POISON;

    assert!(
        solver.is_literal_removable_for_shrink(neg_lit),
        "shrink removability must treat keep as a successful base case"
    );
}
