// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

#[test]
fn compose_scope_assumptions_empty_when_no_scope_or_assumptions() {
    let solver: Solver = Solver::new(2);
    assert!(solver.compose_scope_assumptions(&[]).is_empty());
}

#[test]
fn compose_scope_assumptions_prefixes_scope_selectors() {
    let mut solver: Solver = Solver::new(4);
    solver.cold.scope_selectors = vec![Variable(2), Variable(0)];

    let user_assumptions = [
        Literal::positive(Variable(1)),
        Literal::negative(Variable(3)),
    ];
    let combined = solver.compose_scope_assumptions(&user_assumptions);

    assert_eq!(
        combined,
        vec![
            Literal::negative(Variable(2)),
            Literal::negative(Variable(0)),
            user_assumptions[0],
            user_assumptions[1],
        ]
    );
}

#[test]
fn solve_with_assumptions_refreshes_num_original_clauses_after_bve() {
    let mut solver = Solver::new(6);
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_walk_enabled(false);

    // BVE eliminates x0 by resolving {x0, x1} with {~x0, x2}.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]);

    let assumptions = [Literal::positive(Variable(5))];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(result, AssumeResult::Sat(_)),
        "formula should remain SAT under assumptions after preprocessing, got {result:?}"
    );
    assert!(
        solver.bve_stats().vars_eliminated > 0,
        "test setup must shrink the formula via BVE"
    );

    let active = solver.arena.active_clause_count();
    assert!(
        active < 5,
        "BVE should reduce the active irredundant clause count, got {active}"
    );
    assert_eq!(
        solver.num_original_clauses, active,
        "solve_with_assumptions must refresh num_original_clauses after preprocessing shrink"
    );
}
