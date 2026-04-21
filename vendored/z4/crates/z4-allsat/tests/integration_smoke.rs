// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_allsat::{AllSatConfig, AllSatSolver};

#[test]
fn projection_collapses_models_with_same_projected_assignment() {
    let mut solver = AllSatSolver::new();

    // x1 must be true.
    solver.add_clause(vec![1]);
    // Tautology introduces x2 but does not constrain it.
    solver.add_clause(vec![2, -2]);

    // Full assignments differ on x2, so two models exist.
    assert_eq!(solver.count(), 2);

    // Projecting onto x1 collapses both models into one projected assignment.
    let projected = solver.enumerate_with_config(AllSatConfig {
        projection: Some(vec![1]),
        ..AllSatConfig::default()
    });
    assert_eq!(projected.len(), 1);
    assert_eq!(projected[0].get(1), Some(true));
}

#[test]
fn max_solutions_limit_stops_enumeration() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);

    let bounded = solver.enumerate_with_config(AllSatConfig {
        max_solutions: Some(1),
        ..AllSatConfig::default()
    });
    assert_eq!(bounded.len(), 1);
}
