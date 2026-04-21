// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_simple_unweighted() {
    let mut solver = MaxSatSolver::new();

    // x1 OR x2 (hard)
    solver.add_hard_clause(vec![1, 2]);

    // Prefer x1 = true
    solver.add_soft_clause(vec![1], 1);
    // Prefer x2 = true
    solver.add_soft_clause(vec![2], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => {
            assert_eq!(cost, 0, "Should satisfy all clauses");
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_conflicting_soft_clauses() {
    let mut solver = MaxSatSolver::new();

    // Soft: x1 = true
    solver.add_soft_clause(vec![1], 1);
    // Soft: x1 = false (conflicts!)
    solver.add_soft_clause(vec![-1], 1);
    // Soft: x2 = true
    solver.add_soft_clause(vec![2], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 1, "Should violate exactly one clause");
            // x2 should be true (satisfies third clause)
            assert!(model.get(2).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_weighted() {
    let mut solver = MaxSatSolver::new();

    // Soft: x1 = true (weight 10)
    solver.add_soft_clause(vec![1], 10);
    // Soft: x1 = false (weight 1)
    solver.add_soft_clause(vec![-1], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Should prefer violating the weight-1 clause
            assert_eq!(cost, 1);
            // x1 should be true (higher weight)
            assert!(model.get(1).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_unsatisfiable_hard() {
    let mut solver = MaxSatSolver::new();

    // Hard: x1
    solver.add_hard_clause(vec![1]);
    // Hard: !x1
    solver.add_hard_clause(vec![-1]);

    let result = solver.solve();
    assert_eq!(result, MaxSatResult::Unsatisfiable);
}

#[test]
fn test_only_hard_clauses() {
    let mut solver = MaxSatSolver::new();

    solver.add_hard_clause(vec![1, 2]);
    solver.add_hard_clause(vec![-1, 2]);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 0);
            // x2 must be true to satisfy both
            assert!(model.get(2).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_only_soft_clauses() {
    let mut solver = MaxSatSolver::new();

    solver.add_soft_clause(vec![1], 1);
    solver.add_soft_clause(vec![2], 1);
    solver.add_soft_clause(vec![3], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Check that we can satisfy all soft clauses
            assert_eq!(cost, 0);
            // All should be true
            assert!(model.get(1).copied().unwrap_or(false));
            assert!(model.get(2).copied().unwrap_or(false));
            assert!(model.get(3).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_partial_maxsat() {
    let mut solver = MaxSatSolver::new();

    // Hard: at most one of x1, x2, x3 (encoded)
    // !x1 OR !x2
    solver.add_hard_clause(vec![-1, -2]);
    // !x1 OR !x3
    solver.add_hard_clause(vec![-1, -3]);
    // !x2 OR !x3
    solver.add_hard_clause(vec![-2, -3]);

    // Soft: want all three
    solver.add_soft_clause(vec![1], 1);
    solver.add_soft_clause(vec![2], 1);
    solver.add_soft_clause(vec![3], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Can only satisfy 1 soft clause
            assert_eq!(cost, 2);
            // Exactly one should be true
            let count: usize = (1..=3)
                .filter(|&i| model.get(i).copied().unwrap_or(false))
                .count();
            assert_eq!(count, 1);
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_empty_instance() {
    let mut solver = MaxSatSolver::new();
    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => {
            assert_eq!(cost, 0);
        }
        _ => panic!("Expected optimal solution for empty instance"),
    }
}

#[test]
fn test_stats() {
    let mut solver = MaxSatSolver::new();

    solver.add_soft_clause(vec![1], 1);
    solver.add_soft_clause(vec![-1], 1);

    solver.solve();

    let stats = solver.stats();
    assert!(stats.sat_calls > 0, "Should have made SAT calls");
}

#[test]
fn test_default_trait() {
    let mut solver = MaxSatSolver::default();
    solver.add_soft_clause(vec![1], 1);
    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => assert_eq!(cost, 0),
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_sequential_counter_encoding() {
    // 8 soft clauses triggers sequential counter (n > 6 && k > 1)
    let mut solver = MaxSatSolver::new();

    // Hard: at most one of x1..x8
    for i in 1_i32..=8 {
        for j in (i + 1)..=8 {
            solver.add_hard_clause(vec![-i, -j]);
        }
    }

    // Soft: want all 8 to be true
    for i in 1_i32..=8 {
        solver.add_soft_clause(vec![i], 1);
    }

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Can only satisfy 1 soft clause (at-most-one hard constraint)
            assert_eq!(cost, 7);
            let count: usize = (1..=8)
                .filter(|&i| model.get(i).copied().unwrap_or(false))
                .count();
            assert_eq!(count, 1);
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_multi_stratum_weighted() {
    // 3 distinct weights to exercise stratified solver
    let mut solver = MaxSatSolver::new();

    // x1 = true (high priority)
    solver.add_soft_clause(vec![1], 100);
    // x1 = false (medium priority)
    solver.add_soft_clause(vec![-1], 10);
    // x2 = true (low priority)
    solver.add_soft_clause(vec![2], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Should violate weight-10 clause (x1 = false)
            assert_eq!(cost, 10);
            // x1 = true (weight 100 > weight 10)
            assert!(model.get(1).copied().unwrap_or(false));
            // x2 = true (no conflict)
            assert!(model.get(2).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_stratified_conditions_lower_strata_on_higher_bounds() {
    let mut solver = MaxSatSolver::new();
    solver.add_soft_clause(vec![1], 100);
    solver.add_soft_clause(vec![2], 100);
    solver.add_soft_clause(vec![-1, -2], 10);

    // Mimic solve() relaxation-variable allocation so we can probe
    // stratum minimization directly.
    for soft in &mut solver.soft_clauses {
        soft.relax_var = solver.next_var;
        solver.next_var += 1;
    }

    let high_indices = vec![0, 1];
    let high_relax_vars: Vec<u32> = high_indices
        .iter()
        .map(|&i| solver.soft_clauses[i].relax_var)
        .collect();
    let high_min = solver.find_min_violations_for_stratum(&high_indices, &[]);
    assert_eq!(high_min, 0);

    let low_indices = vec![2];
    let low_min =
        solver.find_min_violations_for_stratum(&low_indices, &[(high_relax_vars, high_min)]);
    assert_eq!(
        low_min, 1,
        "Lower stratum must respect fixed high-priority bounds"
    );
}

#[test]
fn test_weighted_partial_maxsat() {
    // Hard clauses + unit-weight soft clauses (binary search path)
    let mut solver = MaxSatSolver::new();

    // Hard: x1 OR x2
    solver.add_hard_clause(vec![1, 2]);
    // Hard: x3 OR x4
    solver.add_hard_clause(vec![3, 4]);

    // Soft: prefer all false (conflicting with hard)
    solver.add_soft_clause(vec![-1], 1);
    solver.add_soft_clause(vec![-2], 1);
    solver.add_soft_clause(vec![-3], 1);
    solver.add_soft_clause(vec![-4], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            // Must satisfy hard: x1 OR x2, x3 OR x4
            let x1 = model.get(1).copied().unwrap_or(false);
            let x2 = model.get(2).copied().unwrap_or(false);
            let x3 = model.get(3).copied().unwrap_or(false);
            let x4 = model.get(4).copied().unwrap_or(false);
            assert!(x1 || x2, "Hard clause x1 OR x2 violated");
            assert!(x3 || x4, "Hard clause x3 OR x4 violated");
            // Minimum 2 violations (one from each hard pair)
            assert_eq!(cost, 2);
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_single_variable() {
    let mut solver = MaxSatSolver::new();
    solver.add_soft_clause(vec![1], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 0);
            assert!(model.get(1).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_all_soft_conflicting() {
    // Every pair of soft clauses conflicts
    let mut solver = MaxSatSolver::new();

    // x1, NOT x1, x2, NOT x2
    solver.add_soft_clause(vec![1], 1);
    solver.add_soft_clause(vec![-1], 1);
    solver.add_soft_clause(vec![2], 1);
    solver.add_soft_clause(vec![-2], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => {
            assert_eq!(cost, 2, "Must violate exactly 2 of 4 conflicting clauses");
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_hard_subsumes_soft() {
    // Hard clause forces assignment, soft agrees
    let mut solver = MaxSatSolver::new();

    // Hard: x1 must be true
    solver.add_hard_clause(vec![1]);
    // Soft: prefer x1 = true (already forced)
    solver.add_soft_clause(vec![1], 1);
    // Soft: prefer x1 = false (violated by hard)
    solver.add_soft_clause(vec![-1], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, model } => {
            assert_eq!(cost, 1);
            assert!(model.get(1).copied().unwrap_or(false));
        }
        _ => panic!("Expected optimal solution"),
    }
}

#[test]
fn test_large_clause_soft() {
    let mut solver = MaxSatSolver::new();

    // Soft: x1 OR x2 OR x3 OR x4 OR x5 (easy to satisfy)
    solver.add_soft_clause(vec![1, 2, 3, 4, 5], 1);
    // Soft: NOT x1 OR NOT x2 OR ... (all negative lits - also easy to satisfy)
    solver.add_soft_clause(vec![-1, -2, -3, -4, -5], 1);

    let result = solver.solve();
    match result {
        MaxSatResult::Optimal { cost, .. } => {
            assert_eq!(cost, 0, "Both large clauses should be satisfiable");
        }
        _ => panic!("Expected optimal solution"),
    }
}
