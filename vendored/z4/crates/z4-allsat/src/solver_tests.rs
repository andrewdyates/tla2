// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_single_solution() {
    let mut solver = AllSatSolver::new();

    // x1 AND x2
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2]);

    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 1);
    assert!(solutions[0].is_true(1));
    assert!(solutions[0].is_true(2));
}

#[test]
fn test_two_solutions() {
    let mut solver = AllSatSolver::new();

    // (x1 OR x2) AND NOT(x1 AND x2)
    // = (x1 OR x2) AND (NOT x1 OR NOT x2)
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);

    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 2);

    // Should have x1=T,x2=F and x1=F,x2=T
    let has_10 = solutions.iter().any(|s| s.is_true(1) && !s.is_true(2));
    let has_01 = solutions.iter().any(|s| !s.is_true(1) && s.is_true(2));
    assert!(has_10, "Should have solution x1=T, x2=F");
    assert!(has_01, "Should have solution x1=F, x2=T");
}

#[test]
fn test_unsat() {
    let mut solver = AllSatSolver::new();

    // x1 AND NOT x1
    solver.add_clause(vec![1]);
    solver.add_clause(vec![-1]);

    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 0);
}

#[test]
fn test_all_assignments() {
    let mut solver = AllSatSolver::new();

    // TRUE (no clauses restricts nothing, but we need at least one var)
    // Add a tautology: x1 OR NOT x1
    solver.add_clause(vec![1, -1]);

    let solutions = solver.enumerate();
    // Two solutions: x1=T and x1=F
    assert_eq!(solutions.len(), 2);
}

#[test]
fn test_bounded_enumeration() {
    let mut solver = AllSatSolver::new();

    // (x1 OR x2) - has 3 solutions (TT, TF, FT)
    solver.add_clause(vec![1, 2]);

    let config = AllSatConfig {
        max_solutions: Some(2),
        ..Default::default()
    };
    let solutions = solver.enumerate_with_config(config);
    assert_eq!(solutions.len(), 2);
}

#[test]
fn test_projected_enumeration() {
    let mut solver = AllSatSolver::new();

    // x1 AND (x2 OR x3)
    // Full solutions: x1=T,x2=T,x3=T; x1=T,x2=T,x3=F; x1=T,x2=F,x3=T
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2, 3]);

    // Project onto x1 only
    let config = AllSatConfig {
        projection: Some(vec![1]),
        ..Default::default()
    };
    let solutions = solver.enumerate_with_config(config);
    // Only one projected solution: x1=T
    assert_eq!(solutions.len(), 1);
    assert!(solutions[0].is_true(1));
}

#[test]
fn test_count() {
    let mut solver = AllSatSolver::new();

    // (x1 OR x2) - has 3 solutions
    solver.add_clause(vec![1, 2]);

    assert_eq!(solver.count(), 3);
}

#[test]
fn test_is_sat() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    assert!(solver.is_sat());

    let mut solver2 = AllSatSolver::new();
    solver2.add_clause(vec![1]);
    solver2.add_clause(vec![-1]);
    assert!(!solver2.is_sat());
}

#[test]
fn test_unique_solution() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1]);
    solver.add_clause(vec![2]);
    assert!(solver.has_unique_solution());

    let mut solver2 = AllSatSolver::new();
    solver2.add_clause(vec![1, 2]);
    solver2.add_clause(vec![-1, -2]);
    assert!(!solver2.has_unique_solution()); // Has 2 solutions
}

#[test]
fn test_iterator_early_termination() {
    let mut solver = AllSatSolver::new();

    // x1 OR x2 OR x3 - has 7 solutions
    solver.add_clause(vec![1, 2, 3]);

    let mut count = 0;
    for _ in solver.iter() {
        count += 1;
        if count >= 3 {
            break;
        }
    }
    assert_eq!(count, 3);
}

#[test]
fn test_solution_to_literals() {
    let solution = Solution {
        assignment: vec![false, true, false, true], // x1=T, x2=F, x3=T
    };

    let lits = solution.to_literals(&[1, 2, 3]);
    assert_eq!(lits, vec![1, -2, 3]);
}

#[test]
fn test_solution_satisfies() {
    let solution = Solution {
        assignment: vec![false, true, false], // x1=T, x2=F
    };

    assert!(solution.satisfies(1)); // x1 is true
    assert!(!solution.satisfies(-1)); // NOT x1 is false
    assert!(!solution.satisfies(2)); // x2 is false
    assert!(solution.satisfies(-2)); // NOT x2 is true
}

#[test]
fn test_empty_formula() {
    let mut solver = AllSatSolver::new();
    // Empty formula with no variables
    let solutions = solver.enumerate();
    // Empty formula has one solution (the empty assignment)
    assert_eq!(solutions.len(), 1);
}

#[test]
fn test_stats() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);

    let _ = solver.enumerate();

    let stats = solver.stats();
    assert!(stats.sat_calls > 0);
    assert_eq!(stats.solutions_found, 2);
    assert_eq!(stats.blocking_clauses, 2);
}

#[test]
fn test_pigeonhole_3_2() {
    // 3 pigeons, 2 holes - no solution
    let mut solver = AllSatSolver::new();

    // p_{i,j} = pigeon i in hole j
    // Variables: p11=1, p12=2, p21=3, p22=4, p31=5, p32=6

    // Each pigeon must be in some hole
    solver.add_clause(vec![1, 2]); // p1 in h1 or h2
    solver.add_clause(vec![3, 4]); // p2 in h1 or h2
    solver.add_clause(vec![5, 6]); // p3 in h1 or h2

    // No two pigeons in same hole
    // Hole 1: at most one of p11, p21, p31
    solver.add_clause(vec![-1, -3]); // not (p11 and p21)
    solver.add_clause(vec![-1, -5]); // not (p11 and p31)
    solver.add_clause(vec![-3, -5]); // not (p21 and p31)

    // Hole 2: at most one of p12, p22, p32
    solver.add_clause(vec![-2, -4]); // not (p12 and p22)
    solver.add_clause(vec![-2, -6]); // not (p12 and p32)
    solver.add_clause(vec![-4, -6]); // not (p22 and p32)

    let solutions = solver.enumerate();
    assert_eq!(solutions.len(), 0, "Pigeonhole 3->2 should be UNSAT");
}

#[test]
fn test_pigeonhole_2_2() {
    // 2 pigeons, 2 holes - has solutions
    let mut solver = AllSatSolver::new();

    // Variables: p11=1, p12=2, p21=3, p22=4

    // Each pigeon must be in some hole
    solver.add_clause(vec![1, 2]); // p1 in h1 or h2
    solver.add_clause(vec![3, 4]); // p2 in h1 or h2

    // No two pigeons in same hole
    solver.add_clause(vec![-1, -3]); // not (p11 and p21)
    solver.add_clause(vec![-2, -4]); // not (p12 and p22)

    let solutions = solver.enumerate();
    // Solutions: p1->h1,p2->h2 and p1->h2,p2->h1
    // But also variants with "extra" positions set to false
    assert!(solutions.len() >= 2, "Should have at least 2 solutions");

    // With projection to just the "one per pigeon" decision
    let config = AllSatConfig {
        projection: Some(vec![1, 2, 3, 4]),
        ..Default::default()
    };
    let projected = solver.enumerate_with_config(config);
    // Each pigeon in exactly one hole, 2 valid arrangements
    assert!(projected.len() >= 2);
}

#[test]
fn test_xor_chain() {
    // XOR chain: x1 XOR x2 XOR x3 = true
    // (x1 XOR x2 XOR x3) encoded as CNF
    let mut solver = AllSatSolver::new();

    // x1 XOR x2 XOR x3 = 1 is equivalent to:
    // odd number of variables must be true
    // Clauses: (x1 OR x2 OR x3) AND (!x1 OR !x2 OR x3) AND (!x1 OR x2 OR !x3) AND (x1 OR !x2 OR !x3)
    solver.add_clause(vec![1, 2, 3]);
    solver.add_clause(vec![-1, -2, 3]);
    solver.add_clause(vec![-1, 2, -3]);
    solver.add_clause(vec![1, -2, -3]);

    let solutions = solver.enumerate();
    // Should have 4 solutions: TTF, TFT, FTT, FFF... wait, FFF has 0 true = even, not valid
    // Actually: TTT (3), TFF (1), FTF (1), FFT (1) = 4 solutions with odd parity
    assert_eq!(solutions.len(), 4);

    // Verify each solution has odd parity
    for sol in &solutions {
        let count = (1..=3).filter(|&v| sol.is_true(v)).count();
        assert!(count % 2 == 1, "XOR chain should have odd parity");
    }
}
