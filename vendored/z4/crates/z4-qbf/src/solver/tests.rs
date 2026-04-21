// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::parser::parse_qdimacs;

#[test]
fn test_simple_sat_qbf() {
    // ∃x. x
    // This is SAT: just set x = true
    let input = "p cnf 1 1\ne 1 0\n1 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_simple_unsat_qbf() {
    // ∃x. (x ∧ ¬x)
    // This is UNSAT
    let input = "p cnf 1 2\ne 1 0\n1 0\n-1 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
fn test_universal_sat() {
    // ∀x. (x ∨ ¬x)
    // This is SAT (tautology)
    let input = "p cnf 1 1\na 1 0\n1 -1 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_universal_unsat() {
    // ∀x. x
    // This is UNSAT: when x = false, clause is false
    let input = "p cnf 1 1\na 1 0\n1 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
fn test_exists_forall_sat() {
    // ∃x∀y. (x ∨ y) ∧ (x ∨ ¬y)
    // SAT: set x = true, then both clauses satisfied regardless of y
    let input = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_exists_forall_unsat() {
    // ∃x∀y. (x ∨ y) ∧ (¬x ∨ ¬y)
    // UNSAT:
    // - If x = true, adversary sets y = true, second clause false
    // - If x = false, adversary sets y = false, first clause false
    let input = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n-1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
fn test_forall_exists_sat() {
    // ∀x∃y. (x ∨ y) ∧ (¬x ∨ ¬y)
    // SAT: for any x, set y = ¬x
    // - If x = true, set y = false: (T∨F)∧(F∨T) = T∧T = T
    // - If x = false, set y = true: (F∨T)∧(T∨F) = T∧T = T
    let input = "p cnf 2 2\na 1 0\ne 2 0\n1 2 0\n-1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_universal_reduction() {
    // ∃x∀y. (x ∨ y)
    // After universal reduction of y (level 1 >= max_exist 0), clause becomes (x)
    // SAT: set x = true
    let input = "p cnf 2 1\ne 1 0\na 2 0\n1 2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_stats() {
    let input = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n-1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    solver.solve();
    let stats = solver.stats();
    // Should have some activity
    assert!(stats.decisions > 0 || stats.propagations > 0 || stats.conflicts > 0);
}

#[test]
fn test_three_quantifier_blocks_sat() {
    // ∃x∀y∃z. (x ∨ y ∨ z) ∧ (¬x ∨ ¬y ∨ z) ∧ (x ∨ ¬y ∨ ¬z)
    // SAT: set x = true, z = true
    // For any y:
    //   y=T: (T∨T∨T) ∧ (F∨F∨T) ∧ (T∨F∨F) = T ∧ T ∧ T = T
    //   y=F: (T∨F∨T) ∧ (F∨T∨T) ∧ (T∨T∨F) = T ∧ T ∧ T = T
    let input = r#"
p cnf 3 3
e 1 0
a 2 0
e 3 0
1 2 3 0
-1 -2 3 0
1 -2 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_three_quantifier_blocks_unsat() {
    // ∃x∀y∃z. (y) ∧ (¬y)
    // This is UNSAT because for y=T or y=F, one clause fails
    let input = r#"
p cnf 3 2
e 1 0
a 2 0
e 3 0
2 0
-2 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
fn test_multiple_existential_per_block() {
    // ∃x₁x₂∀y. (x₁ ∨ x₂ ∨ y) ∧ (x₁ ∨ x₂ ∨ ¬y)
    // SAT: set x₁ = true (or x₂ = true)
    let input = r#"
p cnf 3 2
e 1 2 0
a 3 0
1 2 3 0
1 2 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_multiple_universal_per_block() {
    // ∃x∀y₁y₂. (x ∨ y₁ ∨ y₂) ∧ (x ∨ y₁ ∨ ¬y₂) ∧ (x ∨ ¬y₁ ∨ y₂) ∧ (x ∨ ¬y₁ ∨ ¬y₂)
    // SAT: set x = true (satisfies all clauses regardless of y₁, y₂)
    let input = r#"
p cnf 3 4
e 1 0
a 2 3 0
1 2 3 0
1 2 -3 0
1 -2 3 0
1 -2 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_forall_exists_unsat_dependency() {
    // ∀x∃y. (x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ ¬y)
    // UNSAT: y cannot satisfy all clauses for all x
    // x=T: need y for (¬x∨y), need ¬y for (x∨¬y) - contradiction
    // x=F: need y for (x∨y), need ¬y for (¬x∨¬y) - contradiction
    let input = r#"
p cnf 2 4
a 1 0
e 2 0
1 2 0
-1 2 0
1 -2 0
-1 -2 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve_with_limit(100);
    assert!(
        matches!(result, QbfResult::Unsat(_)),
        "Expected Unsat, got {result:?}"
    );
}

#[test]
fn test_cube_learning_basic() {
    // Test that cube learning correctly handles partial solutions
    // ∃x∀y∀z. (x ∨ y) ∧ (x ∨ ¬y) ∧ (x ∨ z) ∧ (x ∨ ¬z)
    // SAT: x = true satisfies all clauses regardless of y, z
    // This should trigger cube learning when x=true makes everything SAT
    let input = r#"
p cnf 3 4
e 1 0
a 2 3 0
1 2 0
1 -2 0
1 3 0
1 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));

    // Check that cube learning happened
    let stats = solver.stats();
    assert!(
        stats.learned_cubes > 0 || stats.decisions <= 2,
        "Expected cube learning or quick SAT detection"
    );
}

#[test]
fn test_cube_learning_multiple_universals() {
    // Test cube learning with multiple universal variables
    // ∃x₁x₂∀y₁y₂. (x₁ ∨ y₁) ∧ (x₁ ∨ ¬y₁) ∧ (x₂ ∨ y₂) ∧ (x₂ ∨ ¬y₂)
    // SAT: x₁ = true, x₂ = true
    // The solver should learn cubes to avoid exploring all y₁, y₂ combinations
    let input = r#"
p cnf 4 4
e 1 2 0
a 3 4 0
1 3 0
1 -3 0
2 4 0
2 -4 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_cube_propagation() {
    // Test that cube propagation works correctly
    // ∃x∀y∀z. (x ∨ y ∨ z) ∧ (x ∨ y ∨ ¬z) ∧ (x ∨ ¬y ∨ z) ∧ (x ∨ ¬y ∨ ¬z)
    // SAT: x = true satisfies all
    // After x = true, z = true leads to SAT → cube (z) learned
    // Cube propagation should then try z = false automatically
    let input = r#"
p cnf 3 4
e 1 0
a 2 3 0
1 2 3 0
1 2 -3 0
1 -2 3 0
1 -2 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));

    let stats = solver.stats();
    // With cube learning and propagation, we should solve efficiently
    assert!(
        stats.decisions <= 10,
        "Too many decisions: {}",
        stats.decisions
    );
}

/// Document that the QBF solver has no learned clause/cube reduction.
///
/// Unlike the SAT solver (which has `reduce_db`), the QBF solver's `learned`
/// and `cubes` vectors grow monotonically. Every non-level-0 conflict adds
/// a clause; every cube learning event adds a cube. Nothing is ever removed.
///
/// When clause database reduction is implemented, update this test to verify
/// that learned_clauses can decrease between invocations.
#[test]
fn test_learned_clause_reduction() {
    // ∃x∀y. (x ∨ y) ∧ (¬x ∨ ¬y) — UNSAT (from test_exists_forall_unsat)
    // With clause database reduction, learned_clauses + clauses_deleted
    // equals the total clauses ever learned. Active count is bounded.
    let input = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n-1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let _result = solver.solve();

    let stats = solver.stats();
    // Active learned clauses are bounded by total minus deleted
    assert!(
        stats.learned_clauses + stats.clauses_deleted <= stats.conflicts,
        "active ({}) + deleted ({}) should not exceed conflicts ({})",
        stats.learned_clauses,
        stats.clauses_deleted,
        stats.conflicts,
    );
}
