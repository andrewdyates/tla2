// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential tests: safe BCP vs unsafe BCP (#7989).
//!
//! Every test creates two identical solver instances, applies the same
//! decisions, runs safe BCP on one and unsafe BCP on the other, then
//! asserts that trail, qhead, and conflict results are identical.
//!
//! Gated on `#[cfg(feature = "unsafe-bcp")]` — these tests only compile
//! when the unsafe BCP implementation is present.

use super::*;
use crate::solver::propagation::bcp_mode;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Literal from a DIMACS-style signed integer.
/// Positive n => positive literal for variable (n-1).
/// Negative n => negative literal for variable (|n|-1).
fn lit(dimacs: i32) -> Literal {
    assert!(dimacs != 0, "DIMACS literal 0 is invalid");
    let var = Variable(dimacs.unsigned_abs() - 1);
    if dimacs > 0 {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}

/// Build a solver from DIMACS-style clause descriptions.
/// `num_vars`: number of variables.
/// `clauses`: each inner vec is a clause of signed DIMACS literals.
fn build_solver(num_vars: usize, clauses: &[Vec<i32>]) -> Solver {
    let mut solver = Solver::new(num_vars);
    for clause in clauses {
        let lits: Vec<Literal> = clause.iter().map(|&d| lit(d)).collect();
        solver.add_clause(lits);
    }
    solver.initialize_watches();
    let _ = solver.process_initial_clauses();
    // NOTE: do NOT run BCP here — let run_bcp_comparison control when BCP runs
    // so we can compare safe vs unsafe on the initial propagation too.
    solver
}

/// Snapshot of solver state after BCP, for comparison.
#[derive(Debug, PartialEq)]
struct BcpSnapshot {
    trail: Vec<Literal>,
    qhead: usize,
    conflict: Option<u32>, // ClauseRef.0 if conflict, None otherwise
}

fn snapshot(solver: &Solver, conflict: Option<ClauseRef>) -> BcpSnapshot {
    BcpSnapshot {
        trail: solver.trail.clone(),
        qhead: solver.qhead,
        conflict: conflict.map(|c| c.0),
    }
}

/// Run BCP comparison: build two identical solvers, apply decisions,
/// run safe vs unsafe BCP, assert identical outcomes.
///
/// Returns the safe BCP snapshot for further inspection if needed.
fn run_bcp_comparison(
    num_vars: usize,
    clauses: &[Vec<i32>],
    decisions: &[i32],
) -> BcpSnapshot {
    let mut safe_solver = build_solver(num_vars, clauses);
    let mut unsafe_solver = build_solver(num_vars, clauses);

    // Verify identical starting state
    assert_eq!(
        safe_solver.trail.len(),
        unsafe_solver.trail.len(),
        "solvers should have identical trail length after setup"
    );
    assert_eq!(
        safe_solver.qhead, unsafe_solver.qhead,
        "solvers should have identical qhead after setup"
    );

    // Run initial BCP to drain unit propagations from process_initial_clauses.
    // Compare safe vs unsafe even on initial propagation.
    let mut safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let mut unsafe_conflict = unsafe_solver.propagate_bcp_unsafe::<{ bcp_mode::SEARCH }>();

    if safe_conflict.is_some() || unsafe_conflict.is_some() {
        // Initial BCP found conflict (e.g. contradictory units) — compare and return early.
        let safe_snap = snapshot(&safe_solver, safe_conflict);
        let unsafe_snap = snapshot(&unsafe_solver, unsafe_conflict);
        assert_eq!(
            safe_snap, unsafe_snap,
            "safe and unsafe BCP produced different results on initial propagation.\n\
             Safe:   {safe_snap:?}\n\
             Unsafe: {unsafe_snap:?}"
        );
        return safe_snap;
    }

    // Apply decisions one at a time, running BCP after each.
    for &dec in decisions {
        let decision_lit = lit(dec);

        // Skip if variable already assigned from prior propagation
        if safe_solver.var_is_assigned(decision_lit.variable().index()) {
            continue;
        }

        safe_solver.decide(decision_lit);
        unsafe_solver.decide(decision_lit);

        safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        unsafe_conflict = unsafe_solver.propagate_bcp_unsafe::<{ bcp_mode::SEARCH }>();

        if safe_conflict.is_some() {
            break;
        }
    }

    let safe_snap = snapshot(&safe_solver, safe_conflict);
    let unsafe_snap = snapshot(&unsafe_solver, unsafe_conflict);

    assert_eq!(
        safe_snap, unsafe_snap,
        "safe and unsafe BCP produced different results.\n\
         Safe:   {safe_snap:?}\n\
         Unsafe: {unsafe_snap:?}"
    );

    safe_snap
}

// ---------------------------------------------------------------------------
// Test 1: Unit propagation
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_on_unit_propagation() {
    // Formula: (1) AND (-1 v 2) AND (-2 v 3)
    // Unit clause forces x0=true, then chain propagation: x1=true, x2=true.
    let snap = run_bcp_comparison(
        3,
        &[vec![1], vec![-1, 2], vec![-2, 3]],
        &[], // no decisions needed — unit propagation from level 0
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    assert_eq!(snap.trail.len(), 3, "all 3 variables should be assigned");
    assert_eq!(snap.qhead, 3, "qhead should match trail length");
}

// ---------------------------------------------------------------------------
// Test 2: Conflict detection
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_on_conflict() {
    // Formula: (-1 v -2) AND (1) AND (2)
    // Unit clauses force x0=true and x1=true, but (-1 v -2) conflicts.
    let snap = run_bcp_comparison(
        2,
        &[vec![-1, -2], vec![1], vec![2]],
        &[],
    );
    assert!(
        snap.conflict.is_some(),
        "conflict expected from contradictory unit clauses"
    );
}

// ---------------------------------------------------------------------------
// Test 3: Binary clauses only
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_binary_clauses() {
    // All binary: (-1 v 2), (-2 v 3), (-3 v 4), (-4 v 5)
    // Decide x0=true => chain: x1..x4 all true.
    let snap = run_bcp_comparison(
        5,
        &[vec![-1, 2], vec![-2, 3], vec![-3, 4], vec![-4, 5]],
        &[1], // decide x0 = true
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    // trail: level-0 propagations (none) + decision (1) + propagated (4) = 5
    assert_eq!(snap.trail.len(), 5, "all 5 variables should be assigned");
}

// ---------------------------------------------------------------------------
// Test 4: Long clauses (5+ literals)
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_long_clauses() {
    // 5-literal clause: (-1 v -2 v -3 v -4 v 5)
    // Decide x0=true, x1=true, x2=true, x3=true => forces x4=true.
    let snap = run_bcp_comparison(
        5,
        &[vec![-1, -2, -3, -4, 5]],
        &[1, 2, 3, 4], // four decisions to make the clause unit
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    assert_eq!(snap.trail.len(), 5, "all 5 variables should be assigned");
}

// ---------------------------------------------------------------------------
// Test 5: Replacement scan (saved_pos updates)
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_replacement_scan() {
    // Long clause where BCP must scan past false literals to find a replacement watch.
    // Clause: (1 v 2 v 3 v 4 v 5 v 6)
    // Decide -1 => watch moves. Decide -2 => watch moves again. Etc.
    // Each decision forces the replacement scan to find the next unassigned literal.
    let snap = run_bcp_comparison(
        6,
        &[vec![1, 2, 3, 4, 5, 6]],
        &[-1, -2, -3, -4, -5], // falsify first 5 => forces x5=true
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    assert_eq!(snap.trail.len(), 6, "all 6 variables should be assigned");
}

// ---------------------------------------------------------------------------
// Test 6: Mixed binary and long clauses
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_mixed() {
    // Mix of binary and long clauses.
    // Binary: (-1 v 2), (-2 v 3)
    // Long:   (-1 v -3 v -4 v 5), (-5 v -6 v 7)
    let snap = run_bcp_comparison(
        7,
        &[
            vec![-1, 2],
            vec![-2, 3],
            vec![-1, -3, -4, 5],
            vec![-5, -6, 7],
        ],
        &[1, 4, 6], // decide x0=true, x3=true, x5=true
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    // x0=T(dec), x1=T(prop), x2=T(prop), x3=T(dec), x4=T(prop), x5=T(dec), x6=T(prop)
    assert_eq!(snap.trail.len(), 7, "all 7 variables should be assigned");
}

// ---------------------------------------------------------------------------
// Test 7: Binary conflict after decision
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_binary_conflict() {
    // Formula: (-1 v 2) AND (-2 v 3) AND (-3 v -1)
    // Decide x0=true => BCP: x1=true, x2=true, then (-3 v -1) has
    // both literals false => conflict from binary propagation chain.
    let snap = run_bcp_comparison(
        3,
        &[vec![-1, 2], vec![-2, 3], vec![-3, -1]],
        &[1],
    );
    assert!(
        snap.conflict.is_some(),
        "binary conflict expected from propagation chain"
    );
}

// ---------------------------------------------------------------------------
// Test 8: Long clause conflict
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_long_clause_conflict() {
    // Formula with binary chain + long clause that conflicts:
    //   A: (-1 v 2)   B: (-2 v 3)   C: (-3 v 4)   D: (-4 v -1 v -2 v -3)
    // Decide x0=T → chain: x1=T, x2=T, x3=T.
    // Long clause D: ¬x3=F, ¬x0=F, ¬x1=F, ¬x2=F → all false → conflict.
    let snap = run_bcp_comparison(
        4,
        &[
            vec![-1, 2],               // A: binary
            vec![-2, 3],               // B: binary
            vec![-3, 4],               // C: binary
            vec![-4, -1, -2, -3],      // D: long clause (conflict target)
        ],
        &[1],
    );
    assert!(
        snap.conflict.is_some(),
        "long clause conflict expected from propagation chain"
    );
}

// ---------------------------------------------------------------------------
// Test 9: No propagation (all decisions, no implications)
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_no_propagation() {
    // Independent positive clauses: (1 v 2), (3 v 4)
    // Decide x0=true => satisfies first clause, no propagation.
    let snap = run_bcp_comparison(
        4,
        &[vec![1, 2], vec![3, 4]],
        &[1],
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    // Only the decision, no propagations
    assert_eq!(snap.trail.len(), 1, "only the decision should be on trail");
}

// ---------------------------------------------------------------------------
// Test 10: Multiple watch list updates
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_multiple_watch_updates() {
    // Several clauses all watching the same literal, forcing multiple
    // watch list operations in a single BCP pass.
    // All clauses start with (1 v ...): falsifying x0 triggers scanning all of them.
    let snap = run_bcp_comparison(
        8,
        &[
            vec![1, 2, 3],
            vec![1, 4, 5],
            vec![1, 6, 7],
            vec![1, 8, -2],
        ],
        &[-1], // falsify x0 => all four clauses need watch updates
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
}

// ---------------------------------------------------------------------------
// Test 11: Proptest — exhaustive small random formulas
// ---------------------------------------------------------------------------

mod proptest_bcp {
    use super::*;
    use proptest::prelude::*;

    /// Generate a random 3-SAT clause over `num_vars` variables.
    fn random_clause(num_vars: usize) -> impl Strategy<Value = Vec<i32>> {
        let nv = num_vars as i32;
        proptest::collection::vec(
            (1..=nv).prop_flat_map(|v| prop_oneof![Just(v), Just(-v)]),
            2..=5, // clause length 2..5
        )
    }

    /// Generate a random CNF formula.
    fn random_formula(
        num_vars: usize,
        num_clauses: std::ops::Range<usize>,
    ) -> impl Strategy<Value = Vec<Vec<i32>>> {
        proptest::collection::vec(random_clause(num_vars), num_clauses)
    }

    /// Generate a list of decisions (positive or negative literals).
    fn random_decisions(num_vars: usize, max_decisions: usize) -> impl Strategy<Value = Vec<i32>> {
        let nv = num_vars as i32;
        proptest::collection::vec(
            (1..=nv).prop_flat_map(|v| prop_oneof![Just(v), Just(-v)]),
            0..=max_decisions,
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        #[test]
        fn test_unsafe_bcp_exhaustive_small_formulas(
            clauses in random_formula(6, 5..20),
            decisions in random_decisions(6, 4),
        ) {
            let num_vars = 6;

            let mut safe_solver = build_solver(num_vars, &clauses);
            let mut unsafe_solver = build_solver(num_vars, &clauses);

            // Apply decisions one at a time, running BCP after each.
            // Skip decisions for already-assigned variables.
            for &dec in &decisions {
                let decision_lit = lit(dec);
                let var_idx = decision_lit.variable().index();

                // Both solvers must agree on assignment state
                let safe_assigned = safe_solver.var_is_assigned(var_idx);
                let unsafe_assigned = unsafe_solver.var_is_assigned(var_idx);
                prop_assert_eq!(
                    safe_assigned, unsafe_assigned,
                    "assignment state diverged for var {}", var_idx
                );

                if safe_assigned {
                    continue;
                }

                // Check that qhead == trail.len() (BCP completed) before deciding
                if safe_solver.qhead != safe_solver.trail.len() {
                    break; // previous BCP found conflict, stop
                }

                safe_solver.decide(decision_lit);
                unsafe_solver.decide(decision_lit);

                let safe_conflict =
                    safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
                let unsafe_conflict =
                    unsafe_solver.propagate_bcp_unsafe::<{ bcp_mode::SEARCH }>();

                let safe_snap = snapshot(&safe_solver, safe_conflict);
                let unsafe_snap = snapshot(&unsafe_solver, unsafe_conflict);

                prop_assert_eq!(
                    safe_snap.trail, unsafe_snap.trail,
                    "trail diverged after deciding {}", dec
                );
                prop_assert_eq!(
                    safe_snap.qhead, unsafe_snap.qhead,
                    "qhead diverged after deciding {}", dec
                );
                prop_assert_eq!(
                    safe_snap.conflict, unsafe_snap.conflict,
                    "conflict result diverged after deciding {}", dec
                );

                // If conflict, stop making decisions
                if safe_conflict.is_some() {
                    break;
                }
            }
        }
    }
}

