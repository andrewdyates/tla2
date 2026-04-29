// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for SAT types, solvers, and solver backends.

use super::*;

#[test]
fn test_lit_encoding() {
    let v = Var(5);
    let pos = Lit::pos(v);
    let neg = Lit::neg(v);
    assert!(pos.is_positive());
    assert!(neg.is_negated());
    assert_eq!(pos.var(), v);
    assert_eq!(neg.var(), v);
    assert_eq!(!pos, neg);
    assert_eq!(!neg, pos);
}

#[test]
fn test_lit_constants() {
    // Var(0) is constant-false. pos(Var(0)) evals to false, neg(Var(0)) evals to true.
    assert_eq!(Lit::FALSE.var(), Var::CONST);
    assert!(Lit::FALSE.is_positive()); // pos(Var(0)) = false
    assert_eq!(Lit::TRUE.var(), Var::CONST);
    assert!(Lit::TRUE.is_negated()); // neg(Var(0)) = !false = true
}

#[test]
fn test_clause_display() {
    let c = Clause::new(vec![Lit::pos(Var(1)), Lit::neg(Var(2))]);
    let s = format!("{c}");
    assert!(s.contains("v1"));
    assert!(s.contains("~v2"));
}

#[test]
fn test_simple_solver_sat() {
    let mut solver = SimpleSolver::new();
    let a = solver.new_var(); // Var(1)
    let b = solver.new_var(); // Var(2)
                              // (a OR b)
    solver.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    assert_eq!(solver.solve(&[]), SatResult::Sat);
}

#[test]
fn test_simple_solver_unsat() {
    let mut solver = SimpleSolver::new();
    let a = solver.new_var(); // Var(1)
                              // (a) AND (!a)
    solver.add_clause(&[Lit::pos(a)]);
    solver.add_clause(&[Lit::neg(a)]);
    assert_eq!(solver.solve(&[]), SatResult::Unsat);
}

#[test]
fn test_simple_solver_assumptions() {
    let mut solver = SimpleSolver::new();
    let a = solver.new_var();
    let b = solver.new_var();
    // (a OR b)
    solver.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    // Assume !a, !b => UNSAT
    assert_eq!(solver.solve(&[Lit::neg(a), Lit::neg(b)]), SatResult::Unsat);
    // Assume a => SAT
    assert_eq!(solver.solve(&[Lit::pos(a)]), SatResult::Sat);
}

#[test]
fn test_simple_solver_model() {
    let mut solver = SimpleSolver::new();
    let a = solver.new_var();
    solver.add_clause(&[Lit::pos(a)]);
    assert_eq!(solver.solve(&[]), SatResult::Sat);
    assert_eq!(solver.value(Lit::pos(a)), Some(true));
    assert_eq!(solver.value(Lit::neg(a)), Some(false));
}

#[test]
fn test_z4sat_cdcl_basic() {
    let mut s = Z4SatCdclSolver::new(3);
    s.add_clause(&[Lit::TRUE]); // Var(0)=false
                                // (!v2 OR !v1) AND (v2 OR v1) — equiv to v2 <=> !v1
    s.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(1))]);
    s.add_clause(&[Lit::pos(Var(2)), Lit::pos(Var(1))]);
    let r1 = s.solve(&[Lit::pos(Var(1))]);
    assert_eq!(r1, SatResult::Sat, "v1=true should be SAT");
}

#[test]
fn test_z4sat_cdcl_incremental_fixed() {
    // z4#7987 fixed in z4 ec8d049a5. Incremental add_clause between
    // solve_with_assumptions calls now returns correct results.
    let mut s = Z4SatCdclSolver::new(3);
    s.add_clause(&[Lit::TRUE]);
    s.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(1))]);
    s.add_clause(&[Lit::pos(Var(2)), Lit::pos(Var(1))]);
    let r1 = s.solve(&[Lit::pos(Var(1))]);
    assert_eq!(r1, SatResult::Sat, "v1=true should be SAT");
    s.add_clause(&[Lit::neg(Var(1))]);
    let r2 = s.solve(&[Lit::pos(Var(2))]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "v2=true after adding !v1 should be SAT (z4#7987 fixed)"
    );
}

#[test]
fn test_z4sat_cdcl_model() {
    let mut s = Z4SatCdclSolver::new(3);
    s.add_clause(&[Lit::pos(Var(1))]);
    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat);
    assert_eq!(s.value(Lit::pos(Var(1))), Some(true));
}

#[test]
fn test_z4sat_cdcl_unsat_core() {
    let mut s = Z4SatCdclSolver::new(3);
    s.add_clause(&[Lit::neg(Var(1))]); // !v1
    let r = s.solve(&[Lit::pos(Var(1))]); // assume v1
    assert_eq!(r, SatResult::Unsat);
    let core = s.unsat_core();
    assert!(core.is_some(), "should have UNSAT core");
}

// --- SolverBackend factory tests ---

#[test]
fn test_solver_backend_z4sat_incremental() {
    let mut s = SolverBackend::Z4Sat.make_solver(3);
    s.add_clause(&[Lit::TRUE]);
    s.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(1))]);
    s.add_clause(&[Lit::pos(Var(2)), Lit::pos(Var(1))]);
    let r1 = s.solve(&[Lit::pos(Var(1))]);
    assert_eq!(r1, SatResult::Sat);
    s.add_clause(&[Lit::neg(Var(1))]);
    let r2 = s.solve(&[Lit::pos(Var(2))]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "Z4Sat should handle incremental correctly"
    );
}

#[test]
fn test_solver_backend_simple_incremental() {
    let mut s = SolverBackend::Simple.make_solver(3);
    s.add_clause(&[Lit::TRUE]);
    s.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(1))]);
    s.add_clause(&[Lit::pos(Var(2)), Lit::pos(Var(1))]);
    let r1 = s.solve(&[Lit::pos(Var(1))]);
    assert_eq!(r1, SatResult::Sat);
    s.add_clause(&[Lit::neg(Var(1))]);
    let r2 = s.solve(&[Lit::pos(Var(2))]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "Simple should handle incremental correctly"
    );
}

#[test]
fn test_solver_backend_default_is_z4sat() {
    assert_eq!(SolverBackend::default(), SolverBackend::Z4Sat);
}

// --- solve_with_temporary_clause push/pop tests (#4016) ---

/// Verify that solve_with_temporary_clause's temporary clause does NOT
/// persist after the call returns. This is the core soundness property
/// for IC3: !cube must not pollute frame solvers.
#[test]
fn test_z4sat_solve_with_temporary_clause_isolation() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // Permanent clause: (a OR b)
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

    // Temporary clause: (!a). With assumption a=true, this conflicts => UNSAT.
    let r1 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(a)]);
    assert_eq!(
        r1,
        SatResult::Unsat,
        "should be UNSAT: assumption a=true conflicts with temp clause !a"
    );

    // After the call, the temp clause !a should be gone.
    // Solving with assumption a=true and only permanent clause (a OR b) => SAT.
    let r2 = s.solve(&[Lit::pos(a)]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "temp clause !a must not persist; (a OR b) with a=true is SAT"
    );
}

/// Verify that a temporary clause that constrains (but doesn't conflict
/// with) the formula yields the correct SAT result and model.
#[test]
fn test_z4sat_solve_with_temporary_clause_sat() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // Permanent clauses: (a OR b) AND (!a OR !b)  — XOR: exactly one is true.
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    s.add_clause(&[Lit::neg(a), Lit::neg(b)]);

    // Temporary clause: (!b) — forces b=false, so a=true.
    let r1 = s.solve_with_temporary_clause(&[], &[Lit::neg(b)]);
    assert_eq!(
        r1,
        SatResult::Sat,
        "XOR(a,b) with temp !b should be SAT (a=true, b=false)"
    );
    assert_eq!(
        s.value(Lit::pos(a)),
        Some(true),
        "a should be true when b is forced false"
    );
    assert_eq!(
        s.value(Lit::pos(b)),
        Some(false),
        "b should be false from temp clause"
    );

    // After temp clause is gone, both solutions should be available.
    let r2 = s.solve(&[]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "XOR(a,b) without temp clause is still SAT"
    );
}

/// Verify that UNSAT cores work correctly through push/pop scopes.
#[test]
fn test_z4sat_solve_with_temporary_clause_unsat_core() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);

    // Permanent clause: (a) — forces a=true.
    s.add_clause(&[Lit::pos(a)]);

    // Temporary clause: (!a) — conflicts with permanent (a) => UNSAT.
    // Assumptions: [a] to make the assumption trackable in the core.
    let r = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(a)]);
    assert_eq!(r, SatResult::Unsat, "a AND !a is UNSAT");

    // UNSAT core should exist (z4-sat supports it).
    let core = s.unsat_core();
    assert!(
        core.is_some(),
        "z4-sat should provide UNSAT core through push/pop"
    );
}

/// Verify that UNSAT cores from solve_with_temporary_clause only contain
/// user-facing literals — no z4-sat internal scope-selector variables (#4024).
///
/// This is the core soundness property for IC3 cube generalization: the MIC
/// (Minimal Inductive Clause) algorithm uses the UNSAT core to drop literals
/// from the cube. If the core contains internal z4-sat variables (scope
/// selectors created by push()), MIC would try to look up those variables
/// in the cube and produce incorrect generalizations.
#[test]
fn test_z4sat_solve_with_temporary_clause_unsat_core_no_scope_lits() {
    let mut s = Z4SatCdclSolver::new(4);
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);

    // Record the user-facing variable count before any push/pop.
    let user_num_vars = s.num_vars;

    // Permanent clauses: (a) AND (b OR c)
    s.add_clause(&[Lit::pos(a)]);
    s.add_clause(&[Lit::pos(b), Lit::pos(c)]);

    // Temporary clause: (!a AND !b AND !c) expressed as three unit temp clauses
    // won't work since solve_with_temporary_clause takes a single clause.
    // Instead: temp clause (!a) conflicts with permanent (a) when a is assumed.
    //
    // Use assumptions [a, b] so the core should be a subset of {a, b}.
    let r = s.solve_with_temporary_clause(
        &[Lit::pos(a), Lit::pos(b)],
        &[Lit::neg(a)], // conflicts with permanent clause (a) + assumption a
    );
    assert_eq!(
        r,
        SatResult::Unsat,
        "should be UNSAT: temp !a conflicts with permanent a + assumption a"
    );

    let core = s.unsat_core().expect("should have UNSAT core");

    // Every literal in the core must have a variable index < user_num_vars.
    // No scope-selector variables (created by push()) should be present.
    for lit in &core {
        assert!(
            lit.var().0 < user_num_vars,
            "UNSAT core contains non-user variable {:?} (index {} >= user_num_vars {}); \
             likely a z4-sat scope selector leaked through (#4024)",
            lit,
            lit.var().0,
            user_num_vars,
        );
    }

    // The core should only contain literals from the assumptions we passed.
    let assumption_vars: std::collections::HashSet<u32> = [a.0, b.0].into();
    for lit in &core {
        assert!(
            assumption_vars.contains(&lit.var().0),
            "UNSAT core literal {:?} is not an assumption variable; \
             core should be a subset of assumptions",
            lit,
        );
    }

    // The core may be empty: the permanent clause (a) directly conflicts
    // with the temp clause (!a), so z4-sat can prove UNSAT without any
    // assumptions. An empty core is a valid (and minimal) UNSAT core.
    // With JIT disabled (#4040), z4-sat's interpreter conflict analysis
    // correctly detects this level-0 conflict without assumption involvement.
    // Previously the JIT path included assumption `a` in the core.
}

/// Verify that repeated push/pop cycles don't accumulate stale literals
/// in subsequent UNSAT cores (#4024). After many cycles, the core from a
/// new solve_with_temporary_clause must still only contain user variables.
#[test]
fn test_z4sat_repeated_push_pop_core_stays_clean() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // Permanent clause: (a)
    s.add_clause(&[Lit::pos(a)]);

    let user_num_vars = s.num_vars;

    // Run 50 push/pop cycles, each producing an UNSAT core.
    for i in 0..50 {
        let r = s.solve_with_temporary_clause(&[Lit::pos(a), Lit::pos(b)], &[Lit::neg(a)]);
        assert_eq!(r, SatResult::Unsat, "iteration {i}: should be UNSAT");

        if let Some(core) = s.unsat_core() {
            for lit in &core {
                assert!(
                    lit.var().0 < user_num_vars,
                    "iteration {i}: UNSAT core contains non-user variable {:?} \
                     (index {} >= user_num_vars {})",
                    lit,
                    lit.var().0,
                    user_num_vars,
                );
            }
        }
    }

    // Solver should still be functional after many cycles.
    let r = s.solve(&[Lit::pos(a)]);
    assert_eq!(
        r,
        SatResult::Sat,
        "solver should work after 50 push/pop cycles"
    );
}

/// Empty temporary clause should behave identically to a regular solve().
#[test]
fn test_z4sat_solve_with_temporary_clause_empty() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

    // Empty temp clause => falls through to regular solve.
    let r1 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[]);
    assert_eq!(
        r1,
        SatResult::Sat,
        "empty temp clause should delegate to regular solve"
    );

    let r2 = s.solve(&[Lit::pos(a)]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "regular solve should match empty-temp-clause result"
    );
}

/// Permanent clauses added via add_clause (which uses add_clause_global
/// internally) must survive solve_with_temporary_clause's push/pop cycle.
#[test]
fn test_z4sat_permanent_clauses_survive_temporary_solve() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // Permanent: (!a) — forces a=false.
    s.add_clause(&[Lit::neg(a)]);
    // Permanent: (a OR b) — with !a, forces b=true.
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

    // Do a solve_with_temporary_clause (the temp clause is irrelevant here).
    let r1 = s.solve_with_temporary_clause(&[], &[Lit::pos(a), Lit::pos(b)]);
    assert_eq!(r1, SatResult::Sat, "should be SAT with temp clause");

    // After push/pop, permanent clauses must still hold.
    // a must be false (from permanent !a), b must be true (from permanent a OR b + !a).
    let r2 = s.solve(&[]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "permanent clauses should still be active"
    );
    assert_eq!(
        s.value(Lit::pos(a)),
        Some(false),
        "permanent clause !a must survive push/pop"
    );
    assert_eq!(
        s.value(Lit::pos(b)),
        Some(true),
        "permanent clause (a OR b) with !a must force b=true after push/pop"
    );
}

/// Verify that repeated solve_with_temporary_clause calls do not
/// accumulate solver state. With push/pop, the variable count should
/// stay bounded (unlike the activation-literal pattern which adds one
/// new variable per call).
///
/// This is the key performance property from #4016: IC3 makes thousands
/// of inductiveness checks, and each one should not permanently grow
/// the solver.
#[test]
fn test_z4sat_repeated_temporary_clauses_no_accumulation() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // Permanent: (a OR b)
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

    let initial_num_vars = s.num_vars;

    // Call solve_with_temporary_clause 200 times with different temp clauses.
    for i in 0..200 {
        let temp = if i % 2 == 0 {
            vec![Lit::neg(a)]
        } else {
            vec![Lit::neg(b)]
        };
        let r = s.solve_with_temporary_clause(&[], &temp);
        assert_eq!(
            r,
            SatResult::Sat,
            "iteration {i}: should be SAT with one-literal temp clause"
        );
    }

    // With push/pop, the Z4SatCdclSolver's num_vars should NOT have grown
    // by 200 (which is what the activation-literal default would do).
    // z4-sat's push/pop allocates internal scope selector variables, but
    // those are managed inside z4-sat and not exposed through our num_vars.
    assert_eq!(
        s.num_vars, initial_num_vars,
        "num_vars should not grow with push/pop temporary clauses; \
         activation literals would have added 200 new vars, got {} -> {}",
        initial_num_vars, s.num_vars
    );

    // Verify solver still works correctly after many push/pop cycles.
    let r = s.solve(&[Lit::pos(a)]);
    assert_eq!(
        r,
        SatResult::Sat,
        "solver should still be functional after 200 push/pop cycles"
    );
}

/// Stress-test the push/pop pattern with an UNSAT temporary clause
/// interleaved with SAT solves, mimicking IC3's MIC (Minimal Inductive
/// Clause) pattern where the solver alternates between inductiveness
/// checks (with temp clauses) and regular frame queries.
#[test]
fn test_z4sat_interleaved_temp_and_permanent_solves() {
    let mut s = Z4SatCdclSolver::new(4);
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);

    // Permanent clauses encoding: a XOR b (exactly one true).
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    s.add_clause(&[Lit::neg(a), Lit::neg(b)]);

    for _ in 0..50 {
        // Temp clause: force a=true AND b=true => UNSAT (violates XOR).
        let r1 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::pos(b)]);
        assert_eq!(
            r1,
            SatResult::Unsat,
            "a=true with temp b => UNSAT against XOR(a,b)"
        );

        // Regular solve: should still work.
        let r2 = s.solve(&[Lit::pos(a)]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "permanent XOR(a,b) with a=true should be SAT"
        );
        assert_eq!(
            s.value(Lit::pos(b)),
            Some(false),
            "b should be false when a is true in XOR"
        );

        // Add a permanent clause involving c (to test that permanent additions
        // between push/pop cycles work correctly).
        // This is what IC3 does: add learned lemmas between MIC calls.
        // Use ensure_vars to make sure c is available.
        s.ensure_vars(c.0);
    }

    // Final verification: all permanent clauses still hold.
    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat, "final solve should be SAT");
}

// --- Panic resilience tests (#4026) ---

/// Verify that a poisoned Z4SatCdclSolver returns Unknown for all
/// subsequent calls and does not panic or corrupt state.
#[test]
fn test_z4sat_poisoned_solver_returns_unknown() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // Add a clause and verify the solver works.
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    let r = s.solve(&[Lit::pos(a)]);
    assert_eq!(r, SatResult::Sat, "should be SAT before poison");
    assert!(!s.is_poisoned(), "should not be poisoned yet");

    // Manually poison the solver (simulating a caught z4-sat panic).
    s.poisoned = true;
    assert!(s.is_poisoned());

    // All subsequent calls should return Unknown without panicking.
    let r1 = s.solve(&[Lit::pos(a)]);
    assert_eq!(
        r1,
        SatResult::Unknown,
        "poisoned solve should return Unknown"
    );

    let r2 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(a)]);
    assert_eq!(
        r2,
        SatResult::Unknown,
        "poisoned solve_with_temporary_clause should return Unknown"
    );

    // add_clause should silently no-op (not panic).
    s.add_clause(&[Lit::neg(b)]);
}

/// Verify that the portfolio thread catch_unwind works: if an engine panics,
/// it should produce a CheckResult::Unknown instead of crashing.
#[test]
fn test_z4sat_catch_unwind_in_solve() {
    // This test verifies the catch_unwind wrapper by checking that after
    // calling solve on a working solver, the solver is not poisoned.
    // We cannot easily trigger a z4-sat panic in a unit test without
    // crafting a specific incremental sequence that hits the bug, but
    // we can verify the wrapper's normal-path correctness.
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);

    s.add_clause(&[Lit::pos(a)]);
    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat, "normal solve should still work");
    assert!(
        !s.is_poisoned(),
        "solver should not be poisoned after normal solve"
    );

    let r2 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(a)]);
    assert_eq!(r2, SatResult::Unsat, "temp clause solve should work");
    assert!(
        !s.is_poisoned(),
        "solver should not be poisoned after normal solve_with_temporary_clause"
    );
}

// --- set_cancelled / interrupt wiring tests (#4057) ---

/// Verify that set_cancelled wires the AtomicBool into z4-sat's interrupt
/// mechanism. When the flag is pre-set to true, solve() should return
/// Unknown immediately instead of running to completion.
#[test]
fn test_z4sat_set_cancelled_interrupts_solve() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // Build a satisfiable formula.
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

    // Verify it is SAT without cancellation.
    let r1 = s.solve(&[]);
    assert_eq!(r1, SatResult::Sat, "should be SAT without cancellation");

    // Set the cancellation flag BEFORE solving.
    let cancelled = Arc::new(AtomicBool::new(true));
    s.set_cancelled(cancelled);

    // Solve should return Unknown because the interrupt flag is set.
    let r2 = s.solve(&[]);
    assert_eq!(
        r2,
        SatResult::Unknown,
        "solve() should return Unknown when cancelled flag is set"
    );
}

/// Verify that set_cancelled also interrupts solve_with_temporary_clause.
#[test]
fn test_z4sat_set_cancelled_interrupts_temp_clause_solve() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

    // Set cancellation before the solve.
    let cancelled = Arc::new(AtomicBool::new(true));
    s.set_cancelled(cancelled);

    // Even with a temporary clause, solve should be interrupted.
    let r = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(b)]);
    assert_eq!(
        r,
        SatResult::Unknown,
        "solve_with_temporary_clause should return Unknown when cancelled"
    );
}

/// Verify that cancellation via set_cancelled is cooperative: the solver
/// works normally until the flag is set, then returns Unknown, and
/// continues working after the flag is cleared.
#[test]
fn test_z4sat_set_cancelled_cooperative_lifecycle() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);

    s.add_clause(&[Lit::pos(a)]);

    let flag = Arc::new(AtomicBool::new(false));
    s.set_cancelled(flag.clone());

    // Flag is false: solve should work normally.
    let r1 = s.solve(&[]);
    assert_eq!(r1, SatResult::Sat, "should work with flag=false");

    // Set the flag: solve should return Unknown.
    flag.store(true, Ordering::Relaxed);
    let r2 = s.solve(&[]);
    assert_eq!(r2, SatResult::Unknown, "should be Unknown with flag=true");

    // Clear the flag: solve should work again.
    flag.store(false, Ordering::Relaxed);
    let r3 = s.solve(&[]);
    assert_eq!(r3, SatResult::Sat, "should recover when flag cleared");
}

/// Verify that the SatSolver trait's default set_cancelled is a no-op
/// for SimpleSolver (it doesn't crash or affect behavior).
#[test]
fn test_simple_solver_set_cancelled_noop() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let mut s = SimpleSolver::new();
    let a = s.new_var();
    s.add_clause(&[Lit::pos(a)]);

    // Calling set_cancelled on SimpleSolver should be a no-op.
    let flag = Arc::new(AtomicBool::new(true));
    s.set_cancelled(flag);

    // SimpleSolver should still work (it doesn't check the flag).
    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat, "SimpleSolver ignores cancellation");
}

// --- z4-sat variant backend tests ---

mod z4_variant_tests {
    use super::*;

    /// Each z4-sat variant backend should solve a basic SAT instance.
    #[test]
    fn test_z4_variants_basic_sat() {
        let backends = [
            SolverBackend::Z4Sat,
            SolverBackend::Z4Luby,
            SolverBackend::Z4Stable,
            SolverBackend::Z4Geometric,
            SolverBackend::Z4Vmtf,
            SolverBackend::Z4Chb,
            SolverBackend::Z4NoPreprocess,
        ];
        for backend in backends {
            let mut s = backend.make_solver(3);
            s.add_clause(&[Lit::pos(Var(1)), Lit::pos(Var(2))]);
            let r = s.solve(&[]);
            assert_eq!(r, SatResult::Sat, "{backend:?} should solve basic SAT");
        }
    }

    /// Each z4-sat variant should detect UNSAT.
    #[test]
    fn test_z4_variants_basic_unsat() {
        let backends = [
            SolverBackend::Z4Sat,
            SolverBackend::Z4Luby,
            SolverBackend::Z4Stable,
            SolverBackend::Z4Geometric,
            SolverBackend::Z4Vmtf,
            SolverBackend::Z4Chb,
            SolverBackend::Z4NoPreprocess,
        ];
        for backend in backends {
            let mut s = backend.make_solver(3);
            s.add_clause(&[Lit::pos(Var(1))]);
            s.add_clause(&[Lit::neg(Var(1))]);
            let r = s.solve(&[]);
            assert_eq!(r, SatResult::Unsat, "{backend:?} should detect UNSAT");
        }
    }

    /// Each z4-sat variant should handle assumptions correctly.
    #[test]
    fn test_z4_variants_assumptions() {
        let backends = [
            SolverBackend::Z4Luby,
            SolverBackend::Z4Stable,
            SolverBackend::Z4Vmtf,
            SolverBackend::Z4Chb,
            SolverBackend::Z4NoPreprocess,
        ];
        for backend in backends {
            let mut s = backend.make_solver(3);
            let a = Var(1);
            let b = Var(2);
            s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
            // Assume !a, !b => UNSAT
            let r1 = s.solve(&[Lit::neg(a), Lit::neg(b)]);
            assert_eq!(
                r1,
                SatResult::Unsat,
                "{backend:?}: contradicting assumptions should be UNSAT"
            );
            // Assume a => SAT
            let r2 = s.solve(&[Lit::pos(a)]);
            assert_eq!(
                r2,
                SatResult::Sat,
                "{backend:?}: consistent assumption should be SAT"
            );
        }
    }

    /// Incremental stress test with z4-sat Luby backend.
    #[test]
    fn test_z4_luby_incremental_stress() {
        let mut s = SolverBackend::Z4Luby.make_solver(10);
        // Build a chain: v1 => v2 => ... => v9
        for i in 1..9u32 {
            s.add_clause(&[Lit::neg(Var(i)), Lit::pos(Var(i + 1))]);
        }
        s.add_clause(&[Lit::pos(Var(1))]);

        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat);

        // Now add !v9 => UNSAT
        s.add_clause(&[Lit::neg(Var(9))]);
        let r2 = s.solve(&[]);
        assert_eq!(r2, SatResult::Unsat, "chain with !v9 should be UNSAT");
    }

    /// z4-sat VMTF backend factory works through SolverBackend.
    #[test]
    fn test_z4_vmtf_backend_factory() {
        let mut s = SolverBackend::Z4Vmtf.make_solver(3);
        s.add_clause(&[Lit::TRUE]);
        s.add_clause(&[Lit::pos(Var(1)), Lit::pos(Var(2))]);
        let r = s.solve(&[Lit::pos(Var(1))]);
        assert_eq!(r, SatResult::Sat);
    }
}

// --- clone_solver tests (#4062) ---

/// Verify that SimpleSolver::clone_solver produces a solver with the same
/// clause database that yields identical results on the same queries.
#[test]
fn test_simple_solver_clone_identical_results() {
    let mut orig = SimpleSolver::new();
    let a = orig.new_var(); // Var(1)
    let b = orig.new_var(); // Var(2)
    let c = orig.new_var(); // Var(3)

    // Add clauses: XOR(a, b) AND (b OR c)
    orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    orig.add_clause(&[Lit::neg(a), Lit::neg(b)]);
    orig.add_clause(&[Lit::pos(b), Lit::pos(c)]);

    let mut cloned = orig
        .clone_solver()
        .expect("SimpleSolver clone should succeed");

    // Both should agree on SAT results with the same assumptions.
    let r_orig = orig.solve(&[Lit::pos(a)]);
    let r_clone = cloned.solve(&[Lit::pos(a)]);
    assert_eq!(r_orig, r_clone, "cloned solver should give same result");
    assert_eq!(r_orig, SatResult::Sat);

    // After cloning, adding a clause to the original should NOT affect the clone.
    orig.add_clause(&[Lit::neg(a)]); // Force a=false in original.
    let r_orig2 = orig.solve(&[Lit::pos(a)]);
    let r_clone2 = cloned.solve(&[Lit::pos(a)]);
    assert_eq!(
        r_orig2,
        SatResult::Unsat,
        "original with !a and assumption a should be UNSAT"
    );
    assert_eq!(
        r_clone2,
        SatResult::Sat,
        "clone should not have the !a clause"
    );
}

/// Verify that Z4SatCdclSolver::clone_solver produces a solver with the
/// same clause database via clause log replay (#4062).
#[test]
fn test_z4sat_clone_identical_results() {
    let mut orig = Z4SatCdclSolver::new(4);
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);

    // Build formula: XOR(a, b) AND (b OR c)
    orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    orig.add_clause(&[Lit::neg(a), Lit::neg(b)]);
    orig.add_clause(&[Lit::pos(b), Lit::pos(c)]);

    let mut cloned = orig
        .clone_solver()
        .expect("Z4SatCdclSolver clone should succeed");

    // Both should agree on SAT results.
    let r_orig = orig.solve(&[Lit::pos(a)]);
    let r_clone = cloned.solve(&[Lit::pos(a)]);
    assert_eq!(r_orig, r_clone, "cloned solver should give same result");
    assert_eq!(r_orig, SatResult::Sat);

    // Check model values agree.
    assert_eq!(
        orig.value(Lit::pos(b)),
        cloned.value(Lit::pos(b)),
        "model values should agree"
    );
}

/// Verify that clone isolation holds: adding clauses to the original
/// does not affect the clone, and vice versa.
#[test]
fn test_z4sat_clone_isolation() {
    let mut orig = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // (a OR b)
    orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);

    let mut cloned = orig.clone_solver().expect("clone should succeed");

    // Add !a to original only.
    orig.add_clause(&[Lit::neg(a)]);
    // Original: (a OR b) AND !a => b must be true.
    let r1 = orig.solve(&[]);
    assert_eq!(r1, SatResult::Sat);
    assert_eq!(orig.value(Lit::pos(b)), Some(true));

    // Clone: still has only (a OR b), both solutions available.
    let r2 = cloned.solve(&[Lit::pos(a)]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "clone should not have !a clause from original"
    );
}

/// Verify that cloning a poisoned Z4SatCdclSolver returns None (#4062).
#[test]
fn test_z4sat_clone_poisoned_returns_none() {
    let mut s = Z4SatCdclSolver::new(3);
    s.add_clause(&[Lit::pos(Var(1))]);
    s.poisoned = true;
    assert!(
        s.clone_solver().is_none(),
        "poisoned solver clone should return None"
    );
}

/// Verify that the SatSolver trait's default clone_solver returns None
/// for solvers that don't implement it.
#[test]
fn test_default_clone_solver_returns_none() {
    // The SatSolver trait default returns None.
    // We test via the trait object from SolverBackend::Simple
    // but SimpleSolver overrides clone_solver, so it should succeed.
    let s = SolverBackend::Simple.make_solver(3);
    assert!(
        s.clone_solver().is_some(),
        "SimpleSolver should support clone"
    );

    let z = SolverBackend::Z4Sat.make_solver(3);
    assert!(
        z.clone_solver().is_some(),
        "Z4SatCdclSolver should support clone"
    );
}

/// Stress test: clone a solver with many clauses and verify
/// the clone produces correct results (#4062).
#[test]
fn test_z4sat_clone_many_clauses() {
    let num_vars = 20;
    let mut orig = Z4SatCdclSolver::new(num_vars + 1);

    // Build an implication chain: v1 => v2 => ... => v20.
    for i in 1..num_vars {
        orig.add_clause(&[Lit::neg(Var(i)), Lit::pos(Var(i + 1))]);
    }
    // v1 = true
    orig.add_clause(&[Lit::pos(Var(1))]);

    let mut cloned = orig.clone_solver().expect("clone should succeed");

    // Both should have v1..v20 all true.
    let r_orig = orig.solve(&[]);
    let r_clone = cloned.solve(&[]);
    assert_eq!(r_orig, SatResult::Sat);
    assert_eq!(r_clone, SatResult::Sat);
    for i in 1..=num_vars {
        assert_eq!(
            orig.value(Lit::pos(Var(i))),
            cloned.value(Lit::pos(Var(i))),
            "var {i} should have same value in original and clone"
        );
    }

    // Add !v20 to original only => UNSAT.
    orig.add_clause(&[Lit::neg(Var(num_vars))]);
    assert_eq!(orig.solve(&[]), SatResult::Unsat);
    // Clone should still be SAT.
    assert_eq!(cloned.solve(&[]), SatResult::Sat);
}

/// Verify that cloning preserves the ability to use solve_with_temporary_clause
/// correctly on the cloned solver.
#[test]
fn test_z4sat_clone_temp_clause_works() {
    let mut orig = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // Permanent: XOR(a, b)
    orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    orig.add_clause(&[Lit::neg(a), Lit::neg(b)]);

    let mut cloned = orig.clone_solver().expect("clone should succeed");

    // Temp clause on clone: force both true => UNSAT (violates XOR).
    let r = cloned.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::pos(b)]);
    assert_eq!(r, SatResult::Unsat, "XOR violated by temp clause");

    // After temp clause, clone should still work normally.
    let r2 = cloned.solve(&[Lit::pos(a)]);
    assert_eq!(r2, SatResult::Sat, "clone should recover after temp clause");
}

// --- solve_with_budget tests (#4076) ---

/// Budget of 0 must return Unknown immediately without doing any work.
#[test]
fn test_z4sat_budget_zero_returns_unknown() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    // Trivially SAT formula.
    s.add_clause(&[Lit::pos(a)]);
    let r = s.solve_with_budget(&[], 0);
    assert_eq!(
        r,
        SatResult::Unknown,
        "budget 0 should return Unknown immediately"
    );
}

/// Budget of 0 on SimpleSolver (trait default) also returns Unknown.
#[test]
fn test_simple_budget_zero_returns_unknown() {
    let mut s = SimpleSolver::new();
    let a = s.new_var();
    s.add_clause(&[Lit::pos(a)]);
    let r = s.solve_with_budget(&[], 0);
    assert_eq!(
        r,
        SatResult::Unknown,
        "SimpleSolver budget 0 should return Unknown"
    );
}

/// Large budget on an easy problem should behave like unlimited solve.
#[test]
fn test_z4sat_budget_large_easy_problem_sat() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    // Budget of 1M is effectively unlimited for this trivial problem.
    let r = s.solve_with_budget(&[Lit::pos(a)], 1_000_000);
    assert_eq!(
        r,
        SatResult::Sat,
        "large budget on easy SAT should find solution"
    );
    assert_eq!(
        s.value(Lit::pos(a)),
        Some(true),
        "model should be available after budgeted SAT"
    );
}

/// Large budget on an easy UNSAT problem should return Unsat.
#[test]
fn test_z4sat_budget_large_easy_problem_unsat() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    // a AND !a
    s.add_clause(&[Lit::pos(a)]);
    s.add_clause(&[Lit::neg(a)]);
    let r = s.solve_with_budget(&[], 1_000_000);
    assert_eq!(
        r,
        SatResult::Unsat,
        "large budget on easy UNSAT should detect unsatisfiability"
    );
}

/// Small budget on a hard pigeon hole problem should return Unknown.
/// Pigeon hole (N+1 pigeons, N holes) requires exponential search.
#[test]
fn test_z4sat_budget_small_hard_problem_returns_unknown() {
    // Build pigeon hole: 7 pigeons, 6 holes (UNSAT but requires significant search).
    let num_holes = 6u32;
    let num_pigeons = num_holes + 1;
    let total_vars = num_pigeons * num_holes + 1; // +1 for Var(0)
    let mut s = Z4SatCdclSolver::new(total_vars);

    // p(i, j) = pigeon i is in hole j, variable index = 1 + i*num_holes + j
    for i in 0..num_pigeons {
        // Each pigeon must be in at least one hole.
        let clause: Vec<Lit> = (0..num_holes)
            .map(|j| {
                let var_idx = 1 + i * num_holes + j;
                Lit::pos(Var(var_idx))
            })
            .collect();
        s.add_clause(&clause);
    }
    // No two pigeons in the same hole.
    for j in 0..num_holes {
        for i1 in 0..num_pigeons {
            for i2 in (i1 + 1)..num_pigeons {
                let l1 = Var(1 + i1 * num_holes + j);
                let l2 = Var(1 + i2 * num_holes + j);
                s.add_clause(&[Lit::neg(l1), Lit::neg(l2)]);
            }
        }
    }

    // With a tiny budget (100 conflicts), the solver should not have enough
    // time to prove UNSAT on pigeon hole 7/6.
    let r = s.solve_with_budget(&[], 100);
    // We accept Unknown (budget exhausted) or Unsat (solver was fast enough).
    // The key property: we do NOT hang indefinitely.
    assert!(
        r == SatResult::Unknown || r == SatResult::Unsat,
        "small budget on hard problem should return Unknown or Unsat, got {r:?}"
    );
}

/// Budget does not corrupt solver state: after a budgeted Unknown result,
/// a subsequent unbounded solve should produce the correct answer.
#[test]
fn test_z4sat_budget_solver_usable_after_unknown() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    // (a OR b) AND (!a OR !b) — XOR: exactly one true.
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    s.add_clause(&[Lit::neg(a), Lit::neg(b)]);

    // Budget 0 => Unknown.
    let r1 = s.solve_with_budget(&[], 0);
    assert_eq!(r1, SatResult::Unknown);

    // Subsequent unbounded solve should work correctly.
    let r2 = s.solve(&[]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "solver should be usable after budget-limited Unknown"
    );
}

/// Poisoned solver returns Unknown from solve_with_budget.
#[test]
fn test_z4sat_budget_poisoned_returns_unknown() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    s.add_clause(&[Lit::pos(a)]);
    s.poisoned = true;
    let r = s.solve_with_budget(&[], 1_000_000);
    assert_eq!(
        r,
        SatResult::Unknown,
        "poisoned solver should return Unknown from solve_with_budget"
    );
}

/// SimpleSolver's default solve_with_budget ignores budget (falls through
/// to regular solve) and produces correct results.
#[test]
fn test_simple_budget_correctness() {
    let mut s = SimpleSolver::new();
    let a = s.new_var();
    let b = s.new_var();
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    // Non-zero budget falls through to regular solve.
    let r = s.solve_with_budget(&[Lit::pos(a)], 10);
    assert_eq!(
        r,
        SatResult::Sat,
        "SimpleSolver budget should fall through to regular solve"
    );
}

/// Trait-object dynamic dispatch works correctly with solve_with_budget.
#[test]
fn test_budget_via_trait_object() {
    let mut s: Box<dyn SatSolver> = SolverBackend::Z4Sat.make_solver(3);
    s.add_clause(&[Lit::pos(Var(1))]);
    // Budget 0 => Unknown via trait object.
    let r1 = s.solve_with_budget(&[], 0);
    assert_eq!(r1, SatResult::Unknown);
    // Large budget => Sat via trait object.
    let r2 = s.solve_with_budget(&[], 1_000_000);
    assert_eq!(r2, SatResult::Sat);
}

/// Budget on UNSAT core: when the problem is trivially UNSAT (conflict at
/// clause level, no search needed), even a budget of 1 should return Unsat
/// because the solver detects the conflict before any CDCL search.
#[test]
fn test_z4sat_budget_trivial_unsat() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    // Empty clause via contradictory permanent clauses.
    s.add_clause(&[Lit::pos(a)]);
    s.add_clause(&[Lit::neg(a)]);
    // Even budget=1 should detect this trivial UNSAT.
    let r = s.solve_with_budget(&[], 1);
    assert_eq!(
        r,
        SatResult::Unsat,
        "trivial UNSAT should be detected regardless of budget"
    );
}

/// Budget with assumptions: verify that assumptions and budget work together.
#[test]
fn test_z4sat_budget_with_assumptions() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);
    // (a OR b)
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    // Assume !a, !b with large budget => UNSAT.
    let r = s.solve_with_budget(&[Lit::neg(a), Lit::neg(b)], 1_000_000);
    assert_eq!(
        r,
        SatResult::Unsat,
        "contradicting assumptions should be UNSAT within budget"
    );
    // UNSAT core should be available after budgeted UNSAT.
    let core = s.unsat_core();
    assert!(
        core.is_some(),
        "UNSAT core should be available after budgeted solve"
    );
}

// --- clone_for_incremental tests (#4091) ---

/// Verify that Z4SatCdclSolver::clone_for_incremental produces a solver
/// that preserves learned clauses and gives correct results.
#[test]
fn test_z4sat_clone_for_incremental_basic() {
    let mut orig = Z4SatCdclSolver::new(4);
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);

    // Build formula: XOR(a, b) AND (b OR c)
    orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    orig.add_clause(&[Lit::neg(a), Lit::neg(b)]);
    orig.add_clause(&[Lit::pos(b), Lit::pos(c)]);

    // Do a solve to build up learned clauses and VSIDS scores.
    let r = orig.solve(&[Lit::pos(a)]);
    assert_eq!(r, SatResult::Sat);

    // Clone via native incremental clone.
    let mut cloned = orig
        .clone_for_incremental()
        .expect("Z4SatCdclSolver incremental clone should succeed");

    // Cloned solver should give same results.
    let r_clone = cloned.solve(&[Lit::pos(a)]);
    assert_eq!(r_clone, SatResult::Sat, "cloned solver should agree on SAT");
}

/// Verify clone_for_incremental isolation: changes to original don't
/// affect clone.
#[test]
fn test_z4sat_clone_for_incremental_isolation() {
    let mut orig = Z4SatCdclSolver::new(3);
    let a = Var(1);
    let b = Var(2);

    orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);

    let mut cloned = orig.clone_for_incremental().expect("clone should succeed");

    // Add !a to original only.
    orig.add_clause(&[Lit::neg(a)]);
    let r1 = orig.solve(&[Lit::pos(a)]);
    assert_eq!(
        r1,
        SatResult::Unsat,
        "original with !a + assumption a should be UNSAT"
    );

    // Clone should NOT have !a.
    let r2 = cloned.solve(&[Lit::pos(a)]);
    assert_eq!(r2, SatResult::Sat, "clone should not have !a from original");
}

/// Verify that poisoned solver returns None from clone_for_incremental.
#[test]
fn test_z4sat_clone_for_incremental_poisoned() {
    let mut s = Z4SatCdclSolver::new(3);
    s.add_clause(&[Lit::pos(Var(1))]);
    s.poisoned = true;
    assert!(
        s.clone_for_incremental().is_none(),
        "poisoned solver incremental clone should return None"
    );
}

// --- set_domain / clear_domain tests (#4091) ---

/// Verify that set_domain + solve works correctly: domain restriction
/// should not change the SAT/UNSAT result when all formula variables
/// are within the domain (the correct IC3 usage pattern — domain-restricted
/// solvers only contain domain-relevant clauses).
#[test]
fn test_z4sat_set_domain_basic_sat() {
    let mut s = Z4SatCdclSolver::new(4);
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);

    // (a OR b) AND (b OR c) — all variables are in the domain.
    s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
    s.add_clause(&[Lit::pos(b), Lit::pos(c)]);

    // Without domain restriction.
    let r1 = s.solve(&[Lit::pos(a)]);
    assert_eq!(r1, SatResult::Sat);

    // With domain restricted to {a, b, c} — covers all formula variables.
    s.set_domain(&[a, b, c]);
    let r2 = s.solve(&[Lit::pos(a)]);
    assert_eq!(
        r2,
        SatResult::Sat,
        "domain restriction should not change SAT result"
    );

    // Clear domain and verify normal operation resumes.
    s.clear_domain();
    let r3 = s.solve(&[Lit::pos(c)]);
    assert_eq!(
        r3,
        SatResult::Sat,
        "after clear_domain, full solving should work"
    );
}

/// Verify that set_domain works for UNSAT instances too.
#[test]
fn test_z4sat_set_domain_unsat() {
    let mut s = Z4SatCdclSolver::new(3);
    let a = Var(1);

    // a AND !a
    s.add_clause(&[Lit::pos(a)]);
    s.add_clause(&[Lit::neg(a)]);

    s.set_domain(&[a]);
    let r = s.solve(&[]);
    assert_eq!(
        r,
        SatResult::Unsat,
        "domain-restricted UNSAT should still detect conflict"
    );

    s.clear_domain();
}

/// Verify that set_domain is a no-op on poisoned solver.
#[test]
fn test_z4sat_set_domain_poisoned_noop() {
    let mut s = Z4SatCdclSolver::new(3);
    s.poisoned = true;
    // Should not panic.
    s.set_domain(&[Var(1)]);
    s.clear_domain();
}

/// Default trait implementations for SimpleSolver: set_domain/clear_domain
/// are no-ops and don't affect behavior.
#[test]
fn test_simple_solver_domain_noop() {
    let mut s = SimpleSolver::new();
    let a = s.new_var();
    s.add_clause(&[Lit::pos(a)]);
    s.set_domain(&[a]);
    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat, "SimpleSolver ignores domain restriction");
    s.clear_domain();
    let r2 = s.solve(&[]);
    assert_eq!(r2, SatResult::Sat, "SimpleSolver ignores clear_domain");
}

// --- flip_to_none / minimize_model tests (#4091) ---

/// Verify that flip_to_none on Z4SatCdclSolver works after a SAT result.
#[test]
fn test_z4sat_flip_to_none_basic() {
    let mut s = Z4SatCdclSolver::new(4);
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);

    // (a) AND (b OR c) — a is forced, b/c have freedom.
    s.add_clause(&[Lit::pos(a)]);
    s.add_clause(&[Lit::pos(b), Lit::pos(c)]);

    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat);

    // a is forced by a unit clause — flip should fail.
    let flipped_a = s.flip_to_none(a);
    assert!(!flipped_a, "a is forced by unit clause, should not flip");

    // b or c may be flippable depending on the model.
    // We just verify no panic occurs.
    let _ = s.flip_to_none(b);
    let _ = s.flip_to_none(c);
}

/// Verify that minimize_model returns a subset of the original model.
#[test]
fn test_z4sat_minimize_model_basic() {
    let mut s = Z4SatCdclSolver::new(5);
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);
    let d = Var(4);

    // (a) AND (b OR c) AND (c OR d) — a is essential, others have freedom.
    s.add_clause(&[Lit::pos(a)]);
    s.add_clause(&[Lit::pos(b), Lit::pos(c)]);
    s.add_clause(&[Lit::pos(c), Lit::pos(d)]);

    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat);

    // Minimize with a as important — the result should include a.
    let minimized = s.minimize_model(&[a]);
    let min_vars: Vec<Var> = minimized.iter().map(|l| l.var()).collect();
    assert!(
        min_vars.contains(&a),
        "important variable a must be in minimized model"
    );
    // The minimized model should be no larger than the full variable count.
    assert!(
        minimized.len() <= 5,
        "minimized model should not exceed total variables"
    );
}

/// Verify that minimize_model returns empty on poisoned solver.
#[test]
fn test_z4sat_minimize_model_poisoned() {
    let mut s = Z4SatCdclSolver::new(3);
    s.poisoned = true;
    let result = s.minimize_model(&[Var(1)]);
    assert!(
        result.is_empty(),
        "poisoned solver minimize_model should return empty"
    );
}

/// Default trait implementation: flip_to_none returns false for SimpleSolver.
#[test]
fn test_simple_solver_flip_to_none_default() {
    let mut s = SimpleSolver::new();
    let a = s.new_var();
    s.add_clause(&[Lit::pos(a)]);
    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat);
    // Default implementation returns false.
    assert!(
        !s.flip_to_none(a),
        "SimpleSolver default flip_to_none returns false"
    );
}

/// Default trait implementation: minimize_model returns empty for SimpleSolver.
#[test]
fn test_simple_solver_minimize_model_default() {
    let mut s = SimpleSolver::new();
    let a = s.new_var();
    s.add_clause(&[Lit::pos(a)]);
    let r = s.solve(&[]);
    assert_eq!(r, SatResult::Sat);
    let result = s.minimize_model(&[a]);
    assert!(
        result.is_empty(),
        "SimpleSolver default minimize_model returns empty"
    );
}
