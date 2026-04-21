// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the solve module: model verification fail-closed behavior.

use super::super::*;

/// Helper: build a solver with clause (x0 v x1) and no reconstruction.
/// Both variables are non-eliminated, so the repair pass (#5522) has
/// nothing to flip. With default vals (both false), (x0 v x1) is
/// unsatisfied and verify_against_original catches it.
fn make_unrepairable_model_solver() -> (Solver, Literal, Literal) {
    let mut solver: Solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    solver.add_clause(vec![x0, x1]);
    (solver, x0, x1)
}

/// Helper: build a solver where reconstruction runs but the model
/// is still unrepairable. Clause_db has (x0 v x1) — consistent.
/// original_clauses gets an extra (x2) injected directly — simulating
/// a clause lost during preprocessing. x2 is non-eliminated with
/// val=false, so (x2) is unsatisfied and repair can't flip it.
fn make_unrepairable_reconstruction_solver() -> (Solver, Literal, Literal) {
    let mut solver: Solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    solver.add_clause(vec![x0, x1]);
    solver
        .inproc
        .reconstruction
        .push_witness_clause(vec![x0.negated()], vec![x0.negated()]);
    // Inject clause only in original_ledger (not clause_db).
    solver.cold.original_ledger.push_clause(&[x2]);
    (solver, x0, x1)
}

// verify_against_original checks the immutable original formula and
// the repair pass (#5522) tries to fix models by flipping eliminated
// vars. Tests use unrepairable scenarios (no eliminated vars to flip,
// or non-eliminated vars unsatisfied) to verify the fail-closed path.

#[test]
fn test_invalid_sat_model_fails_closed_to_unknown() {
    let (mut solver, _x0, _x1) = make_unrepairable_model_solver();

    // With uninitialized vals (both false), (x0 v x1) is unsatisfied.
    // No eliminated variables → repair pass cannot fix it.
    // verify_against_original catches the violation → Unknown.
    let result = solver.declare_sat_from_model(vec![true, false]);
    assert_eq!(result, SatResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
    );
    // #7917: detail string must explain which clause failed.
    let detail = solver
        .last_unknown_detail()
        .expect("last_unknown_detail should be populated on InvalidSatModel");
    assert!(
        detail.contains("original clause"),
        "detail should identify the unsatisfied original clause, got: {detail}",
    );
}

#[test]
fn test_invalid_assume_sat_model_fails_closed_to_unknown() {
    let (mut solver, _x0, _x1) = make_unrepairable_model_solver();

    // Same as above but for assumption-based solving path.
    let result = solver.declare_assume_sat_from_model(vec![true, false]);
    assert_eq!(result, AssumeResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
    );
    // #7917: detail string must explain which clause failed.
    let detail = solver
        .last_unknown_detail()
        .expect("last_unknown_detail should be populated on InvalidSatModel");
    assert!(
        detail.contains("original clause"),
        "detail should identify the unsatisfied original clause, got: {detail}",
    );
}

#[test]
fn test_reconstruction_panic_fails_closed_to_unknown() {
    let (mut solver, _x0, _x1) = make_unrepairable_reconstruction_solver();

    // Clause_db has (x0 v x1) — consistent. But original_clauses has
    // an extra (x2) with x2 non-eliminated and val=false.
    // Reconstruction runs, repair pass tries, but can't fix (x2).
    // verify_against_original catches the violation → Unknown.
    let result = solver.declare_sat_from_model(vec![true, true, false]);
    assert_eq!(result, SatResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
    );
    // #7917: detail should mention the failing original clause.
    assert!(
        solver.last_unknown_detail().is_some(),
        "last_unknown_detail should be populated on reconstruction failure",
    );
}

#[test]
fn test_assume_reconstruction_panic_fails_closed_to_unknown() {
    let (mut solver, _x0, _x1) = make_unrepairable_reconstruction_solver();

    // Same as above but for assumption-based solving path.
    let result = solver.declare_assume_sat_from_model(vec![true, true, false]);
    assert_eq!(result, AssumeResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
    );
    // #7917: detail should mention the failing original clause.
    assert!(
        solver.last_unknown_detail().is_some(),
        "last_unknown_detail should be populated on reconstruction failure",
    );
}

#[test]
fn test_solve_no_assumptions_refreshes_num_original_clauses_after_bve() {
    let mut solver = Solver::new(5);
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

    let result = solver.solve_no_assumptions(|| false);
    assert!(
        matches!(result, SatResult::Sat(_)),
        "formula should remain SAT after preprocessing, got {result:?}"
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
        "solve_no_assumptions must refresh num_original_clauses after preprocessing shrink"
    );
}

#[test]
fn test_maybe_run_restart_executes_shared_restart_path() {
    struct RestartProbe {
        restarts: u32,
    }

    impl super::theory_callback::TheoryCallback for RestartProbe {
        fn propagate(&mut self, _solver: &mut Solver) -> TheoryPropResult {
            TheoryPropResult::Continue
        }

        fn on_restart(&mut self) -> Vec<Variable> {
            self.restarts += 1;
            Vec::new()
        }
    }

    let mut solver = Solver::new(1);
    let mut callback = RestartProbe { restarts: 0 };

    solver.num_conflicts = solver.cold.restart_min_conflicts;
    solver.conflicts_since_restart = 1;
    solver.stable_mode = true;
    solver.cold.reluctant_countdown = 1;
    solver.cold.reluctant_ticked_at = solver.num_conflicts - 1;

    assert!(
        solver.maybe_run_restart(&mut callback),
        "helper should execute a pending stable-mode restart",
    );
    assert_eq!(callback.restarts, 1, "restart callback should fire once");
    assert_eq!(
        solver.num_restarts(),
        1,
        "solver restart counter should advance"
    );
    assert_eq!(
        solver.conflicts_since_restart, 0,
        "restart should reset the conflict-since-restart counter",
    );
}

// ---------------------------------------------------------------------------
// JIT BCP integration tests
// ---------------------------------------------------------------------------

#[cfg(feature = "jit")]
mod jit_tests {
    use crate::{Literal, SatResult, Solver, Variable};

    /// Helper: verify a model satisfies a set of clauses.
    fn verify_model(model: &[bool], clauses: &[Vec<Literal>]) {
        for (i, clause) in clauses.iter().enumerate() {
            let satisfied = clause.iter().any(|lit| {
                let val = model[lit.variable().index()];
                if lit.is_positive() { val } else { !val }
            });
            assert!(
                satisfied,
                "clause {i} unsatisfied: {clause:?}, model: {model:?}"
            );
        }
    }

    #[test]
    fn test_jit_simple_sat() {
        let mut s = Solver::new(0);
        let v0 = s.new_var();
        let v1 = s.new_var();

        let clauses = vec![
            vec![Literal::positive(v0), Literal::positive(v1)],
            vec![Literal::negative(v0), Literal::positive(v1)],
            vec![Literal::positive(v0), Literal::negative(v1)],
        ];
        for c in &clauses {
            s.add_clause(c.clone());
        }

        match s.solve().into_inner() {
            SatResult::Sat(model) => verify_model(&model, &clauses),
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    #[test]
    fn test_jit_simple_unsat() {
        // All 8 sign-combinations of 3 variables => UNSAT
        let mut s = Solver::new(0);
        let v: Vec<_> = (0..3).map(|_| s.new_var()).collect();

        for mask in 0..8u32 {
            let clause: Vec<_> = (0..3)
                .map(|i| {
                    if mask & (1 << i) != 0 {
                        Literal::positive(v[i])
                    } else {
                        Literal::negative(v[i])
                    }
                })
                .collect();
            s.add_clause(clause);
        }

        match s.solve().into_inner() {
            SatResult::Unsat => {}
            other => panic!("expected UNSAT, got {other:?}"),
        }
    }

    #[test]
    fn test_jit_pigeonhole_3_2() {
        let mut s = Solver::new(0);
        let vars: Vec<Vec<Variable>> = (0..3)
            .map(|_| (0..2).map(|_| s.new_var()).collect())
            .collect();

        for pigeon in &vars {
            s.add_clause(vec![
                Literal::positive(pigeon[0]),
                Literal::positive(pigeon[1]),
            ]);
        }

        for hole in 0..2 {
            for i in 0..3 {
                for k in (i + 1)..3 {
                    s.add_clause(vec![
                        Literal::negative(vars[i][hole]),
                        Literal::negative(vars[k][hole]),
                    ]);
                }
            }
        }

        match s.solve().into_inner() {
            SatResult::Unsat => {}
            other => panic!("expected UNSAT for pigeonhole(3,2), got {other:?}"),
        }
    }

    #[test]
    fn test_jit_propagation_chain() {
        let n = 10;
        let mut s = Solver::new(0);
        let v: Vec<_> = (0..n).map(|_| s.new_var()).collect();

        s.add_clause(vec![Literal::positive(v[0])]);

        let mut clauses = vec![vec![Literal::positive(v[0])]];
        for i in 0..(n - 1) {
            let c = vec![Literal::negative(v[i]), Literal::positive(v[i + 1])];
            s.add_clause(c.clone());
            clauses.push(c);
        }

        let final_clause = vec![Literal::positive(v[n - 1])];
        s.add_clause(final_clause.clone());
        clauses.push(final_clause);

        match s.solve().into_inner() {
            SatResult::Sat(model) => {
                verify_model(&model, &clauses);
                for (i, var) in v.iter().enumerate() {
                    assert!(
                        model[var.index()],
                        "x{i} should be true in the propagation chain model",
                    );
                }
            }
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    #[test]
    fn test_jit_medium_random_3sat() {
        let num_vars = 20;
        let mut s = Solver::new(0);
        let v: Vec<_> = (0..num_vars).map(|_| s.new_var()).collect();

        let known_model: Vec<bool> = (0..num_vars).map(|i| i % 2 == 0).collect();

        let mut clauses = Vec::new();
        for base in 0..num_vars {
            for offset in [1, 3, 7] {
                let i0 = base;
                let i1 = (base + offset) % num_vars;
                let i2 = (base + offset * 2) % num_vars;

                let l0 = if known_model[i0] {
                    Literal::positive(v[i0])
                } else {
                    Literal::negative(v[i0])
                };
                let l1 = if (base + offset) % 3 == 0 {
                    Literal::positive(v[i1])
                } else {
                    Literal::negative(v[i1])
                };
                let l2 = if (base * offset) % 5 < 3 {
                    Literal::positive(v[i2])
                } else {
                    Literal::negative(v[i2])
                };

                let clause = vec![l0, l1, l2];
                s.add_clause(clause.clone());
                clauses.push(clause);
            }
        }

        match s.solve().into_inner() {
            SatResult::Sat(model) => verify_model(&model, &clauses),
            other => panic!("expected SAT for constructed 3-SAT, got {other:?}"),
        }
    }

    #[test]
    fn test_jit_ternary_plus_clauses_sat() {
        let mut s = Solver::new(0);
        let v: Vec<_> = (0..5).map(|_| s.new_var()).collect();

        let clauses = vec![
            vec![Literal::positive(v[0]), Literal::positive(v[1]), Literal::positive(v[2])],
            vec![Literal::negative(v[0]), Literal::positive(v[1]), Literal::negative(v[3])],
            vec![Literal::positive(v[2]), Literal::negative(v[3]), Literal::positive(v[4])],
            vec![Literal::negative(v[1]), Literal::positive(v[3]), Literal::positive(v[4])],
            vec![
                Literal::positive(v[0]),
                Literal::negative(v[1]),
                Literal::positive(v[2]),
                Literal::negative(v[4]),
            ],
            vec![
                Literal::negative(v[0]),
                Literal::positive(v[2]),
                Literal::positive(v[3]),
                Literal::positive(v[4]),
            ],
            vec![
                Literal::negative(v[0]),
                Literal::negative(v[1]),
                Literal::negative(v[2]),
                Literal::negative(v[3]),
                Literal::negative(v[4]),
            ],
        ];

        for c in &clauses {
            s.add_clause(c.clone());
        }

        match s.solve().into_inner() {
            SatResult::Sat(model) => verify_model(&model, &clauses),
            other => panic!("expected SAT for ternary+ clause mix, got {other:?}"),
        }
    }

    #[test]
    fn test_jit_conflict_driven_learning() {
        // At-most-one + forced pair => UNSAT via CDCL
        let mut s = Solver::new(0);
        let v: Vec<_> = (0..4).map(|_| s.new_var()).collect();

        // At-most-one: (~xi | ~xj) for all i < j
        for i in 0..4 {
            for j in (i + 1)..4 {
                s.add_clause(vec![Literal::negative(v[i]), Literal::negative(v[j])]);
            }
        }

        // Force x0=true and x1=true => contradicts (~x0 | ~x1)
        s.add_clause(vec![Literal::positive(v[0])]);
        s.add_clause(vec![Literal::positive(v[1])]);

        match s.solve().into_inner() {
            SatResult::Unsat => {}
            other => panic!("expected UNSAT for at-most-one + forced pair, got {other:?}"),
        }
    }
}
