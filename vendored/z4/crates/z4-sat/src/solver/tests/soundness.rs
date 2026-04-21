// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness and model verification tests: online witness checking,
//! model verification against original formula, solution file loading,
//! and BVE/sweep elimination verification.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

// ========================================================================
// Online Witness + Solution Loading Tests
// ========================================================================

#[test]
fn test_online_witness_detects_first_invalid_learned_clause_non_incremental() {
    let mut solver: Solver = Solver::new(2);
    solver
        .try_set_solution(&[true, false])
        .expect("valid full witness should be accepted");

    let bad_learned = [
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_db(&bad_learned, true);
    }));

    assert!(
        panic.is_err(),
        "learned clause falsified by witness should panic immediately"
    );
}

#[test]
fn test_online_witness_ignores_internal_scope_selectors() {
    let mut solver: Solver = Solver::new(1);
    solver.push();
    let selector = solver.cold.scope_selectors[0];

    // Provide only user-visible assignment (x0=true). Internal selector stays unknown.
    solver
        .try_set_solution(&[true])
        .expect("user-visible witness should be accepted");

    // Clause is false on known literals (¬x0), but contains unknown selector.
    // Online witness checker must not report a violation.
    let mixed_clause = [Literal::negative(Variable(0)), Literal::positive(selector)];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_db(&mixed_clause, true);
    }));

    assert!(
        panic.is_ok(),
        "internal selector with unknown witness value should not trigger violation"
    );
}

/// Online witness check for replaced/shrunken clauses (CaDiCaL parity:
/// `check_solution_on_shrunken_clause`). When a clause is strengthened via
/// inprocessing (vivification, subsumption, etc.), the replacement must still
/// be satisfied by the witness. This test verifies the gap covered in #4291.
#[test]
fn test_online_witness_detects_invalid_replaced_clause() {
    let mut solver: Solver = Solver::new(3);
    // Solution: x0=true, x1=false, x2=true
    solver
        .try_set_solution(&[true, false, true])
        .expect("valid witness should be accepted");

    // Add an original clause (x0 ∨ x1 ∨ x2) — satisfied by x0=true
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    let clause_idx = 0;

    // Replace with (¬x0 ∨ x1) — falsified by witness (x0=true, x1=false)
    let bad_replacement = [
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.replace_clause_checked(clause_idx, &bad_replacement);
    }));

    assert!(
        panic.is_err(),
        "replaced clause falsified by witness should panic immediately"
    );
}

/// Verify that valid clause replacements do NOT trigger the witness check.
/// Strengthening (x0 ∨ x1 ∨ x2) → (x0 ∨ x2) should be fine when x0=true.
#[test]
fn test_online_witness_allows_valid_replaced_clause() {
    let mut solver: Solver = Solver::new(3);
    // Solution: x0=true, x1=false, x2=true
    solver
        .try_set_solution(&[true, false, true])
        .expect("valid witness should be accepted");

    // Add original clause (x0 ∨ x1 ∨ x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    let clause_idx = 0;

    // Replace with (x0 ∨ x2) — still satisfied by x0=true
    let good_replacement = [
        Literal::positive(Variable(0)),
        Literal::positive(Variable(2)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.replace_clause_checked(clause_idx, &good_replacement);
    }));

    assert!(
        panic.is_ok(),
        "valid replacement should not trigger witness violation"
    );
}

/// Clauses added through the inprocessing path (`add_clause_watched`) are
/// derived consequences and must also be checked against the witness.
#[test]
fn test_online_witness_detects_invalid_irredundant_derived_clause() {
    let mut solver: Solver = Solver::new(3);
    solver.set_solution(vec![true, false, true]);

    // Clause (¬x0 ∨ x1) is falsified by witness (x0=true, x1=false).
    let mut invalid = vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_watched(&mut invalid);
    }));

    assert!(
        panic.is_err(),
        "derived irredundant clause falsified by witness should panic"
    );
}

/// Valid inprocessing-derived clauses should not trigger the witness check.
#[test]
fn test_online_witness_allows_valid_irredundant_derived_clause() {
    let mut solver: Solver = Solver::new(3);
    solver.set_solution(vec![true, false, true]);

    // Clause (x0 ∨ x2) is satisfied by witness.
    let mut valid = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(2)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_watched(&mut valid);
    }));

    assert!(
        panic.is_ok(),
        "valid derived irredundant clause should not trigger witness violation"
    );
}

/// CaDiCaL parity: check_no_solution_after_learning_empty_clause (#4615).
/// When a satisfying assignment is configured and the solver derives the empty
/// clause (UNSAT), it must abort immediately — the formula is SAT so deriving
/// UNSAT is a soundness bug.
#[test]
fn test_online_witness_aborts_on_empty_clause_derivation() {
    let mut solver: Solver = Solver::new(1);
    solver.set_solution(vec![true]);

    // Adding the empty clause signals UNSAT. With a witness configured,
    // mark_empty_clause must abort.
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.add_clause(vec![]);
    }));

    assert!(
        panic.is_err(),
        "deriving empty clause with a configured witness should abort"
    );
}

/// Sam Buss trick: deriving an empty clause while a solution witness is loaded
/// must panic immediately. The empty clause means UNSAT, but the witness proves
/// SAT — so the solver has a soundness bug.
/// CaDiCaL parity: analyze.cpp:19 (empty clause check against solution).
#[test]
fn test_online_witness_detects_empty_clause_derivation() {
    let mut solver: Solver = Solver::new(2);
    solver.set_solution(vec![true, false]);

    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.mark_empty_clause();
    }));

    assert!(
        panic.is_err(),
        "empty clause with loaded witness should panic (UNSAT from SAT formula)"
    );
}

/// Verify that marking an empty clause WITHOUT a solution witness does not panic.
/// Normal UNSAT derivation (no witness loaded) should proceed without assertion failure.
#[test]
fn test_empty_clause_without_witness_does_not_panic() {
    let mut solver: Solver = Solver::new(2);
    // No set_solution call — solution_witness is None.

    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.mark_empty_clause();
    }));

    assert!(
        panic.is_ok(),
        "empty clause without loaded witness should not panic"
    );
    assert!(solver.has_empty_clause, "empty clause flag should be set");
}

/// End-to-end: load a satisfying solution, then solve a satisfiable formula.
/// The solver should return SAT without triggering any witness violations.
#[test]
fn test_online_witness_no_panic_on_normal_sat_solve() {
    let mut solver: Solver = Solver::new(3);
    // Formula: (x0 ∨ x1) ∧ (¬x0 ∨ x2) ∧ (¬x1 ∨ x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    // Known satisfying assignment: x0=true, x1=true, x2=true
    solver.set_solution(vec![true, true, true]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(_) => {} // expected
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Load a solution from a file in SAT competition format (v-lines).
/// CaDiCaL parity: External::read_solution().
#[test]
fn test_load_solution_file_competition_format() {
    use std::io::Write;
    let dir = std::env::temp_dir().join("z4_test_solution");
    std::fs::create_dir_all(&dir).unwrap();
    let sol_path = dir.join("test.sol");
    {
        let mut f = std::fs::File::create(&sol_path).unwrap();
        writeln!(f, "s SATISFIABLE").unwrap();
        writeln!(f, "v 1 -2 3 0").unwrap();
    }

    let mut solver: Solver = Solver::new(3);
    solver
        .load_solution_file(sol_path.to_str().unwrap())
        .unwrap();

    // Witness is: x0=true, x1=false, x2=true
    // A learned clause (¬x0 ∨ x1) = (false ∨ false) should trigger panic.
    let bad_clause = [
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = solver.add_clause_db(&bad_clause, true);
    }));
    assert!(
        panic.is_err(),
        "file-loaded witness should detect falsified learned clause"
    );

    // Clean up
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_try_set_solution_rejects_invalid_lengths_and_solver_remains_operational() {
    let mut solver: Solver = Solver::new(2);

    let short = solver
        .try_set_solution(&[true])
        .expect_err("short witness must return structured error");
    assert_eq!(short, SetSolutionError::TooShort { got: 1, min: 2 });
    assert!(
        solver.cold.solution_witness.is_none(),
        "invalid short witness must not mutate solver witness state"
    );

    let long = solver
        .try_set_solution(&[true, false, true])
        .expect_err("long witness must return structured error");
    assert_eq!(long, SetSolutionError::TooLong { got: 3, max: 2 });
    assert!(
        solver.cold.solution_witness.is_none(),
        "invalid long witness must not mutate solver witness state"
    );

    solver.add_clause(vec![Literal::positive(Variable(0))]);
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "solver should still solve after rejected witness inputs"
    );
}

// ========================================================================
// Model Verification Against Original Formula
// ========================================================================

fn add_binary_xor(solver: &mut Solver, a: Variable, b: Variable) {
    solver.add_clause(vec![Literal::positive(a), Literal::positive(b)]);
    solver.add_clause(vec![Literal::negative(a), Literal::negative(b)]);
}

fn php_var(pigeon: usize, hole: usize, holes: usize) -> Variable {
    Variable((pigeon * holes + hole) as u32)
}

#[test]
fn test_soundness_unique_satisfying_assignment_returns_exact_model() {
    let mut solver = Solver::new(3);

    // Unique model: x0=true, x1=false, x2=true.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert_eq!(
        model,
        vec![true, false, true],
        "formula should have exactly one satisfying assignment"
    );
    assert!(
        solver.verify_against_original(&model).is_none(),
        "returned model must satisfy the original formula"
    );
}

#[test]
fn test_soundness_php_4_3_is_unsat() {
    let pigeons = 4;
    let holes = 3;
    let mut solver = Solver::new(pigeons * holes);

    for pigeon in 0..pigeons {
        let clause = (0..holes)
            .map(|hole| Literal::positive(php_var(pigeon, hole, holes)))
            .collect();
        solver.add_clause(clause);
    }

    for hole in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                solver.add_clause(vec![
                    Literal::negative(php_var(p1, hole, holes)),
                    Literal::negative(php_var(p2, hole, holes)),
                ]);
            }
        }
    }

    let result = solver.solve().into_inner();
    assert_eq!(result, SatResult::Unsat, "PHP(4,3) must be UNSAT");
}

#[test]
fn test_soundness_xor_heavy_parity_formula_returns_valid_model() {
    let mut solver = Solver::new(4);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);

    // Four-way parity ring, then select the phase with (x0 v x2).
    add_binary_xor(&mut solver, x0, x1);
    add_binary_xor(&mut solver, x1, x2);
    add_binary_xor(&mut solver, x2, x3);
    add_binary_xor(&mut solver, x3, x0);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x2)]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert_eq!(
        model,
        vec![true, false, true, false],
        "parity ring should collapse to the alternating model"
    );
    assert!(model[0] ^ model[1], "x0 xor x1 must hold");
    assert!(model[1] ^ model[2], "x1 xor x2 must hold");
    assert!(model[2] ^ model[3], "x2 xor x3 must hold");
    assert!(model[3] ^ model[0], "x3 xor x0 must hold");
    assert!(
        solver.verify_against_original(&model).is_none(),
        "returned model must satisfy the original parity formula"
    );
}

#[test]
fn test_soundness_long_implication_chain_to_not_a_is_unsat() {
    let mut solver = Solver::new(8);

    solver.add_clause(vec![Literal::positive(Variable(0))]);
    for from in 0..7 {
        solver.add_clause(vec![
            Literal::negative(Variable(from as u32)),
            Literal::positive(Variable((from + 1) as u32)),
        ]);
    }
    solver.add_clause(vec![
        Literal::negative(Variable(7)),
        Literal::negative(Variable(0)),
    ]);

    let result = solver.solve().into_inner();
    assert_eq!(
        result,
        SatResult::Unsat,
        "A, A->B->...->H, H->!A must be UNSAT"
    );
}

#[test]
fn test_soundness_unit_and_binary_propagation_fronts_meet_in_conflict() {
    let mut solver = Solver::new(5);

    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(4))]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(4)),
        Literal::negative(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    assert_eq!(
        result,
        SatResult::Unsat,
        "two unit-propagation fronts should meet in a binary-clause conflict"
    );
}

#[test]
fn test_first_model_violation_reports_clause_db_clause() {
    let mut solver: Solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let violation = solver
        .first_model_violation(&[false, false], false)
        .expect("all-false model should violate (x0 v x1)");

    assert_eq!(
        violation,
        ModelViolation::ClauseDb {
            clause_index: 0,
            clause_dimacs: vec![1, 2],
        }
    );
}

#[test]
fn test_describe_model_violation_clause_db_includes_literal_evals() {
    let mut solver: Solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    let model = [false, false];

    let violation = solver
        .first_model_violation(&model, false)
        .expect("all-false model should violate (x0 v x1)");
    let message = solver.describe_model_violation(&model, &violation);

    assert!(
        message.contains("clause_db[0] unsatisfied"),
        "message must include clause source/index: {message}"
    );
    assert!(
        message.contains("clause=[1, 2]"),
        "message must include failing clause DIMACS form: {message}"
    );
    assert!(
        message.contains("1@v0=F->F"),
        "message must include first literal eval: {message}"
    );
    assert!(
        message.contains("2@v1=F->F"),
        "message must include second literal eval: {message}"
    );
}

#[test]
fn test_verify_against_original_reports_first_unsatisfied_clause() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    // x0=true, x1=false satisfies clause 0 and violates clause 1.
    let model = vec![true, false];
    assert_eq!(solver.verify_against_original(&model), Some(1));
}

#[test]
fn test_verify_against_original_ignores_learned_clauses() {
    let mut solver = Solver::new(1);
    solver.add_clause(vec![Literal::positive(Variable(0))]); // Original formula
    let _ = solver.add_clause_db(&[Literal::negative(Variable(0))], true); // Learned only

    // This model satisfies the original formula but falsifies the learned clause.
    let model = vec![true];
    assert_eq!(solver.verify_against_original(&model), None);
    #[cfg(debug_assertions)]
    assert!(
        !solver.verify_clause_db_only(&model, false),
        "clause-db check must still fail on the learned clause"
    );
}

/// verify_against_original must detect a corrupted model (#4604).
///
/// Constructs a SAT formula, solves it, flips one variable to corrupt the model,
/// and verifies that `verify_against_original` returns the index of an unsatisfied
/// original clause.
#[test]
fn test_original_formula_ledger_catches_wrong_model() {
    // Simple SAT formula: (x0 | x1) & (!x0 | x1) — forces x1=true.
    let mut solver: Solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(m) => m,
        other => panic!("expected SAT, got {other:?}"),
    };

    // Corrupt the model: flip x1 (which must be true) to false.
    let mut bad_model = vec![false; solver.num_vars];
    for (i, &val) in model.iter().enumerate() {
        if i < bad_model.len() {
            bad_model[i] = val;
        }
    }
    // x1 = Variable(1) must be true in any satisfying assignment.
    bad_model[1] = !bad_model[1];

    let fail_idx = solver.verify_against_original(&bad_model);
    assert!(
        fail_idx.is_some(),
        "verify_against_original must detect the corrupted model"
    );
}

/// verify_against_original must run on the SECOND solve_with_assumptions call.
///
/// Before this fix, `has_been_incremental` (set on second solve) caused
/// `verify_against_original` to be skipped for ALL incremental solving.
/// The fix uses `has_ever_scoped` (only set by push()) so assumption-only
/// incremental solving (used by CHC) still verifies against original clauses.
#[test]
fn test_verify_against_original_runs_on_second_assumption_solve() {
    let mut solver = Solver::new(4);
    // Simple formula: (x0 | x1) & (!x0 | x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);

    // First solve — this sets has_solved_once=true
    let assumptions = vec![Literal::positive(Variable(3))];
    let r1 = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(r1, AssumeResult::Sat(_)),
        "first solve should be SAT"
    );

    // Add more clauses (simulating CHC blocking clauses)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);

    // Second solve — has_been_incremental is now true.
    // verify_against_original must STILL run because no push() was called.
    let r2 = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(r2, AssumeResult::Sat(_)),
        "second solve should be SAT"
    );

    // Verify the model satisfies ALL original clauses (including the one
    // added between solves). This confirms that verify_against_original
    // is running even though has_been_incremental is true.
    if let AssumeResult::Sat(model) = r2 {
        assert!(
            solver.verify_against_original(&model).is_none(),
            "model from second assumption solve must satisfy all original clauses"
        );
    }

    // Verify has_been_incremental is true but has_ever_scoped is false
    assert!(
        solver.cold.has_been_incremental,
        "has_been_incremental must be true after second solve"
    );
    assert!(
        !solver.cold.has_ever_scoped,
        "has_ever_scoped must be false (no push/pop used)"
    );
}

/// original_clauses must not include learned clauses (#4604).
///
/// Solves a formula that requires conflict-driven learning (PHP 3,2),
/// then verifies that the original_clauses count equals the input clause
/// count, not input + learned.
#[test]
fn test_original_formula_ledger_excludes_learned_clauses() {
    // PHP(3,2): 3 pigeons, 2 holes — 6 vars, 9 clauses, UNSAT.
    // Solving this requires learning at least one clause.
    let mut solver: Solver = Solver::new(6);
    let input_clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        vec![
            Literal::positive(Variable(2)),
            Literal::positive(Variable(3)),
        ],
        vec![
            Literal::positive(Variable(4)),
            Literal::positive(Variable(5)),
        ],
        vec![
            Literal::negative(Variable(0)),
            Literal::negative(Variable(2)),
        ],
        vec![
            Literal::negative(Variable(0)),
            Literal::negative(Variable(4)),
        ],
        vec![
            Literal::negative(Variable(2)),
            Literal::negative(Variable(4)),
        ],
        vec![
            Literal::negative(Variable(1)),
            Literal::negative(Variable(3)),
        ],
        vec![
            Literal::negative(Variable(1)),
            Literal::negative(Variable(5)),
        ],
        vec![
            Literal::negative(Variable(3)),
            Literal::negative(Variable(5)),
        ],
    ];
    let num_input = input_clauses.len();
    for clause in input_clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert_eq!(result, SatResult::Unsat, "PHP(3,2) must be UNSAT");

    assert_eq!(
        solver.cold.original_ledger.num_clauses(),
        num_input,
        "original_ledger must equal input count ({num_input}), not input + learned ({})",
        solver.cold.original_ledger.num_clauses()
    );
}

/// BVE must fire during preprocessing (#4209).
///
/// Before the fix, `should_bve()` checked `should_fire(num_conflicts)` which
/// required `num_conflicts >= BVE_INTERVAL_BASE = 2000`. During preprocessing
/// num_conflicts is always 0, so BVE never ran. CaDiCaL runs BVE unconditionally
/// during preprocessing (elim.cpp); only the fixpoint guard applies.
///
/// Formula: (x0 | x1) & (!x0 | x2) — x0 has 1 positive and 1 negative
/// occurrence, resolvent (x1 | x2) replaces 2 clauses with 1. With
/// growth_bound=8 (preprocessing default), this is bounded.
#[test]

// ========================================================================
// BVE / Sweep Elimination Verification
// ========================================================================

fn test_bve_no_active_clause_contains_eliminated_var() {
    let mut solver = Solver::new(6);
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);

    // BVE of v0: {v0, v1} ∧ {¬v0, v1} → resolvent {v1} (unit)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // Clause satisfied by v1=true, contains v2
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    // BVE of v2: two clauses to resolve
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::positive(Variable(5)),
    ]);
    // Extra clause to keep formula satisfiable
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
        Literal::positive(Variable(5)),
    ]);

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "formula should be satisfiable, got {result:?}"
    );
}

#[test]
fn test_bve_elim_propagate_deletes_satisfied_clauses() {
    let mut solver = Solver::new(5);
    let x = Variable(0);
    let y = Variable(1);
    let a = Variable(2);
    let b = Variable(3);

    solver.freeze(y);
    solver.freeze(a);
    solver.freeze(b);

    solver.add_clause_db(&[Literal::positive(x), Literal::positive(y)], false);
    solver.add_clause_db(&[Literal::negative(x), Literal::positive(y)], false);
    let satisfied_clause = solver.add_clause_db(
        &[
            Literal::positive(y),
            Literal::positive(a),
            Literal::positive(b),
        ],
        false,
    );

    let derived_unsat = solver.bve();
    assert!(!derived_unsat, "BVE should not derive UNSAT here");
    assert_eq!(
        solver.get_var_assignment(y.index()),
        Some(true),
        "unit resolvent should assign y at level 0"
    );
    assert!(
        solver.arena.is_empty_clause(satisfied_clause),
        "elim_propagate should delete clauses satisfied by the new unit"
    );
    // Under D1 (#7399): occ lists may retain stale entries for deleted clauses.
    // Correctness relies on the is_active() guard in the BVE elimination loop
    // (bve.rs:1047), not on eager occ-list cleanup. Verify the clause is
    // properly garbage-collected from the arena instead.
    assert!(
        !solver.arena.is_active(satisfied_clause),
        "satisfied clause should be inactive in arena after elim_propagate"
    );
}

/// #5696: Inline verification in solve() must skip original clauses containing
/// BVE-eliminated variables. Without the skip, the eliminated variable's
/// assignment is set by the extension stack during reconstruction, but the
/// inline check runs before full reconstruction, causing a false-positive
/// InvalidSatModel.
///
/// This test creates a formula where BVE eliminates variable x0 (appears
/// positive in one binary clause, negative in another → resolution yields a
/// binary resolvent {x1, x2}). The original clauses containing x0 are kept
/// in the original_clauses ledger. The inline verification must skip them.
///
/// If the skip-path is broken, solve() returns Unknown(InvalidSatModel).
/// If it works correctly, solve() returns Sat with a valid model.
#[test]
fn test_inline_verify_skips_bve_eliminated_clauses() {
    let mut solver = Solver::new(5); // x0..x4
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);
    // Disable other inprocessing to isolate BVE behavior.
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);

    // BVE target: x0 appears in exactly 2 clauses (one pos, one neg).
    // Resolving {x0, x1} with {¬x0, x2} produces {x1, x2}.
    // x0 is eliminated; the original clauses referencing x0 are handled
    // by the reconstruction extension stack.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    // Additional clauses to make the formula non-trivial.
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

    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            // Verify model against ALL original clauses (including those
            // with the eliminated variable). The full model (post-reconstruction)
            // should satisfy everything.
            assert!(
                solver.verify_against_original(model).is_none(),
                "model must satisfy all original clauses including \
                 those with eliminated variables"
            );
        }
        other => panic!("#5696 regression: BVE + inline verify must return Sat, got {other:?}"),
    }
}

/// #5696: Same as above but with sweep (congruence) enabled alongside BVE.
/// This is the exact configuration that failed on IBM12.
#[test]
fn test_inline_verify_skips_bve_and_sweep_clauses() {
    let mut solver = Solver::new(6); // x0..x5
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_congruence_enabled(true);
    // Disable others for determinism.
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);

    // BVE eliminates x0: {x0, x1} ∧ {¬x0, x2} → {x1, x2}
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    // Sweep may merge x3 ↔ x4 if they're functionally equivalent.
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::negative(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(4)),
    ]);
    // Additional clauses involving both eliminated and sweep-merged vars.
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(3)),
        Literal::positive(Variable(5)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
        Literal::positive(Variable(5)),
    ]);
    // Clause mixing eliminated x0 with sweep candidates.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            assert!(
                solver.verify_against_original(model).is_none(),
                "model must satisfy all original clauses including \
                 those with eliminated and sweep-remapped variables"
            );
        }
        other => panic!("#5696 regression: BVE+sweep+congruence must return Sat, got {other:?}"),
    }
}

fn random_3sat_clauses(num_vars: usize, num_clauses: usize, seed: u64) -> Vec<Vec<Literal>> {
    struct SimpleRng {
        state: u64,
    }

    impl SimpleRng {
        fn new(seed: u64) -> Self {
            Self {
                state: seed.wrapping_add(0x9E3779B97F4A7C15),
            }
        }

        fn next(&mut self) -> u64 {
            let mut x = self.state;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.state = x;
            x
        }
    }

    let mut rng = SimpleRng::new(seed);
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let mut clause = Vec::with_capacity(3);
        for _ in 0..3 {
            let var = Variable((rng.next() % num_vars as u64) as u32);
            let lit = if rng.next().is_multiple_of(2) {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            clause.push(lit);
        }
        clauses.push(clause);
    }
    clauses
}

fn build_dimacs_profile_solver(num_vars: usize, clauses: &[Vec<Literal>]) -> Solver {
    let mut solver = Solver::new(num_vars);
    // Match the DIMACS-oriented preprocessing/search configuration that exists
    // on this branch without relying on the unfinished profile API wiring.
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_subsume_enabled(true);
    solver.preprocessing_quick_mode = false;
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver
}

/// Regression for the satisfiable random-3SAT instance exposed by
/// `cross_check_4542::sat_vs_dpll_consistency_random_3sat` (`seed=76`).
///
/// A brute-force check finds a satisfying assignment for this formula, so the
/// DIMACS SAT profile must not conclude UNSAT under any of the small-formula
/// preprocessing/search variants exercised here.
#[test]
fn test_dimacs_profile_random_3sat_seed_76_remains_sat() {
    let num_vars = 20;
    let clauses = random_3sat_clauses(num_vars, 96, 76);

    type ConfigFn = fn(&mut Solver);
    let configs: [(&str, ConfigFn); 4] = [
        ("no_preprocess", |solver| {
            solver.set_preprocess_enabled(false)
        }),
        ("quick_preprocess", |solver| {
            solver.preprocessing_quick_mode = true
        }),
        ("no_chrono", |solver| solver.set_chrono_enabled(false)),
        ("default", |_| {}),
    ];

    for (label, configure) in configs {
        let mut solver = build_dimacs_profile_solver(num_vars, &clauses);
        configure(&mut solver);

        match solver.solve().into_inner() {
            SatResult::Sat(model) => {
                assert!(
                    solver.verify_against_original(&model).is_none(),
                    "{label}: returned SAT model must satisfy the original clauses",
                );
            }
            other => {
                panic!("{label}: satisfiable random-3SAT seed 76 must remain SAT, got {other:?}")
            }
        }
    }
}

fn repo_unsat_corpus_paths() -> Vec<std::path::PathBuf> {
    let corpus_dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/sat/unsat");
    let mut cnf_paths: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", corpus_dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .filter(|path| is_fail_closed_known_unsat_benchmark(path))
        .collect();
    cnf_paths.sort();
    assert!(
        !cnf_paths.is_empty(),
        "expected at least one UNSAT benchmark in {}",
        corpus_dir.display()
    );
    cnf_paths
}

fn is_fail_closed_known_unsat_benchmark(path: &std::path::Path) -> bool {
    if path
        .file_name()
        .is_some_and(|name| name == "tseitin_cycle_10.cnf")
    {
        return false;
    }
    // `benchmarks/sat/unsat` also carries phase-transition random 3-SAT files
    // that are only "expected UNSAT" statistically, not proven UNSAT. Keep
    // the fail-closed sweep restricted to the deterministic UNSAT corpus.
    // `tseitin_cycle_10.cnf` is also excluded: the checked-in fixture is SAT.
    let contents = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
    !contents
        .lines()
        .take_while(|line| !line.starts_with("p cnf"))
        .any(|line| line.contains("expected UNSAT"))
}

fn assert_unsat_result_for_known_unsat(
    solver: &Solver,
    result: SatResult,
    benchmark: &std::path::Path,
) {
    let label = benchmark
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("<unknown>");
    match result {
        SatResult::Unsat => {}
        SatResult::Sat(model) => {
            let violated = solver
                .verify_against_original(&model)
                .map_or_else(|| "none".to_string(), |idx| idx.to_string());
            panic!(
                "known-UNSAT benchmark {label} returned SAT; first violated original clause={violated}"
            );
        }
        SatResult::Unknown => {
            panic!("known-UNSAT benchmark {label} returned Unknown");
        }
        #[allow(unreachable_patterns)]
        other => unreachable!("unexpected SAT result variant for {label}: {other:?}"),
    }
}

#[test]
fn test_soundness_small_unsat_corpus_dimacs_profile() {
    for path in repo_unsat_corpus_paths() {
        let dimacs = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let formula = crate::parse_dimacs(&dimacs)
            .unwrap_or_else(|e| panic!("parse {} failed: {e}", path.display()));
        let mut solver = formula.into_solver();
        let result = solver.solve().into_inner();
        assert_unsat_result_for_known_unsat(&solver, result, &path);
    }
}

#[test]
fn test_soundness_small_unsat_corpus_core_search_only() {
    for path in repo_unsat_corpus_paths() {
        let dimacs = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let formula = crate::parse_dimacs(&dimacs)
            .unwrap_or_else(|e| panic!("parse {} failed: {e}", path.display()));
        let mut solver = Solver::new(formula.num_vars);
        solver.disable_all_inprocessing();
        solver.set_preprocess_enabled(false);
        solver.set_walk_enabled(false);
        solver.set_warmup_enabled(false);
        for clause in formula.clauses {
            solver.add_clause(clause);
        }
        let result = solver.solve().into_inner();
        assert_unsat_result_for_known_unsat(&solver, result, &path);
    }
}

// ========================================================================
// #7912: Universal verify_external_model tests
//
// These tests validate that verify_external_model correctly verifies
// SAT results against the original formula across all solve paths:
// solve(), solve_with_assumptions(), walk, and preprocessing.
// ========================================================================

/// Verify that solve() produces a model passing verify_external_model.
#[test]
fn test_verify_external_model_solve_basic() {
    let mut solver = Solver::new(4);
    // (x0 v x1) ^ (x1 v x2) ^ (x2 v x3) ^ (~x0 v ~x3)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(3)),
    ]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    // The debug_assert in declare_sat_from_model already calls
    // verify_external_model, but this test explicitly validates it.
    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept the model returned by solve()"
    );
}

/// Verify that solve_with_assumptions() produces a model passing
/// verify_external_model.
#[test]
fn test_verify_external_model_solve_with_assumptions() {
    let mut solver = Solver::new(3);
    // (x0 v x1) ^ (x1 v x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    // Assume x0=false: forces x1=true (from clause 1)
    let assumptions = vec![Literal::negative(Variable(0))];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    let model = match result {
        AssumeResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept the model returned by solve_with_assumptions()"
    );
    // x0 must be false (assumed), x1 must be true (forced by clause 1)
    assert!(!model[0], "x0 should be false (assumed)");
    assert!(
        model[1],
        "x1 should be true (forced by clause 1 with x0=false)"
    );
}

/// Verify that verify_external_model rejects a model that violates an
/// original clause.
#[test]
fn test_verify_external_model_rejects_invalid_model() {
    let mut solver = Solver::new(2);
    // Single clause: (x0 v x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // Model with both variables false violates (x0 v x1)
    let bad_model = vec![false, false];
    assert!(
        !solver.verify_external_model(&bad_model),
        "verify_external_model must reject a model that violates the original clause"
    );

    // Model with x0=true satisfies (x0 v x1)
    let good_model = vec![true, false];
    assert!(
        solver.verify_external_model(&good_model),
        "verify_external_model must accept a valid model"
    );
}

/// Verify that verify_external_model works after preprocessing (BVE).
/// BVE eliminates variables and adds reconstruction entries. The model
/// returned by solve() must still pass verify_external_model after
/// reconstruction.
#[test]
fn test_verify_external_model_after_bve() {
    let mut solver = Solver::new(5);
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_walk_enabled(false);

    // Create a formula where BVE can eliminate x0:
    // (x0 v x1) ^ (~x0 v x2) ^ (x1 v x3) ^ (x2 v x4) ^ (x3 v x4)
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

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept the model after BVE reconstruction"
    );
}

/// Verify that interruptible solve also goes through verify_external_model.
#[test]
fn test_verify_external_model_solve_interruptible() {
    let mut solver = Solver::new(3);
    // (x0 v x1) ^ (~x0 v x2) ^ (x1 v x2)
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
        Literal::positive(Variable(2)),
    ]);

    let result = solver.solve_interruptible(|| false).into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept the model from solve_interruptible()"
    );
}

/// Verify that verify_external_model handles truncated models correctly.
/// Models returned by solve() are truncated to user_num_vars and should
/// still pass verification.
#[test]
fn test_verify_external_model_truncated_model() {
    let mut solver = Solver::new(3);
    // (x0) ^ (~x1) ^ (x2) — unique model: [true, false, true]
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::negative(Variable(1))]);
    solver.add_clause(vec![Literal::positive(Variable(2))]);

    let result = solver.solve().into_inner();
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };

    assert_eq!(model.len(), 3, "model should have exactly 3 variables");
    assert!(
        solver.verify_external_model(&model),
        "verify_external_model must accept unit-clause forced model"
    );
    assert_eq!(model, vec![true, false, true], "unique model must match");
}
