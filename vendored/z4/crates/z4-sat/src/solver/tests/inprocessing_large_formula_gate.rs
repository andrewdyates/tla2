// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn hyper_unary_round_solver() -> (Solver, Variable) {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);
    let a_pos = Literal::positive(a);

    // (a v b) and (a v !b) let the inprocessing binary-dedup pass derive unit a.
    solver.add_clause_db(&[a_pos, Literal::positive(b)], false);
    solver.add_clause_db(&[a_pos, Literal::negative(b)], false);
    solver.initialize_watches();

    (solver, a)
}

#[test]
fn test_inprocessing_gates_pass_uses_base_interval_on_small_formulas() {
    let (mut solver, _) = hyper_unary_round_solver();

    // With next_inprobe_conflict=0 (default), any num_conflicts>0 passes.
    solver.num_conflicts = 500;
    assert!(
        solver.inprocessing_gates_pass(),
        "small formulas should pass inprocessing gate when conflicts >= limit",
    );
}

#[test]
fn test_inprocessing_gates_pass_respects_conflict_limit() {
    let (mut solver, _) = hyper_unary_round_solver();

    // Set a conflict limit — gate should block until reached.
    solver.cold.next_inprobe_conflict = 2000;
    solver.num_conflicts = 500;
    assert!(
        !solver.inprocessing_gates_pass(),
        "conflicts below next_inprobe_conflict should be blocked",
    );

    solver.num_conflicts = 1999;
    assert!(
        !solver.inprocessing_gates_pass(),
        "conflicts just below limit should be blocked",
    );

    solver.num_conflicts = 2000;
    assert!(
        solver.inprocessing_gates_pass(),
        "conflicts at limit should pass",
    );
}

#[test]
fn test_run_restart_inprocessing_respects_conflict_limit_on_large_formulas() {
    let (mut solver, a) = hyper_unary_round_solver();
    solver
        .arena
        .spoof_num_clauses_for_test(PREPROCESS_EXPENSIVE_MAX_CLAUSES + 1);

    // Simulate init_search_limits setting a high conflict limit.
    solver.cold.next_inprobe_conflict = 2000;

    solver.num_conflicts = 500;
    assert!(
        !solver.run_restart_inprocessing(),
        "500 conflicts should not enter inprocessing when limit is 2000",
    );
    assert_eq!(
        solver.get_var_assignment(a.index()),
        None,
        "the conflict limit should prevent binary dedup from firing at 500 conflicts",
    );

    solver.num_conflicts = 2000;
    assert!(
        !solver.run_restart_inprocessing(),
        "the inprocessing round should complete without deriving UNSAT",
    );
    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "once the limit is reached, the inprocessing round should derive the hyper-unary unit",
    );
}

#[test]
fn test_run_restart_inprocessing_allows_bve_above_former_large_clause_cap() {
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // x0 is a trivial BVE candidate: eliminating it replaces the pair with (x1 v x2).
    solver.add_clause_db(&[Literal::positive(x0), Literal::positive(x1)], false);
    solver.add_clause_db(&[Literal::negative(x0), Literal::positive(x2)], false);

    // Keep auxiliaries from being pure-eliminated before x0.
    solver.freeze(x1);
    solver.freeze(x2);

    solver.initialize_watches();
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_backbone_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_cce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_vivify_enabled(false);

    // Reproduce the old scheduler condition: active_clauses > 5_000_000.
    solver.arena.spoof_num_clauses_for_test(5_000_001);
    solver.cold.next_inprobe_conflict = 1;
    solver.num_conflicts = 1;

    assert!(
        !solver.run_restart_inprocessing(),
        "the inprocessing round should complete without deriving UNSAT",
    );
    assert_eq!(
        solver.bve_stats().vars_eliminated,
        1,
        "BVE should still run above the former 5M-clause inprocessing cap",
    );
    assert!(
        solver.inproc.bve.is_eliminated(x0),
        "x0 should be eliminated by inprocessing BVE",
    );
}
