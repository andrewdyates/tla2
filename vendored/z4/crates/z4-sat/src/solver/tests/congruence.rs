// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::add_duplicate_and_gate_formula;
use super::*;

#[test]
fn test_preprocess_congruence_htr_binaries_feed_decompose_without_gate_equivalences() {
    // Clauses:
    //  (r ∨ ¬y ∨ x), (¬r ∨ ¬y), (¬x ∨ y)
    //
    // Hyper-ternary in congruence derives (¬y ∨ x). Together with (¬x ∨ y),
    // this forms x ↔ y and decompose should substitute at least one variable.
    // There are no duplicated gates here, so this exercises the "new binary
    // clauses but no congruence equivalence" path.
    let mut solver: Solver = Solver::new(3);
    let r = Variable(0);
    let x = Variable(1);
    let y = Variable(2);

    solver.add_clause(vec![
        Literal::positive(r),
        Literal::negative(y),
        Literal::positive(x),
    ]);
    solver.add_clause(vec![Literal::negative(r), Literal::negative(y)]);
    solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    assert!(
        !solver.preprocess(),
        "preprocess should not derive UNSAT on this satisfiable formula"
    );

    // With find_equivalences(), congruence now discovers binary implication
    // equivalences (x ≡ y from HTR-derived (¬y,x) + existing (¬x,y)).
    // The original test expected 0 gate equivalences + decompose SCC discovery.
    // Now congruence finds the equivalence directly OR decompose finds it via SCC.
    let cong_equivs = solver.congruence_stats().equivalences_found;
    let decompose_subs = solver.decompose_stats().substituted;
    assert!(
        cong_equivs > 0 || decompose_subs > 0,
        "x↔y equivalence should be found by congruence find_equivalences or decompose SCC \
         (cong_equivs={cong_equivs}, decompose_subs={decompose_subs})"
    );
}

#[test]
fn test_congruence_uses_level0_vals_to_collapse_duplicate_and_gates() {
    let mut solver: Solver = Solver::new(5);
    let y0 = Variable(0);
    let y1 = Variable(1);
    let a = Variable(2);
    let b = Variable(3);
    let c = Variable(4);

    // Root unit assignment a=true. Without passing solver.vals into the
    // congruence engine, y0 stays AND(a,b,c) and cannot collide with y1.
    solver.add_clause(vec![Literal::positive(a)]);

    // y0 = AND(a, b, c)
    solver.add_clause(vec![
        Literal::negative(a),
        Literal::negative(b),
        Literal::negative(c),
        Literal::positive(y0),
    ]);
    solver.add_clause(vec![Literal::positive(a), Literal::negative(y0)]);
    solver.add_clause(vec![Literal::positive(b), Literal::negative(y0)]);
    solver.add_clause(vec![Literal::positive(c), Literal::negative(y0)]);

    // y1 = AND(b, c)
    solver.add_clause(vec![
        Literal::negative(b),
        Literal::negative(c),
        Literal::positive(y1),
    ]);
    solver.add_clause(vec![Literal::positive(b), Literal::negative(y1)]);
    solver.add_clause(vec![Literal::positive(c), Literal::negative(y1)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "fixture must expose a level-0 assignment before congruence runs"
    );

    assert!(
        solver.congruence(),
        "level-0 vals should reduce y0 to AND(b,c) so congruence can discover y0 ≡ y1"
    );
    assert!(
        solver.congruence_stats().equivalences_found > 0,
        "expected congruence equivalences after vals-aware gate rewriting"
    );
}

#[test]
fn test_preprocess_congruence_does_not_force_decompose_when_disabled() {
    let mut solver: Solver = Solver::new(4);
    add_duplicate_and_gate_formula(&mut solver);

    solver.set_decompose_enabled(false);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_factor_enabled(false);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    // Drain initial unit propagations so qhead == trail.len() before preprocess.
    assert!(solver.propagate().is_none());

    let decompose_rounds_before = solver.decompose_stats().rounds;
    let congruence_rounds_before = solver.congruence_stats().rounds;

    assert!(
        !solver.preprocess(),
        "preprocess should not derive UNSAT on satisfiable duplicate-gate formula"
    );
    // #5752: congruence MUST NOT run when decompose is disabled. Without
    // decompose, congruence binary clauses remain unsubstituted and BVE may
    // eliminate variables with active equivalence binaries, causing
    // reconstruction to produce invalid models.
    assert_eq!(
        solver.congruence_stats().rounds,
        congruence_rounds_before,
        "congruence must not run when decompose_enabled=false (#5752)"
    );
    assert_eq!(
        solver.decompose_stats().rounds,
        decompose_rounds_before,
        "decompose must not run when decompose_enabled=false"
    );
}

#[test]
fn test_preprocess_skips_congruence_when_congruence_disabled() {
    let mut solver: Solver = Solver::new(4);
    add_duplicate_and_gate_formula(&mut solver);

    solver.set_decompose_enabled(false);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(false);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_factor_enabled(false);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    // Drain initial unit propagations so qhead == trail.len() before preprocess.
    assert!(solver.propagate().is_none());

    let congruence_rounds_before = solver.congruence_stats().rounds;
    assert!(
        !solver.preprocess(),
        "preprocess should not derive UNSAT on satisfiable duplicate-gate formula"
    );
    assert_eq!(
        solver.congruence_stats().rounds,
        congruence_rounds_before,
        "congruence must stay skipped when congruence_enabled=false"
    );
}

#[test]
fn test_restart_inprocessing_congruence_does_not_force_decompose_when_disabled() {
    let mut solver: Solver = Solver::new(4);
    add_duplicate_and_gate_formula(&mut solver);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    // Drain initial unit propagations so qhead == trail.len() before inprocessing.
    assert!(solver.propagate().is_none());

    solver.set_decompose_enabled(false);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_factor_enabled(false);

    solver.num_conflicts = solver.inproc_ctrl.congruence.next_conflict;
    // Simulate a reduce_db having occurred so the reduction gate passes (#5130).
    solver.cold.num_reductions = 1;

    let decompose_rounds_before = solver.decompose_stats().rounds;
    let congruence_rounds_before = solver.congruence_stats().rounds;

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on satisfiable duplicate-gate formula"
    );
    // #5752: congruence MUST NOT run when decompose is disabled. Without
    // decompose, congruence binary clauses remain unsubstituted and BVE may
    // eliminate variables with active equivalence binaries, causing
    // reconstruction to produce invalid models.
    assert_eq!(
        solver.congruence_stats().rounds,
        congruence_rounds_before,
        "congruence must not run when decompose_enabled=false (#5752)"
    );
    assert_eq!(
        solver.decompose_stats().rounds,
        decompose_rounds_before,
        "decompose must not run when decompose_enabled=false"
    );
}
