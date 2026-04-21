// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::assert_watch_invariant_for_all_active_clauses;
use super::*;

#[test]
fn test_rebuild_watches_rewinds_qhead_and_exposes_level0_conflict() {
    let mut solver: Solver = Solver::new(3);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);

    // Level-0 assignment: x=false, y=false, z=true.
    solver.add_clause(vec![Literal::negative(x)]);
    solver.add_clause(vec![Literal::negative(y)]);
    solver.add_clause(vec![Literal::positive(z)]);
    // Initially satisfied by z=true.
    let last_clause_off = solver.arena.len();
    solver.add_clause(vec![
        Literal::positive(x),
        Literal::positive(y),
        Literal::positive(z),
    ]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());
    assert_eq!(
        solver.qhead,
        solver.trail.len(),
        "setup should finish with no pending propagation"
    );

    // Simulate an inprocessing rewrite: (x ∨ y ∨ z) -> (x ∨ y), which is now
    // conflicting under the current level-0 assignment.
    let clause_idx = last_clause_off;
    let new_lits = &[Literal::positive(x), Literal::positive(y)];
    solver.arena.replace(clause_idx, new_lits);
    solver.arena.set_saved_pos(clause_idx, 2);

    // Mark trail as affected from position 0 since clause content changed (#8095).
    solver.mark_trail_affected(0);
    solver.rebuild_watches();
    assert_eq!(
        solver.qhead, 0,
        "rebuild_watches must rewind qhead so existing assignments are rechecked"
    );
    assert!(
        solver.propagate().is_some(),
        "rebuilt watches should expose the latent level-0 conflict"
    );
}

/// Verify that `rebuild_watches` with `earliest_affected_trail_pos = None`
/// sets qhead to trail.len() (no re-propagation needed). This is the common
/// case when rebuild_watches is called without any clause content changes.
#[test]
fn test_rebuild_watches_no_affected_pos_skips_repropagation() {
    let mut solver: Solver = Solver::new(4);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);

    // Create a formula with level-0 units and a satisfied clause.
    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![Literal::positive(b)]);
    solver.add_clause(vec![
        Literal::positive(a),
        Literal::positive(c),
        Literal::positive(d),
    ]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());
    let trail_len = solver.trail.len();

    // Reset earliest_affected_trail_pos to None (no changes during inprocessing).
    solver.earliest_affected_trail_pos = None;
    solver.rebuild_watches();

    // qhead should be set to trail.len() since nothing was affected.
    assert_eq!(
        solver.qhead, trail_len,
        "rebuild_watches with no affected pos should set qhead to trail.len()"
    );
}

/// Verify that `rebuild_watches` with `earliest_affected_trail_pos = Some(pos)`
/// rewinds qhead to exactly that position, not to 0.
#[test]
fn test_rebuild_watches_minimal_rewind_to_affected_pos() {
    let mut solver: Solver = Solver::new(5);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);
    let e = Variable(4);

    // Create a formula with several level-0 units.
    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![Literal::positive(b)]);
    solver.add_clause(vec![Literal::positive(c)]);
    solver.add_clause(vec![
        Literal::positive(a),
        Literal::positive(d),
        Literal::positive(e),
    ]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());
    let trail_len = solver.trail.len();
    assert!(trail_len >= 3, "expected at least 3 trail entries from units");

    // Simulate: inprocessing affected position 2 (e.g., a new unit was
    // derived at trail position 2).
    solver.mark_trail_affected(2);
    solver.rebuild_watches();

    assert_eq!(
        solver.qhead, 2,
        "rebuild_watches should rewind qhead to earliest_affected_trail_pos"
    );
    // Propagation from position 2 should succeed without conflict.
    assert!(solver.propagate().is_none());
}

/// Verify that `mark_trail_affected` correctly tracks the minimum position
/// across multiple calls.
#[test]
fn test_mark_trail_affected_tracks_minimum() {
    let mut solver: Solver = Solver::new(2);

    // Start with None.
    assert_eq!(solver.earliest_affected_trail_pos, None);

    // First mark: sets to 10.
    solver.mark_trail_affected(10);
    assert_eq!(solver.earliest_affected_trail_pos, Some(10));

    // Second mark at 5: should update to 5 (lower).
    solver.mark_trail_affected(5);
    assert_eq!(solver.earliest_affected_trail_pos, Some(5));

    // Third mark at 8: should keep 5 (lower).
    solver.mark_trail_affected(8);
    assert_eq!(solver.earliest_affected_trail_pos, Some(5));

    // Fourth mark at 0: should update to 0.
    solver.mark_trail_affected(0);
    assert_eq!(solver.earliest_affected_trail_pos, Some(0));
}

#[test]
fn test_add_preserved_learned_sets_watches_and_enqueues_unit() {
    let mut solver: Solver = Solver::new(2);
    let x = Variable(0);
    let y = Variable(1);

    // Force x=true at level 0 so (¬x ∨ y) is unit and should enqueue y.
    solver.add_clause(vec![Literal::positive(x)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());

    let clause_idx = solver.arena.len();
    assert!(solver.add_preserved_learned(vec![Literal::negative(x), Literal::positive(y),]));

    let clause_ref = ClauseRef(clause_idx as u32);
    assert!(
        solver.arena.is_learned(clause_idx),
        "preserved clause must be marked learned"
    );
    assert_eq!(
        solver.watches.count_watches_for_clause(clause_ref),
        2,
        "preserved learned clause must be attached to two watch lists"
    );
    // Z4 keeps reasons at level 0 (unlike CaDiCaL which clears them) for
    // LRAT proof materialization (#6998). The important thing is that y IS
    // assigned (propagation happened).
    assert_eq!(
        solver.lit_val(Literal::positive(y)),
        1,
        "preserved learned clause should participate in unit propagation"
    );
    assert_watch_invariant_for_all_active_clauses(&solver, "add_preserved_learned");
}

#[test]
fn test_propagate_conflict_updates_no_conflict_until_binary() {
    let mut solver: Solver = Solver::new(2);
    let x = Variable(0);
    let y = Variable(1);

    solver.add_clause(vec![Literal::negative(x), Literal::negative(y)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver.decide(Literal::positive(y));
    solver.enqueue(Literal::positive(x), None);
    solver.no_conflict_until = solver.trail.len();

    assert!(solver.propagate().is_some(), "expected binary conflict");
    assert_eq!(
        solver.no_conflict_until, 0,
        "binary conflict must reset no_conflict_until to level-1 trail start"
    );
}

#[test]
fn test_propagate_conflict_updates_no_conflict_until_non_binary() {
    let mut solver: Solver = Solver::new(3);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);

    solver.add_clause(vec![
        Literal::negative(x),
        Literal::negative(y),
        Literal::negative(z),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver.decide(Literal::positive(x));
    solver.enqueue(Literal::positive(y), None);
    solver.enqueue(Literal::positive(z), None);
    solver.no_conflict_until = solver.trail.len();

    assert!(solver.propagate().is_some(), "expected non-binary conflict");
    assert_eq!(
        solver.no_conflict_until, 0,
        "non-binary conflict must reset no_conflict_until to level-1 trail start"
    );
}

#[test]
fn test_search_propagate_direct_unit_chain() {
    let mut solver: Solver = Solver::new(3);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);

    solver.add_clause(vec![Literal::positive(x)]);
    solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]);
    solver.add_clause(vec![Literal::negative(y), Literal::positive(z)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let conflict = solver.search_propagate();
    assert!(
        conflict.is_none(),
        "search propagation should not conflict on a simple implication chain"
    );
    assert_eq!(solver.lit_val(Literal::positive(x)), 1);
    assert_eq!(solver.lit_val(Literal::positive(y)), 1);
    assert_eq!(solver.lit_val(Literal::positive(z)), 1);
    // Level-0 propagated units retain their reason clause for LRAT
    // proof chain construction (#6998). Unlike CaDiCaL which clears
    // level-0 reasons, Z4 uses lazy proof materialization that needs
    // the reason clause to build LRAT chains for level-0 units
    // discovered during ChrBT propagation.
    assert_eq!(
        solver.var_data[y.index()].level,
        0,
        "y should be assigned at level 0"
    );
    assert!(
        solver.var_reason(y.index()).is_some(),
        "level-0 propagated y retains reason for LRAT (#6998)"
    );
    assert_eq!(
        solver.var_data[z.index()].level,
        0,
        "z should be assigned at level 0"
    );
    assert!(
        solver.var_reason(z.index()).is_some(),
        "level-0 propagated z retains reason for LRAT (#6998)"
    );
}

#[test]
fn test_enqueue_uses_reason_max_level_under_chrono() {
    let mut solver: Solver = Solver::new(3);
    solver.chrono_enabled = true;

    let a = Variable(0);
    let b = Variable(1);

    solver.add_clause(vec![Literal::negative(a), Literal::positive(b)]);
    let reason = ClauseRef(0);

    solver.decide(Literal::positive(a));
    solver.qhead = solver.trail.len();
    solver.decision_level = 2;
    solver.trail_lim.push(1);

    solver.enqueue(Literal::positive(b), Some(reason));

    assert_eq!(
        solver.var_data[b.index()].level,
        1,
        "chrono propagate should use max reason level instead of current decision level"
    );
    assert_eq!(
        solver.var_reason(b.index()),
        Some(reason),
        "non-zero assignment level must retain the reason clause"
    );
}

#[test]
fn test_enqueue_clamps_stale_reason_levels_at_root() {
    let mut solver: Solver = Solver::new(2);
    solver.chrono_enabled = true;

    let a = Variable(0);
    let b = Variable(1);

    solver.add_clause(vec![Literal::negative(a), Literal::positive(b)]);
    let reason = ClauseRef(0);

    // Simulate chrono-BT residue: `a` is still assigned true in vals[] so
    // the reason literal ¬a is false, but the stored level is stale relative
    // to the current root decision level.
    solver.vals[Literal::positive(a).index()] = 1;
    solver.vals[Literal::negative(a).index()] = -1;
    solver.var_data[a.index()].level = 1;
    solver.decision_level = 0;

    solver.enqueue(Literal::positive(b), Some(reason));

    assert_eq!(
        solver.var_data[b.index()].level,
        0,
        "root-level enqueue must clamp stale reason levels to decision_level"
    );
}

#[test]
fn test_search_propagate_binary_delete_unlinks_watches_before_flush() {
    let mut solver: Solver = Solver::new(2);
    let x = Variable(0);
    let y = Variable(1);
    let clause_ref = ClauseRef(0);
    let has_watch = |solver: &Solver, lit: Literal| {
        let watch_list = solver.watches.get_watches(lit);
        (0..watch_list.len()).any(|wi| watch_list.clause_ref(wi) == clause_ref)
    };

    solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(
        has_watch(&solver, Literal::negative(x)),
        "binary clause should watch ¬x before deletion",
    );
    assert!(
        has_watch(&solver, Literal::positive(y)),
        "binary clause should watch y before deletion",
    );

    // Delete the binary clause without flushing watches. Binary watches must
    // be unlinked eagerly (#4924), unlike long-clause watches.
    let deleted = solver.delete_clause_unchecked(0, mutate::ReasonPolicy::Skip);
    assert_eq!(deleted, mutate::DeleteResult::Deleted);
    assert!(!solver.arena.is_active(0));
    assert!(
        !has_watch(&solver, Literal::negative(x)),
        "binary delete must eagerly unlink watch on ¬x",
    );
    assert!(
        !has_watch(&solver, Literal::positive(y)),
        "binary delete must eagerly unlink watch on y",
    );

    solver.decide(Literal::positive(x));
    let conflict = solver.search_propagate();
    assert!(
        conflict.is_none(),
        "deleted binary clause should not cause conflict before flush",
    );
    assert_eq!(
        solver.lit_val(Literal::positive(y)),
        0,
        "deleted binary watcher must not propagate y before flush",
    );
    assert_eq!(
        solver.var_reason(y.index()),
        None,
        "deleted binary watcher must not become y's reason",
    );

    // Flushing should preserve the same result (already unlinked).
    solver.backtrack(0);
    solver.flush_watches();
    solver.decide(Literal::positive(x));
    let conflict_after_flush = solver.search_propagate();
    assert!(conflict_after_flush.is_none());
    assert_eq!(
        solver.lit_val(Literal::positive(y)),
        0,
        "flushing should not change already-unlinked binary propagation behavior"
    );
}

#[test]
fn test_search_propagate_matches_probe_path_without_probing_mode() {
    fn next_u64(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        *state
    }

    fn next_literal(state: &mut u64, num_vars: usize) -> Literal {
        let var = Variable((next_u64(state) % num_vars as u64) as u32);
        if next_u64(state) & 1 == 0 {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }

    const NUM_FORMULAS: usize = 64;
    const NUM_VARS: usize = 10;

    for seed in 0..NUM_FORMULAS as u64 {
        let mut state = seed ^ 0x9E37_79B9_7F4A_7C15;
        let mut formula: Vec<Vec<Literal>> = Vec::new();
        let clause_count = 6 + (next_u64(&mut state) % 10) as usize;

        for _ in 0..clause_count {
            let clause_len = 2 + (next_u64(&mut state) % 3) as usize;
            let mut clause = Vec::with_capacity(clause_len);
            while clause.len() < clause_len {
                let lit = next_literal(&mut state, NUM_VARS);
                if !clause.contains(&lit) {
                    clause.push(lit);
                }
            }
            formula.push(clause);
        }

        let mut probe_like: Solver = Solver::new(NUM_VARS);
        let mut search: Solver = Solver::new(NUM_VARS);
        for clause in &formula {
            probe_like.add_clause(clause.clone());
            search.add_clause(clause.clone());
        }

        probe_like.initialize_watches();
        search.initialize_watches();
        let probe_ok = probe_like.process_initial_clauses().is_none();
        let search_ok = search.process_initial_clauses().is_none();
        assert_eq!(
            search_ok, probe_ok,
            "initial clause processing diverged for seed {seed}",
        );
        if !probe_ok {
            continue;
        }

        let decisions = (next_u64(&mut state) % 4) as usize;
        let mut early_conflict = false;
        for _ in 0..decisions {
            let lit = next_literal(&mut state, NUM_VARS);
            let var_idx = lit.variable().index();
            if probe_like.var_is_assigned(var_idx) {
                continue;
            }
            probe_like.decide(lit);
            search.decide(lit);
            // Propagate between decisions: decide() requires qhead == trail.len()
            // (CaDiCaL propagate.cpp:188 — all propagations complete before deciding).
            let probe_c = probe_like.propagate();
            let search_c = search.search_propagate();
            if probe_c.is_some() || search_c.is_some() {
                assert_eq!(
                    search_c.is_some(),
                    probe_c.is_some(),
                    "conflict mismatch during decision for seed {seed}",
                );
                early_conflict = true;
                break;
            }
        }
        if early_conflict {
            continue;
        }

        // Final propagation (in case 0 decisions were made).
        let probe_conflict = probe_like.propagate();
        let search_conflict = search.search_propagate();
        assert_eq!(
            search_conflict.is_some(),
            probe_conflict.is_some(),
            "conflict mismatch for seed {seed}",
        );
        if let (Some(probe_cref), Some(search_cref)) = (probe_conflict, search_conflict) {
            let probe_clause = probe_like.arena.literals(probe_cref.0 as usize);
            let search_clause = search.arena.literals(search_cref.0 as usize);
            assert_eq!(
                search_clause, probe_clause,
                "conflict clause mismatch for seed {seed}",
            );
        }

        assert_eq!(
            search.trail, probe_like.trail,
            "trail mismatch for seed {seed}"
        );
        assert_eq!(
            search.vals, probe_like.vals,
            "vals mismatch for seed {seed}",
        );
        assert_eq!(
            search.var_data, probe_like.var_data,
            "var_data mismatch for seed {seed}"
        );
        assert_eq!(
            search.qhead, probe_like.qhead,
            "qhead mismatch for seed {seed}"
        );
        assert_eq!(
            search.no_conflict_until, probe_like.no_conflict_until,
            "no_conflict_until mismatch for seed {seed}",
        );
    }
}

// ========================================================================
// Watch attachment tests (extracted from tests.rs, Part of #5142)
// ========================================================================

#[test]
fn test_watch_attachment_checker_covers_all_insertion_paths() {
    let mut solver: Solver = Solver::new(6);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);
    let x4 = Variable(4);
    let x5 = Variable(5);

    // initialize_watches path (pre-solve clause insertion via add_clause).
    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::negative(x1),
        Literal::positive(x3),
    ]);
    solver.initialize_watches();
    assert_watch_invariant_for_all_active_clauses(&solver, "initialize_watches");

    // add_clause_watched path.
    let mut irredundant = [
        Literal::negative(x2),
        Literal::positive(x4),
        Literal::positive(x5),
    ];
    let _ = solver.add_clause_watched(&mut irredundant);
    assert_watch_invariant_for_all_active_clauses(&solver, "add_clause_watched");

    // add_theory_lemma path.
    let theory_ref = solver.add_theory_lemma(vec![
        Literal::negative(x3),
        Literal::positive(x4),
        Literal::negative(x5),
    ]);
    assert!(theory_ref.is_some(), "expected theory lemma to be inserted");
    assert_watch_invariant_for_all_active_clauses(&solver, "add_theory_lemma");

    // add_learned_clause path (learned backtrack-order policy).
    solver.var_data[x0.index()].level = 1;
    solver.var_data[x4.index()].level = 5;
    solver.var_data[x5.index()].level = 3;
    let learned_ref = solver.add_learned_clause(
        vec![
            Literal::negative(x0),
            Literal::positive(x5),
            Literal::positive(x4),
        ],
        2,
        &[],
    );
    let learned_idx = learned_ref.0 as usize;
    assert_eq!(
        solver.arena.literal(learned_idx, 1),
        Literal::positive(x4),
        "learned-clause watch policy must place max non-UIP level at index 1"
    );
    assert_watch_invariant_for_all_active_clauses(&solver, "add_learned_clause");

    // replace_clause_checked path (strengthen/rewrite attachment).
    let _ =
        solver.replace_clause_checked(learned_idx, &[Literal::negative(x0), Literal::positive(x4)]);
    assert_watch_invariant_for_all_active_clauses(&solver, "replace_clause_checked");

    // rebuild_watches path.
    let rebuild_lits = &[
        Literal::positive(x1),
        Literal::positive(x0),
        Literal::positive(x2),
    ];
    solver.arena.replace(0, rebuild_lits);
    solver.arena.set_saved_pos(0, 2);
    // Mark trail as affected since clause content changed (#8095).
    solver.mark_trail_affected(0);
    solver.rebuild_watches();
    assert_watch_invariant_for_all_active_clauses(&solver, "rebuild_watches");
}
