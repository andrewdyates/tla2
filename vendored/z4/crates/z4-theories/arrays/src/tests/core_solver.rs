// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_array_solver_basic_sat() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), i)
    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, i);

    // Create equality: select(store(a, i, v), i) = v
    let eq = store.mk_eq(selected, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);

    // Should be SAT - this is consistent with ROW1
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_array_solver_row1_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int); // Different variable for index
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j)
    // Using different index variable j to avoid term-level simplification
    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, j);

    // Create equalities
    let eq_ij = store.mk_eq(i, j); // i = j (will be asserted true)
    let eq_sel_v = store.mk_eq(selected, v); // select(store(a,i,v), j) = v

    let mut solver = ArraySolver::new(&store);

    // Assert i = j (so ROW1 applies)
    solver.assert_literal(eq_ij, true);
    // Assert select(store(a,i,v), j) ≠ v (directly contradicts ROW1 when i=j)
    solver.assert_literal(eq_sel_v, false);

    solver.populate_caches();
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row1()
        .expect("expected ROW1 helper to emit a lemma")
    else {
        panic!("expected NeedLemmas from ROW1 helper");
    };
    assert_eq!(lemmas.len(), 1, "ROW1 conflict should emit one lemma");
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, false), TheoryLit::new(eq_sel_v, true)],
        "ROW1 lemma must block i=j and select(store(a,i,v),j)!=v simultaneously"
    );
}

#[test]
fn test_array_solver_row1_preserves_pending_tail_after_first_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a1 = store.mk_var("a1", arr_sort.clone());
    let a2 = store.mk_var("a2", arr_sort);

    let i1 = store.mk_var("i1", Sort::Int);
    let j1 = store.mk_var("j1", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);

    let i2 = store.mk_var("i2", Sort::Int);
    let j2 = store.mk_var("j2", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let store1 = store.mk_store(a1, i1, v1);
    let select1 = store.mk_select(store1, j1);
    let eq_i1_j1 = store.mk_eq(i1, j1);
    let eq_sel1_v1 = store.mk_eq(select1, v1);

    let store2 = store.mk_store(a2, i2, v2);
    let select2 = store.mk_select(store2, j2);
    let eq_i2_j2 = store.mk_eq(i2, j2);
    let eq_sel2_v2 = store.mk_eq(select2, v2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_i1_j1, true);
    solver.assert_literal(eq_sel1_v1, false);
    solver.assert_literal(eq_i2_j2, true);

    solver.populate_caches();
    assert!(
        solver.pending_row1.contains(&(select1, store1)),
        "first ROW1 pair should be queued before the first check"
    );
    assert!(
        solver.pending_row1.contains(&(select2, store2)),
        "second ROW1 pair should be queued before the first check"
    );

    let TheoryResult::NeedLemmas(first_lemmas) = solver
        .check_row1()
        .expect("expected the first ROW1 pair to emit a lemma")
    else {
        panic!("expected NeedLemmas from the first ROW1 pair");
    };
    assert_eq!(
        first_lemmas[0].clause,
        vec![
            TheoryLit::new(eq_i1_j1, false),
            TheoryLit::new(eq_sel1_v1, true),
        ],
        "the first ROW1 conflict should be emitted before replaying the retained tail"
    );
    assert_eq!(
        solver.pending_row1,
        vec![(select2, store2)],
        "the unprocessed ROW1 tail must survive the first lemma return"
    );

    solver.assert_literal(eq_sel2_v2, false);
    let TheoryResult::NeedLemmas(second_lemmas) = solver
        .check_row1()
        .expect("expected retained ROW1 work to emit a second lemma")
    else {
        panic!("expected NeedLemmas from the retained ROW1 pair");
    };
    assert_eq!(
        second_lemmas[0].clause,
        vec![
            TheoryLit::new(eq_i2_j2, false),
            TheoryLit::new(eq_sel2_v2, true),
        ],
        "retained ROW1 work should fire without repopulating caches"
    );
    assert!(
        solver.pending_row1.is_empty(),
        "the ROW1 queue should be empty after draining the retained tail"
    );
}

#[test]
fn test_array_solver_row2_sat() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j)
    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    // Create equalities
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);

    // Assert i ≠ j
    solver.assert_literal(eq_ij, false);
    // Assert select(store(a,i,v), j) = select(a, j) - consistent with ROW2
    solver.assert_literal(eq_sels, true);

    // ROW2 clause is (eq_ij ∨ eq_sels). Since eq_sels is already true,
    // the clause is satisfied — the solver correctly skips emission (#6738).
    // check() returns Sat (no lemmas needed) instead of NeedLemmas.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected Sat when ROW2 clause is already satisfied, got {result:?}",
    );
}

#[test]
fn test_array_solver_row2_unassigned_emits_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j)
    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    // Create equalities (these must exist for the lemma atoms)
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);

    // Assert i ≠ j but do NOT assert eq_sels — leave it unassigned
    solver.assert_literal(eq_ij, false);

    // ROW2 clause (eq_ij ∨ eq_sels): eq_ij is false, eq_sels is unassigned.
    // Clause is NOT satisfied — solver should emit NeedLemmas.
    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("expected NeedLemmas when ROW2 clause has unassigned disjunct");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW2 lemma clause");
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_sels, true)],
        "ROW2 lemma must assert i=j or select(store(a,i,v),j)=select(a,j)"
    );
}

#[test]
fn test_array_solver_row2_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j) and select(a, j)
    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    // Create equalities
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);

    // Assert i ≠ j
    solver.assert_literal(eq_ij, false);
    // Assert select(store(a,i,v), j) ≠ select(a, j) - contradicts ROW2
    solver.assert_literal(eq_sels, false);

    // #6694: After restoring Unsat early-returns in check(), a conflict
    // check may detect the contradiction directly as Unsat before
    // check_row2() emits NeedLemmas. Both are sound — ROW2 says
    // i≠j → select(store(a,i,v),j)=select(a,j), so asserting both
    // i≠j and sel(store)≠sel(a) is unsatisfiable.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from ROW2 contradiction, got {result:?}",
    );
}

#[test]
fn test_array_solver_row2_propagation_dedups_same_reason() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ij, false);

    let first = solver.propagate();
    assert_eq!(
        first.len(),
        1,
        "ROW2 should emit one propagation the first time"
    );
    assert_eq!(
        first[0].literal,
        TheoryLit::new(eq_sels, true),
        "ROW2 should propagate select(store(a,i,v),j) = select(a,j)"
    );
    assert_eq!(
        first[0].reason,
        vec![TheoryLit::new(eq_ij, false)],
        "ROW2 propagation should keep the index disequality reason"
    );

    let second = solver.propagate();
    assert!(
        second.is_empty(),
        "repeating propagate() with the same reason set must not re-emit the same clause"
    );
}

#[test]
fn test_affine_index_relations_detect_equal_and_distinct() {
    let mut store = TermStore::new();
    let i = store.mk_var("i", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let i_plus_1_a = store.mk_add(vec![i, one]);
    let i_plus_1_b = store.mk_add(vec![i, one]);
    let i_plus_2 = store.mk_add(vec![i, two]);

    let solver = ArraySolver::new(&store);
    assert!(solver.known_equal(i_plus_1_a, i_plus_1_b));
    // Tautological affine offset (i+1 vs i+2) is O(1) and kept in the
    // array theory for the propagation path (#6820).  The expensive
    // equality-substituted affine BFS was removed.
    assert!(solver.distinct_by_affine_offset(i_plus_1_a, i_plus_2));
}

#[test]
fn test_explain_distinct_if_provable_no_affine_bfs() {
    // After #6820, the array theory no longer does affine BFS to prove i ≠ j
    // from arithmetic structure like j = i + 1.  That reasoning belongs in
    // the LRA/LIA solver.
    let mut store = TermStore::new();
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let i_plus_1 = store.mk_add(vec![i, one]);
    let eq_j_i_plus_1 = store.mk_eq(j, i_plus_1);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_j_i_plus_1, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Without the arithmetic solver propagating i ≠ j into the diseq_set,
    // the array theory cannot explain the distinctness.
    assert_eq!(
        solver.explain_distinct_if_provable(i, j),
        None,
        "array theory should not independently derive arithmetic disequalities (#6820)"
    );
}

/// Verify resolve_select_through_stores walks a store chain using concrete
/// integer constants. ROW2 skips stores at distinct indices, ROW1 matches
/// the target index. Uses concrete constants (0, 1, 2) so both_const is
/// true and explain_distinct's empty reasons don't cause a bail-out (#5157).
#[test]
fn test_resolve_select_through_concrete_store_chain() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a = store.mk_var("a", arr_sort);
    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));
    let idx2 = store.mk_int(BigInt::from(2));
    let v0 = store.mk_var("v0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    // Build chain: store(store(store(a, 2, v2), 1, v1), 0, v0)
    let s1 = store.mk_store(a, idx2, v2);
    let s2 = store.mk_store(s1, idx1, v1);
    let s3 = store.mk_store(s2, idx0, v0);

    // Assert a literal so the solver has something to process, then
    // call check() to populate store_cache from all TermStore terms.
    let sel = store.mk_select(s3, idx1);
    let eq = store.mk_eq(sel, v1);
    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    // Select at index 1: skip store at 0 (ROW2), match store at 1 (ROW1).
    let result = solver.resolve_select_through_stores(s3, idx1);
    assert!(result.is_some(), "should resolve value at index 1");
    let (value, _reasons) = result.unwrap();
    assert_eq!(value, v1, "select(store(..., 1, v1), 1) should be v1");

    // Select at index 2: skip stores at 0 and 1, match store at 2.
    let result = solver.resolve_select_through_stores(s3, idx2);
    assert!(result.is_some(), "should resolve value at index 2");
    let (value, _reasons) = result.unwrap();
    assert_eq!(value, v2, "select(store(..., 2, v2), 2) should be v2");
}

#[test]
fn test_array_solver_push_pop() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, i);
    let eq_sel_v = store.mk_eq(selected, v);
    let eq_v_w = store.mk_eq(v, w);

    let mut solver = ArraySolver::new(&store);

    // Assert something consistent
    solver.assert_literal(eq_sel_v, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Push and add conflicting assertion
    solver.push();
    solver.assert_literal(eq_v_w, false);
    // Note: This specific case might still be SAT because eq_sel_v being true
    // doesn't directly conflict with eq_v_w being false in the current implementation
    // Let me fix the test to be more precise

    // Pop should restore consistent state
    solver.pop();
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_equiv_class_cache_rebuilds_only_when_graph_changes() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let eq_ab = store.mk_eq(a, b);
    let sel = store.mk_select(a, i);
    let eq_sel_v = store.mk_eq(sel, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(solver.equiv_class_cache_builds, 1);

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.equiv_class_cache_builds, 1,
        "repeated check() without equality-graph changes should reuse the cache"
    );

    solver.assert_literal(eq_sel_v, false);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.equiv_class_cache_builds, 1,
        "false equality assignments must not rebuild equivalence classes"
    );

    solver.assert_literal(eq_sel_v, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.equiv_class_cache_builds, 2,
        "new true equalities must rebuild equivalence classes"
    );
}

#[test]
fn test_final_check_skips_equiv_cache_when_no_selects_or_stores() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);

    assert!(
        matches!(solver.final_check(), TheoryResult::Sat),
        "array final_check with zero select/store terms should be a no-op"
    );
    assert_eq!(
        solver.final_check_call_count, 1,
        "final_check should still record the call"
    );
    assert_eq!(
        solver.equiv_class_cache_builds, 0,
        "final_check should not rebuild equivalence classes when there are no array terms"
    );
    assert_eq!(
        solver.final_check_snapshot,
        Some((1, 0, 0, 0, 0)),
        "zero-array final_check should cache the empty snapshot"
    );
}

#[test]
fn test_warm_cache_true_equalities_update_assignment_indices_incrementally() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let c = store.mk_var("c", Sort::Int);

    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "initial cache warm-up should perform one full assignment-index rebuild"
    );

    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_bc, true);

    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "warm-cache asserted equalities should update eq_adj incrementally"
    );
    assert_eq!(
        solver.explain_equal_if_provable(a, c),
        Some(vec![
            TheoryLit::new(eq_ab, true),
            TheoryLit::new(eq_bc, true),
        ]),
        "incremental eq_adj maintenance must preserve transitive equality reasons"
    );

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "check() after warm-cache equality updates should reuse the incremental indices"
    );
}

#[test]
fn test_warm_cache_disequalities_update_assignment_indices_incrementally() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);

    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "initial cache warm-up should perform one full assignment-index rebuild"
    );

    solver.assert_literal(eq_ab, false);

    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "warm-cache disequalities should update diseq_set incrementally"
    );
    assert_eq!(
        solver.explain_distinct_if_provable(a, b),
        Some(vec![TheoryLit::new(eq_ab, false)]),
        "incremental diseq_set maintenance must preserve the direct disequality reason"
    );

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "check() after warm-cache disequalities should reuse the incremental indices"
    );
}

#[test]
fn test_late_registered_true_equality_avoids_full_assignment_rebuild() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "initial cache warm-up should perform one full assignment-index rebuild"
    );

    // Synthetic late-registration setup: direct unit tests cannot mutate
    // `TermStore` after `ArraySolver` borrows it, so rewind the cache to
    // make the final equality atom look newly interned.
    solver.equality_cache.remove(&eq_ab);
    solver
        .eq_pair_index
        .remove(&ArraySolver::ordered_pair(a, b));
    solver.populated_terms = eq_ab.index();

    solver.assert_literal(eq_ab, true);
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "late equality assignments should queue incremental index updates"
    );

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "late-registered asserted equalities should not force a full rebuild"
    );
    assert_eq!(
        solver.explain_equal_if_provable(a, b),
        Some(vec![TheoryLit::new(eq_ab, true)]),
        "late-registered equality should still produce the direct equality reason"
    );
}

#[test]
fn test_late_registered_disequality_avoids_full_assignment_rebuild() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "initial cache warm-up should perform one full assignment-index rebuild"
    );

    // Synthetic late-registration setup: mirror the true-equality case for
    // a false assignment so the disequality path stays incremental too.
    solver.equality_cache.remove(&eq_ab);
    solver
        .eq_pair_index
        .remove(&ArraySolver::ordered_pair(a, b));
    solver.populated_terms = eq_ab.index();

    solver.assert_literal(eq_ab, false);
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "late disequality assignments should queue incremental index updates"
    );

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "late-registered disequalities should not force a full rebuild"
    );
    assert_eq!(
        solver.explain_distinct_if_provable(a, b),
        Some(vec![TheoryLit::new(eq_ab, false)]),
        "late-registered disequality should still produce the direct reason"
    );
}

#[test]
fn test_array_solver_reset() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, j);
    let eq_ij = store.mk_eq(i, j);
    let eq_sel_v = store.mk_eq(selected, v);

    let mut solver = ArraySolver::new(&store);

    // Create conflicting state: i = j but select(store(a,i,v), j) ≠ v
    solver.assert_literal(eq_ij, true);
    solver.assert_literal(eq_sel_v, false);
    // Batched-lemma check() converts ROW1 Unsat to NeedLemmas (#6546).
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from ROW1 conflict"
    );

    // Reset should clear state
    solver.reset();
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_array_equality_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    // Create select(a, i) and select(b, i)
    let sel_a = store.mk_select(a, i);
    let sel_b = store.mk_select(b, i);

    // Create equalities
    let eq_ab = store.mk_eq(a, b);
    let eq_sels = store.mk_eq(sel_a, sel_b);

    let mut solver = ArraySolver::new(&store);

    // Assert a = b
    solver.assert_literal(eq_ab, true);
    // Assert select(a, i) ≠ select(b, i) - contradicts array equality
    solver.assert_literal(eq_sels, false);

    solver.populate_caches();
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_array_equality()
        .expect("expected array-equality helper to emit a lemma")
    else {
        panic!("expected NeedLemmas from array-equality helper");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "array-equality conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ab, false), TheoryLit::new(eq_sels, true)],
        "array-equality lemma must block a=b and select(a,i)!=select(b,i)"
    );
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_var_eq_store_row2() {
    // Test: B = store(A, 0, v), and we select at index 1
    // select(B, 1) should equal select(A, 1) because 0 ≠ 1
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("A", arr_sort.clone());
    let b = store.mk_var("B", arr_sort);
    let v = store.mk_var("v", Sort::Int);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));

    // store(A, 0, v)
    let store_term = store.mk_store(a, zero, v);
    // B = store(A, 0, v)
    let eq_b_store = store.mk_eq(b, store_term);

    // select(A, 1) and select(B, 1)
    let sel_a_1 = store.mk_select(a, one);
    let sel_b_1 = store.mk_select(b, one);

    // x = select(A, 1) and y = select(B, 1)
    let eq_x_sel = store.mk_eq(x, sel_a_1);
    let eq_y_sel = store.mk_eq(y, sel_b_1);

    // x ≠ y
    let eq_xy = store.mk_eq(x, y);

    let mut solver = ArraySolver::new(&store);

    // Assert the equalities
    solver.assert_literal(eq_b_store, true); // B = store(A, 0, v)
    solver.assert_literal(eq_x_sel, true); // x = select(A, 1)
    solver.assert_literal(eq_y_sel, true); // y = select(B, 1)
    solver.assert_literal(eq_xy, false); // x ≠ y

    // This SHOULD be UNSAT because:
    // B = store(A, 0, v) and 0 ≠ 1 implies select(B, 1) = select(A, 1)
    // So x = select(A, 1) = select(B, 1) = y, contradiction with x ≠ y
    // Batched-lemma check() may convert Unsat to NeedLemmas (#6546).
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "Expected UNSAT or NeedLemmas but got {result:?}"
    );
}
