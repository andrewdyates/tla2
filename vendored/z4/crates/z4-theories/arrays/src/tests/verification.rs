// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Conflict soundness tests (Part of #298)
// These tests verify that conflict explanations are semantically sound:
// re-solving with just the conflict literals must still be UNSAT.
// ========================================================================

/// Verify ROW1 conflict explanations are sound.
/// ROW1: select(store(a, i, v), i) = v
#[test]
fn test_arrays_row1_conflict_soundness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // store(a, i, v) and select(store(a, i, v), j)
    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, j);

    let eq_ij = store.mk_eq(i, j);
    let eq_sel_v = store.mk_eq(selected, v);

    let mut solver = ArraySolver::new(&store);

    // Assert i = j (so ROW1 applies) and select(...) ≠ v (contradiction)
    solver.assert_literal(eq_ij, true);
    solver.assert_literal(eq_sel_v, false);

    solver.populate_caches();
    let result = solver
        .check_row1()
        .expect("expected ROW1 helper to emit a lemma");
    assert!(
        matches!(&result, TheoryResult::NeedLemmas(_)),
        "ROW1 helper should now route through lemma emission, got {result:?}"
    );
    assert_conflict_soundness(result, ArraySolver::new(&store));
}

/// Verify ROW2 conflict explanations are sound.
/// ROW2: i ≠ j → select(store(a, i, v), j) = select(a, j)
#[test]
fn test_arrays_row2_conflict_soundness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // store(a, i, v), select(store(a, i, v), j), and select(a, j)
    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);

    // Assert i ≠ j and select(store(a,i,v), j) ≠ select(a, j) (contradicts ROW2)
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);

    // #6694: After restoring Unsat early-returns in check(), a conflict
    // check (store-chain resolution or nested-select) may detect the
    // contradiction directly as Unsat before check_row2() emits NeedLemmas.
    // Both are sound — ROW2 says i≠j → select(store(a,i,v),j)=select(a,j),
    // so asserting both i≠j and sel(store)≠sel(a) is unsatisfiable.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from ROW2 contradiction, got {result:?}",
    );
}

#[test]
fn test_arrays_row2_direct_conflict_soundness() {
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
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: sel_stored_j,
        }],
        "ROW2 direct check should consume the registered store/select pair"
    );

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2()
        .expect("ROW2 direct path should emit one permanent clause")
    else {
        panic!("expected NeedLemmas from ROW2 direct path");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "expected one ROW2 clause for the queued pair"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_sels, true)],
        "ROW2 clause must assert i=j or select(store(a,i,v),j)=select(a,j)"
    );
}

#[test]
fn test_arrays_row2_batches_multiple_lemmas() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let l = store.mk_var("l", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let stored1 = store.mk_store(a, i, v1);
    let stored2 = store.mk_store(a, k, v2);
    let sel_stored1_j = store.mk_select(stored1, j);
    let sel_stored2_l = store.mk_select(stored2, l);
    let sel_a_j = store.mk_select(a, j);
    let sel_a_l = store.mk_select(a, l);

    let eq_ij = store.mk_eq(i, j);
    let eq_kl = store.mk_eq(k, l);
    let eq_sel1 = store.mk_eq(sel_stored1_j, sel_a_j);
    let eq_sel2 = store.mk_eq(sel_stored2_l, sel_a_l);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sel1, false);
    solver.assert_literal(eq_kl, false);
    solver.assert_literal(eq_sel2, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2()
        .expect("expected batched ROW2 lemmas for two queued pairs")
    else {
        panic!("expected NeedLemmas from batched ROW2");
    };

    assert_eq!(lemmas.len(), 2, "expected one lemma per violated ROW2 pair");

    let clauses: HashSet<Vec<(TermId, bool)>> = lemmas
        .iter()
        .map(|lemma| {
            lemma
                .clause
                .iter()
                .map(|lit| (lit.term, lit.value))
                .collect::<Vec<_>>()
        })
        .collect();

    assert!(
        clauses.contains(&vec![(eq_ij, true), (eq_sel1, true)]),
        "first ROW2 clause should assert i=j or select(store(a,i,v1),j)=select(a,j)"
    );
    assert!(
        clauses.contains(&vec![(eq_kl, true), (eq_sel2, true)]),
        "second ROW2 clause should assert k=l or select(store(a,k,v2),l)=select(a,l)"
    );
    // After emitting lemmas, axioms are drained — second call returns None.
    // DpllT applies NeedLemmas as permanent SAT clauses in-place, so
    // re-emitting is redundant (#6546).
    assert!(
        solver.check_row2().is_none(),
        "emitted ROW2 axioms should be drained after first lemma emit"
    );
}

/// Verify that check_row2 drains axioms after emitting their lemma clause.
/// DpllT applies NeedLemmas as permanent clauses in-place, so re-emitting
/// is redundant. The drain avoids O(total_axioms) re-scanning (#6546).
#[test]
fn test_arrays_row2_drains_after_lemma_emit() {
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
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) =
        solver.check_row2().expect("expected ROW2 lemma request")
    else {
        panic!("expected NeedLemmas from ROW2 check");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW2 lemma clause");

    // After emitting the lemma, the axiom is drained — second call returns None.
    assert!(
        solver.check_row2().is_none(),
        "emitted ROW2 axiom should be drained after first lemma emit"
    );
}

#[test]
fn test_arrays_row2_dirty_rebuild_does_not_requeue_emitted_axiom() {
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
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2()
        .expect("expected ROW2 lemma request before dirty rebuild")
    else {
        panic!("expected NeedLemmas from ROW2 check");
    };
    assert_eq!(lemmas.len(), 1, "expected one emitted ROW2 lemma clause");
    assert!(
        solver.pending_axioms.is_empty(),
        "emitted ROW2 axiom should be drained before the rebuild"
    );

    // Simulate the split-loop dirty rebuild that repopulates array caches
    // after the SAT solver has already installed the permanent clause.
    solver.dirty = true;
    solver.populate_caches();

    assert!(
        solver.pending_axioms.is_empty(),
        "dirty rebuild must not requeue a ROW2 axiom whose fingerprint already exists"
    );
    assert!(
        solver.check_row2().is_none(),
        "dirty rebuild must not re-emit an already-applied ROW2 lemma"
    );
}

#[test]
fn test_arrays_row2_reset_requeues_unemitted_axiom() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: sel_stored_j,
        }],
        "baseline ROW2 pair should be queued before reset"
    );

    // No clause was emitted yet, so reset must not leave behind a stale
    // fingerprint that suppresses re-queuing the same structural pair.
    solver.reset();
    solver.populate_caches();

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: sel_stored_j,
        }],
        "reset must requeue un-emitted ROW2 axioms on the rebuilt problem state"
    );
    assert_eq!(
        solver.row2_down_clause_terms(stored, sel_stored_j),
        Some((i, j, sel_a_j)),
        "rebuilt caches must still recover the ROW2 base-select clause terms"
    );
    assert!(
        solver.requested_model_eqs.is_empty(),
        "reset must clear model-equality request dedup before ROW2 re-check"
    );

    let TheoryResult::NeedModelEqualities(requests) = solver
        .check_row2()
        .expect("re-queued ROW2 pair should request the missing clause atoms")
    else {
        panic!("expected NeedModelEqualities after reset re-queued the ROW2 pair");
    };
    assert_eq!(
        requests.len(),
        2,
        "reset should restore both missing ROW2 equality requests"
    );
}

#[test]
fn test_arrays_row2_requests_missing_clause_atoms_once() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();

    let TheoryResult::NeedModelEqualities(requests) = solver
        .check_row2()
        .expect("missing equality atoms should be requested before ROW2 clause emission")
    else {
        panic!("expected NeedModelEqualities for missing ROW2 clause atoms");
    };
    assert_eq!(
        requests.len(),
        2,
        "expected index and value equality requests"
    );
    assert!(
        requests
            .iter()
            .any(|request| request.lhs == i && request.rhs == j),
        "ROW2 should request the missing index equality atom"
    );
    assert!(
        requests
            .iter()
            .any(|request| request.lhs == sel_stored_j && request.rhs == sel_a_j),
        "ROW2 should request the missing select equality atom"
    );

    assert!(
        solver.check_row2().is_none(),
        "duplicate missing equality requests should be suppressed until new atoms appear"
    );
}

#[test]
fn test_array_var_tracking_registers_store_select_relationships() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_on_store = store.mk_select(stored, j);
    let select_on_base = store.mk_select(a, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();

    let base_data = solver
        .array_vars
        .get(&a)
        .expect("base array should be tracked");
    assert_eq!(
        base_data.parent_selects,
        vec![select_on_base],
        "base array should track its parent select"
    );
    assert_eq!(
        base_data.parent_stores,
        vec![stored],
        "base array should track parent stores that read from it"
    );
    assert!(
        base_data.prop_upward,
        "base array with both a parent store and parent select must request upward ROW2 work"
    );

    let result_data = solver
        .array_vars
        .get(&stored)
        .expect("store result array should be tracked");
    assert_eq!(
        result_data.stores_as_result,
        vec![stored],
        "store result should track itself as a result array"
    );
    assert_eq!(
        result_data.parent_selects,
        vec![select_on_store],
        "store result should track selects over the stored array"
    );
    assert_eq!(
        solver.get_exact_select_term(a, j),
        Some(select_on_base),
        "exact select lookup should recover the base-array select term"
    );
    assert_eq!(
        solver.get_exact_select_term(stored, j),
        Some(select_on_store),
        "exact select lookup should recover the store-result select term"
    );

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: select_on_store,
        }],
        "one ROW2-down axiom should be queued for the store-result select"
    );
    assert!(
        solver.axiom_fingerprints.contains(&(stored, j)),
        "ROW2 fingerprint should be keyed by the store term and select index"
    );
    assert_eq!(
        solver.populated_terms,
        store.len(),
        "populate_caches should advance the high-water mark"
    );
}

#[test]
fn test_array_var_tracking_repopulate_is_idempotent() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_on_store = store.mk_select(stored, j);
    let select_on_base = store.mk_select(a, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    let expected_vars = solver.array_vars.clone();
    let expected_axioms = solver.pending_axioms.clone();
    let expected_fingerprints = solver.axiom_fingerprints.clone();

    solver.populate_caches();

    assert_eq!(
        solver.array_vars, expected_vars,
        "re-running populate_caches without new terms must not duplicate per-array tracking"
    );
    assert_eq!(
        solver.pending_axioms, expected_axioms,
        "re-running populate_caches without new terms must not queue duplicate axioms"
    );
    assert_eq!(
        solver.axiom_fingerprints, expected_fingerprints,
        "re-running populate_caches without new terms must not add duplicate fingerprints"
    );
    assert!(
        solver
            .array_vars
            .get(&a)
            .is_some_and(|data| data.parent_selects == vec![select_on_base]),
        "base array tracking should remain stable across repeated cache populations"
    );
    assert!(
        solver
            .array_vars
            .get(&stored)
            .is_some_and(|data| data.parent_selects == vec![select_on_store]),
        "store-result tracking should remain stable across repeated cache populations"
    );
}

#[test]
fn test_row2_fingerprint_dedups_equal_index_aliases() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_j = store.mk_select(stored, j);
    let select_k = store.mk_select(stored, k);
    let eq_jk = store.mk_eq(j, k);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.pending_axioms.clear();
    solver.axiom_fingerprints.clear();
    solver.row2_fingerprint_indices.clear();

    solver.queue_row2_down_axiom(stored, select_j);
    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: select_j,
        }],
        "first ROW2 candidate should be queued exactly once"
    );

    solver.assert_literal(eq_jk, true);
    solver.queue_row2_down_axiom(stored, select_k);

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: select_j,
        }],
        "current-equality dedup should suppress a second ROW2 axiom for an alias-equivalent index"
    );
    assert_eq!(
        solver
            .row2_fingerprint_indices
            .get(&stored)
            .cloned()
            .unwrap_or_default(),
        vec![j],
        "only the exact queued index should be kept in the persistent fingerprint history"
    );
}

#[test]
fn test_row2_fingerprint_dedup_is_backtrack_safe() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_j = store.mk_select(stored, j);
    let select_k = store.mk_select(stored, k);
    let eq_jk = store.mk_eq(j, k);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.pending_axioms.clear();
    solver.axiom_fingerprints.clear();
    solver.row2_fingerprint_indices.clear();

    solver.queue_row2_down_axiom(stored, select_j);
    solver.push();
    solver.assert_literal(eq_jk, true);
    solver.queue_row2_down_axiom(stored, select_k);
    assert_eq!(
        solver.pending_axioms.len(),
        1,
        "branch-local equality should suppress alias-equivalent ROW2 work"
    );

    solver.pop();
    solver.populate_caches();
    solver.queue_row2_down_axiom(stored, select_k);

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: select_k,
        }],
        "after backtracking the alias equality away, the distinct exact index must queue normally"
    );
    assert_eq!(
        solver
            .row2_fingerprint_indices
            .get(&stored)
            .cloned()
            .unwrap_or_default(),
        vec![j, k],
        "persistent fingerprint history should retain both exact indices once they are queued in distinct branches"
    );
}

#[test]
fn test_array_var_tracking_notify_equality_repopulate_keeps_merged_state() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let select_on_a = store.mk_select(a, j);
    let store_on_b = store.mk_store(b, i, v);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.notify_equality(a, b);

    let merged = solver
        .array_vars
        .get(&a)
        .expect("notify_equality should preserve merged array data");
    assert_eq!(
        merged.parent_selects,
        vec![select_on_a],
        "target array should keep its original parent select"
    );
    assert_eq!(
        merged.parent_stores,
        vec![store_on_b],
        "target array should inherit parent stores from the equal array"
    );
    assert!(
        merged.prop_upward,
        "merged array data should request upward ROW2 when stores and selects come from different equal arrays"
    );

    solver.populate_caches();

    let merged = solver
        .array_vars
        .get(&a)
        .expect("merged array data should survive repopulation");
    assert_eq!(
        merged.parent_selects,
        vec![select_on_a],
        "repopulation must preserve the target array's parent select"
    );
    assert_eq!(
        merged.parent_stores,
        vec![store_on_b],
        "repopulation must preserve equality-driven parent stores"
    );
    assert!(
        merged.prop_upward,
        "repopulation must not drop upward ROW2 eligibility derived from merged data"
    );
}

#[test]
fn test_array_var_tracking_assert_literal_true_queues_cross_equal_row2() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let select_on_a = store.mk_select(a, j);
    let store_on_b = store.mk_store(b, i, v);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);

    let merged = solver
        .array_vars
        .get(&a)
        .expect("asserted array equality should merge direct ArrayVarData");
    assert_eq!(
        merged.parent_selects,
        vec![select_on_a],
        "direct array equality should preserve target parent selects"
    );
    assert_eq!(
        merged.parent_stores,
        vec![store_on_b],
        "direct array equality should inherit parent stores from the equal array"
    );
    assert!(
        merged.prop_upward,
        "direct array equality should mark the merged array for upward ROW2"
    );
    assert!(
        solver.pending_axioms.contains(&PendingAxiom::Row2Down {
            store: store_on_b,
            select: select_on_a,
        }),
        "direct array equality should queue the cross-array ROW2 axiom"
    );
    assert!(
        solver.axiom_fingerprints.contains(&(store_on_b, j)),
        "queued direct-equality ROW2 work should record its fingerprint"
    );
}

#[test]
fn test_array_var_tracking_assert_literal_unwraps_not_equalities() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let select_on_a = store.mk_select(a, j);
    let store_on_b = store.mk_store(b, i, v);
    let eq_ab = store.mk_eq(a, b);
    let not_eq_ab = store.mk_not(eq_ab);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(not_eq_ab, false);

    let merged = solver
        .array_vars
        .get(&a)
        .expect("false on not(= a b) should be treated as a = b");
    assert_eq!(
        merged.parent_selects,
        vec![select_on_a],
        "negated equality literal should unwrap before merging parent selects"
    );
    assert_eq!(
        merged.parent_stores,
        vec![store_on_b],
        "negated equality literal should unwrap before merging parent stores"
    );
    assert!(
        solver.pending_axioms.contains(&PendingAxiom::Row2Down {
            store: store_on_b,
            select: select_on_a,
        }),
        "negated equality literal should still queue the direct-equality ROW2 axiom"
    );
}

#[test]
fn test_disjunctive_store_target_guidance_tracks_direct_store_equalities_6885() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let store_x = store.mk_store(a, x, v);
    let store_y = store.mk_store(a, y, w);
    let eq_store_x_b = store.mk_eq(store_x, b);
    let eq_store_y_b = store.mk_eq(store_y, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_x_b, true);
    solver.assert_literal(eq_store_y_b, true);

    let result = solver.check_disjunctive_store_target_equalities();
    let TheoryResult::NeedModelEqualities(requests) =
        result.expect("dual store equalities should request disjunctive guidance")
    else {
        panic!("expected NeedModelEqualities for dual store guidance");
    };

    assert_eq!(
        requests.len(),
        2,
        "should request both disjunctive branches"
    );
    assert!(
        requests
            .iter()
            .any(|req| ArraySolver::ordered_pair(req.lhs, req.rhs)
                == ArraySolver::ordered_pair(x, y)),
        "must request the store-index equality branch"
    );
    assert!(
        requests
            .iter()
            .any(|req| ArraySolver::ordered_pair(req.lhs, req.rhs)
                == ArraySolver::ordered_pair(a, b)),
        "must request the base-target equality branch"
    );
}

/// Verify array equality conflict explanations are sound.
/// If a = b, then select(a, i) = select(b, i)
#[test]
fn test_arrays_equality_conflict_soundness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    let sel_a = store.mk_select(a, i);
    let sel_b = store.mk_select(b, i);

    let eq_ab = store.mk_eq(a, b);
    let eq_sels = store.mk_eq(sel_a, sel_b);

    let mut solver = ArraySolver::new(&store);

    // Assert a = b and select(a, i) ≠ select(b, i) (contradiction)
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_sels, false);

    solver.populate_caches();
    let result = solver
        .check_array_equality()
        .expect("expected array-equality helper to emit a lemma");
    assert!(
        matches!(&result, TheoryResult::NeedLemmas(_)),
        "array-equality helper should now route through lemma emission, got {result:?}"
    );
    assert_conflict_soundness(result, ArraySolver::new(&store));
}
