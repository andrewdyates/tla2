// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_arrays_store_chain_resolution_conflict_emits_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let i_plus_1 = store.mk_add(vec![i, one]);
    let eq_j_i_plus_1 = store.mk_eq(j, i_plus_1);

    let stored_at_i = store.mk_store(a, i, v1);
    let nested = store.mk_store(stored_at_i, j, v2);
    let select_at_i = store.mk_select(nested, i);
    let eq_select_v1 = store.mk_eq(select_at_i, v1);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_j_i_plus_1, true);
    solver.assert_literal(eq_select_v1, false);

    // After #6820, the array theory no longer derives index disequalities from
    // arithmetic facts like j = i+1. That reasoning is delegated to the LIA
    // solver, which propagates j ≠ i into the array theory's diseq_set via
    // assert_external_disequality_with_reasons. Simulate that here.
    solver.assert_external_disequality_with_reasons(
        i,
        j,
        vec![TheoryLit::new(eq_j_i_plus_1, true)],
    );

    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("expected NeedLemmas from store-chain resolution conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "store-chain resolution conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_j_i_plus_1, false),
            TheoryLit::new(eq_select_v1, true),
        ],
        "store-chain lemma must block the ROW2 skip reason with the conflicting select disequality"
    );
}

#[test]
fn test_arrays_conflicting_store_equalities_conflict_emits_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let first_store = store.mk_store(a, i, v1);
    let second_store = store.mk_store(a, j, v2);
    let eq_stores = store.mk_eq(first_store, second_store);
    let eq_ij = store.mk_eq(i, j);
    let eq_vals = store.mk_eq(v1, v2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_stores, true);
    solver.assert_literal(eq_ij, true);
    solver.assert_literal(eq_vals, false);

    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("expected NeedLemmas from conflicting-store-equalities conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "conflicting store equalities should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_stores, false),
            TheoryLit::new(eq_ij, false),
            TheoryLit::new(eq_vals, true),
        ],
        "conflicting-store-equalities lemma must block equal stores with equal indices and distinct values"
    );
}

#[test]
fn test_arrays_disjunctive_store_target_equalities_emit_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let first_store = store.mk_store(a, x, v);
    let second_store = store.mk_store(a, y, w);
    let eq_first = store.mk_eq(first_store, b);
    let eq_second = store.mk_eq(second_store, b);
    let eq_xy = store.mk_eq(x, y);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_first, true);
    solver.assert_literal(eq_second, true);
    solver.assert_literal(eq_xy, false);
    solver.assert_literal(eq_ab, false);

    let TheoryResult::NeedLemmas(lemmas) = solver.final_check() else {
        panic!("expected NeedLemmas from disjunctive store-target equalities");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "disjunctive store-target equalities should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_first, false),
            TheoryLit::new(eq_second, false),
            TheoryLit::new(eq_xy, true),
            TheoryLit::new(eq_ab, true),
        ],
        "lemma must force x=y or a=b when two same-base stores equal the same target"
    );
}

/// Verify no false positives - SAT case must stay SAT.
#[test]
fn test_arrays_no_bogus_conflict_on_sat() {
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

    // Assert i ≠ j and select(store(a,i,v), j) = select(a, j)
    // This is SAT - consistent with ROW2. The ROW2 clause is already
    // satisfied by the assignment, so check() must return Sat — not
    // NeedLemmas with a redundant clause (#6738).
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "ROW2-satisfied assignment must return Sat, got: {result:?}"
    );
}

/// Verify const-array conflict explanations are sound.
/// Tests the const-array axiom: select(const-array(v), i) = v
#[test]
fn test_arrays_const_array_conflict_soundness() {
    let mut store = TermStore::new();
    let default_val = store.mk_var("default", Sort::Int);
    let const_arr = store.mk_const_array(Sort::Int, default_val);
    let i = store.mk_var("i", Sort::Int);

    // select(const-array(default), i)
    let selected = store.mk_select(const_arr, i);

    // Note: mk_select already simplifies select(const-array(v), i) → v
    // So selected == default_val due to term normalization
    // This tests that the simplification works correctly

    // Verify the simplification happened
    assert_eq!(
        selected, default_val,
        "select(const-array(v), i) should simplify to v"
    );

    // Since the terms are identical, any test asserting them different
    // would be asserting v ≠ v which is immediately false at the term level.
    // This test verifies the term-level simplification is working.
}

/// Verify extended ROW2 conflict via store chain following.
/// Tests the check_row2_extended path.
#[test]
fn test_arrays_row2_extended_conflict_soundness() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let v = store.mk_var("v", Sort::Int);

    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));

    // B = store(A, 0, v)
    let store_a = store.mk_store(a, idx0, v);
    let eq_b_store = store.mk_eq(b, store_a);

    // select(A, 1) and select(B, 1)
    let sel_a_1 = store.mk_select(a, idx1);
    let sel_b_1 = store.mk_select(b, idx1);
    let eq_sels = store.mk_eq(sel_a_1, sel_b_1);

    let mut solver = ArraySolver::new(&store);

    // Assert B = store(A, 0, v) and select(A, 1) ≠ select(B, 1)
    // Since 0 ≠ 1, by ROW2: select(B, 1) = select(A, 1), so UNSAT
    solver.assert_literal(eq_b_store, true);
    solver.assert_literal(eq_sels, false);

    let result = solver.check();
    let conflict = assert_conflict_soundness(result, ArraySolver::new(&store));

    // Conflict should be reasonably minimal (≤4 literals)
    assert!(
        conflict.len() <= 4,
        "Conflict too large: {} literals",
        conflict.len()
    );
}

#[test]
fn test_arrays_row2_extended_conflict_via_constant_equalities() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let v = store.mk_var("v", Sort::Int);

    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));

    let store_a = store.mk_store(a, idx0, v);
    let eq_b_store = store.mk_eq(b, store_a);
    let sel_a_1 = store.mk_select(a, idx1);
    let sel_b_1 = store.mk_select(b, idx1);
    let eq_sel_a_zero = store.mk_eq(sel_a_1, zero);
    let eq_sel_b_one = store.mk_eq(sel_b_1, one);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_b_store, true);
    solver.assert_literal(eq_sel_a_zero, true);
    solver.assert_literal(eq_sel_b_one, true);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2_extended()
        .expect("constant-backed select conflict should be discovered")
    else {
        panic!("expected NeedLemmas from ROW2-extended constant conflict");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW2-extended lemma");
    assert!(
        lemmas[0]
            .clause
            .contains(&TheoryLit::new(eq_b_store, false)),
        "lemma must negate the asserted store/base equality antecedent"
    );
    assert!(
        lemmas[0]
            .clause
            .contains(&TheoryLit::new(eq_sel_a_zero, false)),
        "lemma must retain the left select-to-constant equality reason"
    );
    assert!(
        lemmas[0]
            .clause
            .contains(&TheoryLit::new(eq_sel_b_one, false)),
        "lemma must retain the right select-to-constant equality reason"
    );
}

/// Verify upward ROW2 conflict detection directly.
///
/// Call `check_row2_upward()` instead of `check()` so this test exercises
/// the axiom-2b path even though the main check order reaches downward
/// ROW2 first for the same syntactic pattern.
#[test]
fn test_arrays_row2_upward_conflict_soundness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_a_j = store.mk_select(a, j);
    let sel_stored_j = store.mk_select(stored, j);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_a_j, sel_stored_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let result = solver
        .check_row2_upward()
        .expect("ROW2 upward should detect direct store/base conflict");
    let conflict = match result {
        TheoryResult::Unsat(conflict) => conflict,
        other => panic!("expected upward ROW2 conflict, got {other:?}"),
    };

    let mut verify_solver = ArraySolver::new(&store);
    for lit in &conflict {
        verify_solver.assert_literal(lit.term, lit.value);
    }
    verify_solver.populate_caches();
    assert!(
        matches!(
            verify_solver.check_row2_upward(),
            Some(TheoryResult::Unsat(_))
        ),
        "upward ROW2 conflict literals must still trigger the upward conflict path"
    );

    assert!(
        conflict.iter().any(|lit| lit.term == eq_ij && !lit.value),
        "ROW2 upward conflict must include the asserted index disequality"
    );
    assert!(
        conflict.iter().any(|lit| lit.term == eq_sels && !lit.value),
        "ROW2 upward conflict must include the asserted select disequality"
    );
}

#[test]
fn test_arrays_row2_upward_guidance_batches_multiple_requests() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let s1 = store.mk_store(a, i, v1);
    let s2 = store.mk_store(a, j, v2);
    let _sel_a_k = store.mk_select(a, k);
    let _sel_s1_k = store.mk_select(s1, k);
    let _sel_s2_k = store.mk_select(s2, k);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();

    let result = solver
        .check_row2_upward_with_guidance()
        .expect("expected ROW2-upward guidance request");

    match result {
        TheoryResult::NeedModelEqualities(requests) => {
            assert_eq!(
                requests.len(),
                2,
                "one base select with two parent stores should batch both undecided pairs"
            );
            assert!(
                requests
                    .iter()
                    .any(|req| req.lhs == i && req.rhs == k || req.lhs == k && req.rhs == i),
                "batched guidance must include the first store index pair"
            );
            assert!(
                requests
                    .iter()
                    .any(|req| req.lhs == j && req.rhs == k || req.lhs == k && req.rhs == j),
                "batched guidance must include the second store index pair"
            );
        }
        other => panic!("expected NeedModelEqualities, got {other:?}"),
    }
}

#[test]
fn test_arrays_row2_upward_guidance_conflict_emits_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_a_j = store.mk_select(a, j);
    let sel_stored_j = store.mk_select(stored, j);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_a_j, sel_stored_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2_upward_with_guidance()
        .expect("ROW2 upward guidance should emit a lemma for a proven conflict")
    else {
        panic!("expected NeedLemmas from ROW2-upward guidance conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "ROW2-upward conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_sels, true)],
        "ROW2-upward lemma must block index disequality plus select disequality"
    );
}

#[test]
fn test_arrays_final_check_returns_row2_extended_lemma_when_deferred() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let v = store.mk_var("v", Sort::Int);

    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));

    let store_a = store.mk_store(a, idx0, v);
    let eq_b_store = store.mk_eq(b, store_a);
    let sel_a_1 = store.mk_select(a, idx1);
    let sel_b_1 = store.mk_select(b, idx1);
    let eq_sels = store.mk_eq(sel_a_1, sel_b_1);

    let mut solver = ArraySolver::new(&store);
    solver.set_defer_expensive_checks(true);
    solver.assert_literal(eq_b_store, true);
    solver.assert_literal(eq_sels, false);

    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "deferred expensive checks should leave ROW2-extended for final_check()"
    );

    let TheoryResult::NeedLemmas(lemmas) = solver.final_check() else {
        panic!("expected NeedLemmas from deferred ROW2-extended conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "final_check should emit one deferred lemma"
    );
    assert!(
        lemmas[0]
            .clause
            .contains(&TheoryLit::new(eq_b_store, false)),
        "ROW2-extended lemma must include the store/base equality antecedent"
    );
    assert!(
        lemmas[0].clause.contains(&TheoryLit::new(eq_sels, true)),
        "ROW2-extended lemma must negate the conflicting select disequality"
    );
}

#[test]
fn test_arrays_nested_select_conflict_emits_lemma() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let row_sort = make_array_sort();
    let heap_sort = Sort::array(Sort::Int, row_sort.clone());

    let heap = store.mk_var("heap", heap_sort.clone());
    let heap_alias = store.mk_var("heap_alias", heap_sort);
    let row = store.mk_var("row", row_sort);
    let zero = store.mk_int(BigInt::from(0));
    let field = store.mk_var("field", Sort::Int);

    let heap_with_row = store.mk_store(heap, zero, row);
    let eq_alias = store.mk_eq(heap_alias, heap_with_row);
    let nested_row = store.mk_select(heap_alias, zero);
    let sel_nested = store.mk_select(nested_row, field);
    let sel_row = store.mk_select(row, field);
    let eq_sels = store.mk_eq(sel_nested, sel_row);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_alias, true);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_nested_select_conflicts()
        .expect("nested select normalization should detect the conflict")
    else {
        panic!("expected NeedLemmas from nested-select conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "nested-select conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_alias, false), TheoryLit::new(eq_sels, true)],
        "nested-select lemma must negate the asserted disequality and retain the alias-to-store antecedent"
    );
}

#[test]
fn test_arrays_check_surfaces_row2_upward_guidance_without_defer_6282() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let s1 = store.mk_store(a, i, v1);
    let s2 = store.mk_store(a, j, v2);
    let _sel_a_k = store.mk_select(a, k);
    let _sel_s1_k = store.mk_select(s1, k);
    let _sel_s2_k = store.mk_select(s2, k);

    let mut solver = ArraySolver::new(&store);

    match solver.check() {
        TheoryResult::NeedModelEqualities(requests) => {
            assert_eq!(
                requests.len(),
                4,
                "check() should surface both downward ROW2 atom creation and upward guidance"
            );
            assert!(
                requests
                    .iter()
                    .any(|req| req.lhs == i && req.rhs == k || req.lhs == k && req.rhs == i),
                "requests must include the first index equality"
            );
            assert!(
                requests
                    .iter()
                    .any(|req| req.lhs == j && req.rhs == k || req.lhs == k && req.rhs == j),
                "requests must include the second index equality"
            );
        }
        other => panic!("expected NeedModelEqualities from check(), got {other:?}"),
    }
}

/// Test for issue #920: store-select soundness - term-level fix
///
/// The primary fix for #920 is in mk_eq() which rewrites:
///   (= (store a i v) a) -> (= (select a i) v)
///
/// This test verifies the rewrite happens correctly.
#[test]
fn test_issue_920_self_store_term_rewrite() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let bv8_sort = Sort::bitvec(8);
    let arr_sort = Sort::array(bv8_sort.clone(), bv8_sort.clone());

    // arr: (Array BV8 BV8)
    let arr = store.mk_var("arr", arr_sort);
    // i: BV8
    let i = store.mk_var("i", bv8_sort);
    // #x02: BV8 constant
    let two = store.mk_bitvec(BigInt::from(2), 8);

    // store(arr, i, #x02)
    let stored = store.mk_store(arr, i, two);
    // select(arr, i)
    let selected = store.mk_select(arr, i);

    // (= (store arr i #x02) arr) - should be rewritten to (= (select arr i) #x02)
    let eq_store_arr = store.mk_eq(stored, arr);
    // (= (select arr i) #x02)
    let eq_sel_two = store.mk_eq(selected, two);

    // Due to the term-level rewrite, these should be the SAME term (hash-consed)
    assert_eq!(
        eq_store_arr, eq_sel_two,
        "Issue #920: (= (store a i v) a) should rewrite to (= (select a i) v)"
    );
}

// Note: A defense-in-depth test for check_self_store() would require
// bypassing mk_eq's rewrite via private intern(). The check_self_store()
// function in ArraySolver provides a backup mechanism for incremental solving
// scenarios. The primary fix is the term-level rewrite in mk_eq().

/// Test that self-store with consistent select is SAT
#[test]
fn test_self_store_consistent_sat() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let bv8_sort = Sort::bitvec(8);
    let arr_sort = Sort::array(bv8_sort.clone(), bv8_sort.clone());

    let arr = store.mk_var("arr", arr_sort);
    let i = store.mk_var("i", bv8_sort);
    let two = store.mk_bitvec(BigInt::from(2), 8);

    let stored = store.mk_store(arr, i, two);
    let selected = store.mk_select(arr, i);

    let eq_store_arr = store.mk_eq(stored, arr);
    let eq_sel_two = store.mk_eq(selected, two);

    let mut solver = ArraySolver::new(&store);

    // Assert store(arr, i, #x02) = arr AND select(arr, i) = #x02
    // This is consistent and should be SAT
    solver.assert_literal(eq_store_arr, true);
    solver.assert_literal(eq_sel_two, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Self-store with consistent select should be SAT, got {result:?}"
    );
}

#[test]
fn test_self_store_register_store_queues_assigned_store_equality() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let arr = store.mk_var("arr", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(arr, i, v);
    let eq_store_alias = store.mk_eq(stored, alias);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_alias, true);
    solver.populate_caches();

    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "register_store() should queue already-assigned equalities involving the new store"
    );
}

#[test]
fn test_self_store_pending_pair_waits_for_base_alias() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let arr = store.mk_var("arr", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(arr, i, v);
    let select_alias = store.mk_select(alias, i);
    let eq_store_alias = store.mk_eq(stored, alias);
    let eq_alias_arr = store.mk_eq(alias, arr);
    let eq_select_v = store.mk_eq(select_alias, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_alias, true);
    solver.assert_literal(eq_select_v, false);
    solver.populate_caches();

    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "the store equality should be queued once the store term is registered"
    );
    assert!(
        solver.check_self_store().is_none(),
        "without alias = base, the queued self-store candidate should not conflict yet"
    );
    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "non-self-store pairs must be retained for later equality propagation"
    );

    solver.assert_literal(eq_alias_arr, true);
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_self_store()
        .expect("expected retained self-store work to emit a lemma once alias = base")
    else {
        panic!("expected NeedLemmas from retained self-store work");
    };

    assert_eq!(lemmas.len(), 1, "self-store conflict should emit one lemma");
    let clause = &lemmas[0].clause;
    assert_eq!(
        clause.len(),
        3,
        "expected store, alias, and select antecedents"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_store_alias, false)),
        "lemma should negate the queued store equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_alias_arr, false)),
        "lemma should include the alias-to-base equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_select_v, true)),
        "lemma should block select(alias, i) != v"
    );
    assert!(
        solver.pending_self_store.is_empty(),
        "once the retained pair produces a lemma it should be drained"
    );
}

#[test]
fn test_self_store_pending_pair_falls_back_to_index_alias_select() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let arr = store.mk_var("arr", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(arr, i, v);
    let select_alias_index = store.mk_select(alias, j);
    let eq_store_alias = store.mk_eq(stored, alias);
    let eq_alias_arr = store.mk_eq(alias, arr);
    let eq_j_i = store.mk_eq(j, i);
    let eq_select_v = store.mk_eq(select_alias_index, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_alias, true);
    solver.assert_literal(eq_select_v, false);
    solver.populate_caches();

    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "the alias-based self-store equality should be queued once the store term is registered"
    );
    assert!(
        solver.check_self_store().is_none(),
        "without alias = base, the queued self-store candidate should not conflict yet"
    );
    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "the self-store queue must retain work until the base alias arrives"
    );

    solver.assert_literal(eq_alias_arr, true);
    assert!(
        solver.check_self_store().is_none(),
        "without j = i, the alias-index select should still wait after alias = base"
    );
    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "the queue must retain the alias-based self-store work until the index alias arrives"
    );

    solver.assert_literal(eq_j_i, true);
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_self_store()
        .expect("expected alias-index select to conflict once j = i is asserted")
    else {
        panic!("expected NeedLemmas from alias-index self-store work");
    };

    assert_eq!(lemmas.len(), 1, "self-store conflict should emit one lemma");
    let clause = &lemmas[0].clause;
    assert_eq!(
        clause.len(),
        4,
        "expected store, base-alias, index-alias, and select antecedents"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_store_alias, false)),
        "lemma should negate the queued self-store equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_alias_arr, false)),
        "lemma should include the base-alias equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_j_i, false)),
        "lemma should include the index-alias equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_select_v, true)),
        "lemma should block select(alias, j) != v"
    );
}
