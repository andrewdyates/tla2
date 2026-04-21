// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use z4_core::term::TermStore;

fn arrays_check_count(combiner: &TheoryCombiner<'_>) -> u64 {
    let arrays = combiner
        .arrays
        .as_ref()
        .expect("test requires array solver");
    arrays
        .collect_statistics()
        .into_iter()
        .find_map(|(name, value)| (name == "arrays_checks").then_some(value))
        .expect("arrays solver should report arrays_checks")
}

#[test]
fn test_check_arrays_step_skips_quiescent_array_solver_6820() {
    use z4_core::term::Symbol;
    use z4_core::ArraySort;

    let mut terms = TermStore::new();
    // Create an array-related literal: (= a b) where a, b : (Array Int Int)
    let arr_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort);
    let arr_eq = terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
    // Create a non-array literal: a plain Bool variable
    let bool_lit = terms.mk_var("p", Sort::Bool);
    // Int-sorted equality: (= i j) — feeds array diseq_set via equality_cache
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let int_eq = terms.mk_app(Symbol::named("="), vec![i, j], Sort::Bool);

    let mut combiner = TheoryCombiner::auf_lia(&terms);

    assert_eq!(arrays_check_count(&combiner), 0);
    assert!(!combiner
        .check_arrays_step(false, 0)
        .expect("initial empty array step should succeed"));
    assert_eq!(arrays_check_count(&combiner), 1);

    assert!(!combiner
        .check_arrays_step(false, 1)
        .expect("quiescent array step should still succeed"));
    assert_eq!(
        arrays_check_count(&combiner),
        1,
        "second quiescent check must skip redundant arrays.check()"
    );

    // Non-array literal should NOT invalidate quiescence (#6820)
    combiner.assert_literal(bool_lit, true);
    assert!(!combiner
        .check_arrays_step(false, 2)
        .expect("non-array literal should not force re-check"));
    assert_eq!(
        arrays_check_count(&combiner),
        1,
        "non-array literal must not invalidate array quiescence"
    );

    // Array-related literal SHOULD invalidate quiescence
    combiner.assert_literal(arr_eq, true);
    assert!(!combiner
        .check_arrays_step(false, 3)
        .expect("array literal should re-run arrays.check()"));
    assert_eq!(arrays_check_count(&combiner), 2);

    // Int-sorted equality SHOULD invalidate quiescence (e87f539 broadened
    // involves_array to include all =/distinct — index equalities like
    // (= i j) feed the array solver's diseq_set through equality_cache).
    // First, re-establish quiescence.
    assert!(!combiner
        .check_arrays_step(false, 4)
        .expect("post-array quiescent step should succeed"));
    assert_eq!(
        arrays_check_count(&combiner),
        2,
        "should still be quiescent"
    );

    combiner.assert_literal(int_eq, true);
    assert!(!combiner
        .check_arrays_step(false, 5)
        .expect("Int equality should force re-check for diseq_set"));
    assert_eq!(
        arrays_check_count(&combiner),
        3,
        "Int equality must invalidate array quiescence — feeds diseq_set"
    );
}
