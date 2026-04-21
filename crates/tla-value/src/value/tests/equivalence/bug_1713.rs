// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bug #1713 regression: SET_INTERN_TABLE variant substitution.

use super::super::super::*;
use std::sync::Arc;

/// #1713: When the intern table substitutes Func(empty) for Tuple([]),
/// as_seq() must still return the empty sequence.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1713_intern_substitution_empty_func_for_tuple_as_seq() {
    // Clear intern table for deterministic test
    clear_set_intern_table();

    // Seed the intern table with a set containing Func(empty)
    let empty_func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![])));
    let _set1 = SortedSet::from_iter(vec![empty_func.clone()]);

    // Create a set with Tuple([]) - intern table substitutes Func(empty)
    let empty_tuple = Value::Tuple(vec![].into());
    let set2 = SortedSet::from_iter(vec![empty_tuple]);

    // Extract the element - may be Func(empty) due to substitution
    let element = set2.iter().next().unwrap();

    // as_seq() must work regardless of which variant the intern table returned
    let seq_result = element.as_seq();
    assert!(
        seq_result.is_some(),
        "as_seq() must handle intern-substituted Func variant, got {element:?}",
    );
    assert_eq!(seq_result.unwrap().len(), 0);

    clear_set_intern_table();
}

/// #1713: Non-empty variant substitution - Func([1|->a, 2|->b]) substituted
/// for Seq([a,b]), as_seq() must extract elements correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1713_intern_substitution_func_for_seq_nonempty() {
    clear_set_intern_table();

    // Seed intern table with a Func that has domain 1..2
    let func = {
        let mut fb = FuncBuilder::new();
        fb.insert(Value::SmallInt(1), Value::SmallInt(10));
        fb.insert(Value::SmallInt(2), Value::SmallInt(20));
        Value::Func(Arc::new(fb.build()))
    };
    let _set1 = SortedSet::from_iter(vec![func]);

    // Create set with equivalent Seq - intern table may substitute
    let seq = Value::Seq(Arc::new(
        vec![Value::SmallInt(10), Value::SmallInt(20)].into(),
    ));
    let set2 = SortedSet::from_iter(vec![seq]);

    let element = set2.iter().next().unwrap();

    // as_seq() must extract [10, 20] regardless of variant
    let seq_result = element.as_seq();
    assert!(
        seq_result.is_some(),
        "as_seq() must handle substituted variant: {element:?}",
    );
    let elements = seq_result.unwrap();
    assert_eq!(elements.len(), 2);
    assert_eq!(elements[0], Value::SmallInt(10));
    assert_eq!(elements[1], Value::SmallInt(20));

    clear_set_intern_table();
}

/// #1713: Reverse direction - Seq substituted for Func, to_func_coerced()
/// must still produce a FuncValue (BagsExt operations path).
/// Uses values (10, 20) distinct from keys (1, 2) to detect key-value confusion.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1713_intern_substitution_seq_for_func_to_func_coerced() {
    clear_set_intern_table();

    // Seed intern table with a Seq — values (10, 20) differ from implicit keys (1, 2)
    let seq = Value::Seq(Arc::new(
        vec![Value::SmallInt(10), Value::SmallInt(20)].into(),
    ));
    let _set1 = SortedSet::from_iter(vec![seq]);

    // Create set with equivalent Func - intern table may substitute to Seq
    let func = {
        let mut fb = FuncBuilder::new();
        fb.insert(Value::SmallInt(1), Value::SmallInt(10));
        fb.insert(Value::SmallInt(2), Value::SmallInt(20));
        Value::Func(Arc::new(fb.build()))
    };
    let set2 = SortedSet::from_iter(vec![func]);

    let element = set2.iter().next().unwrap();

    // to_func_coerced() must produce a FuncValue regardless of variant
    let func_result = element.to_func_coerced();
    assert!(
        func_result.is_some(),
        "to_func_coerced() must handle substituted Seq variant: {element:?}",
    );
    let fv = func_result.unwrap();
    assert_eq!(fv.domain_len(), 2);
    // Verify actual mapping content — values must be 10, 20 (not keys 1, 2)
    assert_eq!(fv.apply(&Value::SmallInt(1)), Some(&Value::SmallInt(10)));
    assert_eq!(fv.apply(&Value::SmallInt(2)), Some(&Value::SmallInt(20)));

    clear_set_intern_table();
}

/// #1713: Direct unit test - as_seq() handles all function-like variants.
/// This verifies the fix independent of intern table nondeterminism.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1713_as_seq_accepts_func_and_intfunc() {
    // Empty Func
    let empty_func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![])));
    let result = empty_func.as_seq();
    assert!(result.is_some(), "as_seq must accept empty Func");
    assert_eq!(result.unwrap().len(), 0);

    // Func with domain 1..3
    let func_1_3 = {
        let mut fb = FuncBuilder::new();
        fb.insert(Value::SmallInt(1), Value::string("a"));
        fb.insert(Value::SmallInt(2), Value::string("b"));
        fb.insert(Value::SmallInt(3), Value::string("c"));
        Value::Func(Arc::new(fb.build()))
    };
    let result = func_1_3.as_seq();
    assert!(result.is_some(), "as_seq must accept Func with domain 1..n");
    let elems = result.unwrap();
    assert_eq!(elems.len(), 3);
    assert_eq!(elems[0], Value::string("a"));
    assert_eq!(elems[1], Value::string("b"));
    assert_eq!(elems[2], Value::string("c"));

    // Func with non-1..n domain should return None
    let func_non_seq = {
        let mut fb = FuncBuilder::new();
        fb.insert(Value::string("x"), Value::SmallInt(1));
        fb.insert(Value::string("y"), Value::SmallInt(2));
        Value::Func(Arc::new(fb.build()))
    };
    assert!(
        func_non_seq.as_seq().is_none(),
        "as_seq must reject Func with non-integer domain"
    );

    // Func with integer domain not starting at 1 should return None
    let func_offset_domain = {
        let mut fb = FuncBuilder::new();
        fb.insert(Value::SmallInt(2), Value::SmallInt(100));
        fb.insert(Value::SmallInt(3), Value::SmallInt(200));
        Value::Func(Arc::new(fb.build()))
    };
    assert!(
        func_offset_domain.as_seq().is_none(),
        "as_seq must reject Func with domain not starting at 1"
    );

    // IntFunc with min=1
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        3,
        vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ],
    )));
    let result = intfunc.as_seq();
    assert!(result.is_some(), "as_seq must accept IntFunc with min=1");
    let elems = result.unwrap();
    assert_eq!(elems.len(), 3);
    assert_eq!(elems[0], Value::SmallInt(10));

    // IntFunc with min!=1 should return None
    let intfunc_non_seq = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        2,
        4,
        vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ],
    )));
    assert!(
        intfunc_non_seq.as_seq().is_none(),
        "as_seq must reject IntFunc with min!=1"
    );
}

/// #1713: Direct unit test - to_func_coerced() handles all seq-like variants.
/// Verifies both that conversion succeeds AND that the resulting FuncValue
/// preserves the correct domain→value mapping (not just domain_len).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1713_to_func_coerced_accepts_seq_tuple_intfunc() {
    // Seq
    let seq = Value::Seq(Arc::new(
        vec![Value::SmallInt(10), Value::SmallInt(20)].into(),
    ));
    let result = seq.to_func_coerced();
    assert!(result.is_some(), "to_func_coerced must accept Seq");
    let fv = result.unwrap();
    assert_eq!(fv.domain_len(), 2);
    assert_eq!(fv.apply(&Value::SmallInt(1)), Some(&Value::SmallInt(10)));
    assert_eq!(fv.apply(&Value::SmallInt(2)), Some(&Value::SmallInt(20)));

    // Tuple
    let tuple = Value::Tuple(vec![Value::SmallInt(10), Value::SmallInt(20)].into());
    let result = tuple.to_func_coerced();
    assert!(result.is_some(), "to_func_coerced must accept Tuple");
    let fv = result.unwrap();
    assert_eq!(fv.domain_len(), 2);
    assert_eq!(fv.apply(&Value::SmallInt(1)), Some(&Value::SmallInt(10)));
    assert_eq!(fv.apply(&Value::SmallInt(2)), Some(&Value::SmallInt(20)));

    // IntFunc
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::SmallInt(10), Value::SmallInt(20)],
    )));
    let result = intfunc.to_func_coerced();
    assert!(result.is_some(), "to_func_coerced must accept IntFunc");
    let fv = result.unwrap();
    assert_eq!(fv.domain_len(), 2);
    assert_eq!(fv.apply(&Value::SmallInt(1)), Some(&Value::SmallInt(10)));
    assert_eq!(fv.apply(&Value::SmallInt(2)), Some(&Value::SmallInt(20)));

    // Func (identity case)
    let func = {
        let mut fb = FuncBuilder::new();
        fb.insert(Value::SmallInt(1), Value::SmallInt(42));
        Value::Func(Arc::new(fb.build()))
    };
    let result = func.to_func_coerced();
    assert!(result.is_some(), "to_func_coerced must accept Func");
    let fv = result.unwrap();
    assert_eq!(fv.domain_len(), 1);
    assert_eq!(fv.apply(&Value::SmallInt(1)), Some(&Value::SmallInt(42)));
}
