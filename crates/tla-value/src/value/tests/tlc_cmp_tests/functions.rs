// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FuncValue TLC normalization caching tests (Part of #1434).

use super::super::super::*;
use super::tlc_normalized;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_tlc_normalized_model_value_domain_correctness() {
    // ModelValue domains have Value::cmp that diverges from tlc_cmp
    // (tlc_cmp uses registration-order indices, Value::cmp uses lexicographic).
    // Verify that sets of ModelValue-keyed functions are sorted consistently
    // via func_tlc_normalized_entries (which uses OnceLock caching internally).
    let mv_a = Value::try_model_value("norm_a").unwrap();
    let mv_b = Value::try_model_value("norm_b").unwrap();
    let mv_c = Value::try_model_value("norm_c").unwrap();

    // Create functions with ModelValue domain — not homogeneous-safe
    let f1 = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (mv_a.clone(), Value::int(1)),
        (mv_b.clone(), Value::int(2)),
        (mv_c.clone(), Value::int(3)),
    ])));
    let f2 = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (mv_a.clone(), Value::int(10)),
        (mv_b.clone(), Value::int(20)),
        (mv_c.clone(), Value::int(30)),
    ])));

    // Sorting a set of ModelValue-domain functions triggers func_tlc_normalized_entries.
    // This exercises the OnceLock caching path for non-homogeneous-safe domains.
    let set_of_funcs = Value::set([f1.clone(), f2.clone()]);
    let normalized1 = tlc_normalized(&set_of_funcs);
    assert_eq!(normalized1.len(), 2, "set should have 2 distinct functions");

    // Repeated normalization must produce identical results (correctness + cache consistency)
    let normalized2 = tlc_normalized(&set_of_funcs);
    assert_eq!(
        normalized1, normalized2,
        "repeated normalization must be consistent"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_tlc_normalized_homogeneous_safe_bypass() {
    // Integer-domain functions are homogeneous-safe: Value::cmp agrees with tlc_cmp.
    // func_tlc_normalized_entries returns entries directly without caching.
    // Verify correctness and consistency.
    let f1 = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("a")),
        (Value::int(2), Value::string("b")),
    ])));
    let f2 = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::int(1), Value::string("x")),
        (Value::int(2), Value::string("y")),
    ])));

    let set_of_funcs = Value::set([f1.clone(), f2.clone()]);
    let normalized1 = tlc_normalized(&set_of_funcs);
    assert_eq!(normalized1.len(), 2, "set should have 2 distinct functions");

    // Repeated normalization consistent
    let normalized2 = tlc_normalized(&set_of_funcs);
    assert_eq!(
        normalized1, normalized2,
        "repeated normalization must be consistent"
    );
}
