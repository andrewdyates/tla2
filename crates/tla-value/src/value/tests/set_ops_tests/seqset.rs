// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SeqSetValue membership coverage — "what counts as a sequence for Seq(S)".

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seqset_contains_seq() {
    // Seq({1, 2}) should contain <<1>>, <<2>>, <<1, 2>>, <<>>
    let base = Value::set([Value::int(1), Value::int(2)]);
    let seqset = SeqSetValue::new(base);

    assert_eq!(seqset.contains(&Value::seq([Value::int(1)])), Some(true));
    assert_eq!(
        seqset.contains(&Value::seq([Value::int(1), Value::int(2)])),
        Some(true)
    );
    assert_eq!(
        seqset.contains(&Value::seq(std::iter::empty::<Value>())),
        Some(true),
        "empty seq should be in Seq(S)"
    );
    assert_eq!(
        seqset.contains(&Value::seq([Value::int(3)])),
        Some(false),
        "<<3>> should not be in Seq({{1,2}})"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seqset_contains_tuple() {
    // Tuples are also valid sequences
    let base = Value::set([Value::int(1), Value::int(2)]);
    let seqset = SeqSetValue::new(base);

    assert_eq!(
        seqset.contains(&Value::tuple([Value::int(1), Value::int(2)])),
        Some(true)
    );
    assert_eq!(seqset.contains(&Value::tuple([Value::int(3)])), Some(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seqset_contains_intfunc() {
    // IntFunc with domain 1..n is a valid sequence
    let base = Value::set([Value::int(10), Value::int(20)]);
    let seqset = SeqSetValue::new(base);

    // IntFunc(1, 2, [10, 20]) = <<10, 20>> which is in Seq({10, 20})
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(10), Value::int(20)],
    )));
    assert_eq!(seqset.contains(&intfunc), Some(true));

    // IntFunc with min != 1 is NOT a valid sequence
    let intfunc_bad_min = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        2,
        3,
        vec![Value::int(10), Value::int(20)],
    )));
    assert_eq!(
        seqset.contains(&intfunc_bad_min),
        Some(false),
        "IntFunc with min=2 is not a valid sequence"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seqset_contains_func() {
    // Func with domain {1, ..., n} is a valid sequence
    let base = Value::set([Value::string("a"), Value::string("b")]);
    let seqset = SeqSetValue::new(base);

    // Func [1 |-> "a", 2 |-> "b"] is a valid sequence in Seq({"a", "b"})
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::string("a"));
    fb.insert(Value::int(2), Value::string("b"));
    let func = Value::Func(Arc::new(fb.build()));
    assert_eq!(seqset.contains(&func), Some(true));

    // Func with non-integer domain is NOT a valid sequence
    let mut fb2 = FuncBuilder::new();
    fb2.insert(Value::string("x"), Value::string("a"));
    let func_bad_domain = Value::Func(Arc::new(fb2.build()));
    assert_eq!(
        seqset.contains(&func_bad_domain),
        Some(false),
        "Func with string domain is not a valid sequence"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seqset_rejects_non_seq_values() {
    let base = Value::set([Value::int(1)]);
    let seqset = SeqSetValue::new(base);

    // Non-sequence values should not be in Seq(S)
    assert_eq!(seqset.contains(&Value::int(1)), Some(false));
    assert_eq!(seqset.contains(&Value::string("a")), Some(false));
    assert_eq!(seqset.contains(&Value::bool(true)), Some(false));
    assert_eq!(seqset.contains(&Value::set([Value::int(1)])), Some(false));
}
