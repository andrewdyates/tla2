// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_reverse() {
    // Reverse a sequence
    assert_eq!(
        eval_str("Reverse(<<1, 2, 3>>)").unwrap(),
        Value::seq([Value::int(3), Value::int(2), Value::int(1)])
    );

    // Reverse empty sequence
    assert_eq!(eval_str("Reverse(<<>>)").unwrap(), Value::seq([]));

    // Reverse single element
    assert_eq!(
        eval_str("Reverse(<<42>>)").unwrap(),
        Value::seq([Value::int(42)])
    );

    // Reverse with strings
    assert_eq!(
        eval_str(r#"Reverse(<<"a", "b", "c">>)"#).unwrap(),
        Value::seq([Value::string("c"), Value::string("b"), Value::string("a")])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_front() {
    // Front - all but last element
    assert_eq!(
        eval_str("Front(<<1, 2, 3>>)").unwrap(),
        Value::seq([Value::int(1), Value::int(2)])
    );

    // Front of single element
    assert_eq!(eval_str("Front(<<42>>)").unwrap(), Value::seq([]));

    // Front of empty sequence should error with IndexOutOfBounds
    // (unlike Head which uses ApplyEmptySeq, Front uses IndexOutOfBounds)
    assert!(
        matches!(
            eval_str("Front(<<>>)"),
            Err(EvalError::IndexOutOfBounds {
                index: 1,
                len: 0,
                ..
            })
        ),
        "Front(<<>>) should return IndexOutOfBounds error"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_last() {
    // Last element of sequence
    assert_eq!(eval_str("Last(<<1, 2, 3>>)").unwrap(), Value::int(3));

    // Last of single element
    assert_eq!(eval_str("Last(<<42>>)").unwrap(), Value::int(42));

    // Last of empty sequence should error with IndexOutOfBounds
    // (unlike Tail which uses ApplyEmptySeq, Last uses IndexOutOfBounds)
    assert!(
        matches!(
            eval_str("Last(<<>>)"),
            Err(EvalError::IndexOutOfBounds {
                index: 1,
                len: 0,
                ..
            })
        ),
        "Last(<<>>) should return IndexOutOfBounds error"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_settoseq() {
    // SetToSeq converts set to sequence (order is deterministic but arbitrary)
    let result = eval_str("SetToSeq({1, 2, 3})").unwrap();
    let seq = result.as_seq().unwrap();
    assert_eq!(seq.len(), 3);
    // Check all elements are present
    assert!(seq.contains(&Value::int(1)));
    assert!(seq.contains(&Value::int(2)));
    assert!(seq.contains(&Value::int(3)));

    // Empty set
    assert_eq!(eval_str("SetToSeq({})").unwrap(), Value::seq([]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_foldset() {
    // FoldSet(Op, base, S) - sum of set elements
    assert_eq!(
        eval_with_ops("Add(a, b) == a + b", "FoldSet(Add, 0, {1, 2, 3})").unwrap(),
        Value::int(6)
    );

    // Product of set elements
    assert_eq!(
        eval_with_ops("Mul(a, b) == a * b", "FoldSet(Mul, 1, {2, 3, 4})").unwrap(),
        Value::int(24)
    );

    // Empty set returns base
    assert_eq!(
        eval_with_ops("Add(a, b) == a + b", "FoldSet(Add, 100, {})").unwrap(),
        Value::int(100)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_foldseq() {
    // FoldSeq(Op, base, s) - sum of sequence elements
    assert_eq!(
        eval_with_ops("Add(a, b) == a + b", "FoldSeq(Add, 0, <<1, 2, 3>>)").unwrap(),
        Value::int(6)
    );

    // Build string by concatenation (demonstrates order matters)
    // Note: FoldSeq goes left to right, so we build "cba" from <<a,b,c>> with prepend
    // Actually let's test with subtraction to show order
    assert_eq!(
        eval_with_ops("Sub(a, b) == a - b", "FoldSeq(Sub, 10, <<1, 2, 3>>)").unwrap(),
        Value::int(4) // ((10 - 1) - 2) - 3 = 4
    );

    // Empty sequence returns base
    assert_eq!(
        eval_with_ops("Add(a, b) == a + b", "FoldSeq(Add, 42, <<>>)").unwrap(),
        Value::int(42)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_foldfunction() {
    // FoldFunction(Op, base, f) - sum of function range values
    assert_eq!(
        eval_with_ops(
            "Add(a, b) == a + b\nf == [x \\in {1,2,3} |-> x * 2]",
            "FoldFunction(Add, 0, f)"
        )
        .unwrap(),
        Value::int(12) // 2 + 4 + 6 = 12
    );

    // Single element function
    assert_eq!(
        eval_with_ops(
            "Add(a, b) == a + b\ng == [x \\in {1} |-> x * 10]",
            "FoldFunction(Add, 5, g)"
        )
        .unwrap(),
        Value::int(15) // 5 + 10 = 15
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_foldfunctiononset() {
    // FoldFunctionOnSet(Op, base, f, S) - fold over function values for keys in S
    assert_eq!(
        eval_with_ops(
            "Add(a, b) == a + b\nf == [x \\in {1,2,3,4} |-> x * 2]",
            "FoldFunctionOnSet(Add, 0, f, {1,2})"
        )
        .unwrap(),
        Value::int(6) // 2 + 4 = 6 (only keys 1 and 2)
    );

    // Full domain
    assert_eq!(
        eval_with_ops(
            "Add(a, b) == a + b\nf == [x \\in {1,2,3} |-> x * 2]",
            "FoldFunctionOnSet(Add, 0, f, {1,2,3})"
        )
        .unwrap(),
        Value::int(12) // 2 + 4 + 6 = 12
    );

    // Empty subset returns base
    assert_eq!(
        eval_with_ops(
            "Add(a, b) == a + b\nf == [x \\in {1,2,3} |-> x * 2]",
            "FoldFunctionOnSet(Add, 100, f, {})"
        )
        .unwrap(),
        Value::int(100)
    );
}
