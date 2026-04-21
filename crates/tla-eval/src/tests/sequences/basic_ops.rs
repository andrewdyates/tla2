// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_cardinality() {
    assert_eq!(eval_str("Cardinality({1, 2, 3})").unwrap(), Value::int(3));
    assert_eq!(eval_str("Cardinality({})").unwrap(), Value::int(0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_len() {
    assert_eq!(eval_str("Len(<<1, 2, 3>>)").unwrap(), Value::int(3));
    assert_eq!(eval_str("Len(<<>>)").unwrap(), Value::int(0));
    assert_eq!(eval_str(r#"Len("abc")"#).unwrap(), Value::int(3));
    // TLC-compatible string length is UTF-16 code units (Java String.length()).
    assert_eq!(eval_str(r#"Len("🙂")"#).unwrap(), Value::int(2));
    assert_eq!(eval_str(r#"Len("a🙂b")"#).unwrap(), Value::int(4));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_head_tail() {
    assert_eq!(eval_str("Head(<<1, 2, 3>>)").unwrap(), Value::int(1));
    assert_eq!(
        eval_str("Tail(<<1, 2, 3>>)").unwrap(),
        Value::seq([Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_head_tail_on_func_constructed_seq() {
    // Functions with domain 1..n are semantically sequences in TLA+
    // Head/Tail must work on them (issue: AlternatingBit Lose function)
    assert_eq!(
        eval_str(r#"Head([x \in 1..3 |-> x * 2])"#).unwrap(),
        Value::int(2)
    );
    assert_eq!(
        eval_str(r#"Tail([x \in 1..3 |-> x * 2])"#).unwrap(),
        Value::seq([Value::int(4), Value::int(6)])
    );
    // Len must also work
    assert_eq!(
        eval_str(r#"Len([x \in 1..3 |-> x * 2])"#).unwrap(),
        Value::int(3)
    );
    // Test the pattern from AlternatingBit Lose function
    // [j \in 1..(Len(q)-1) |-> ...] should work with Tail
    assert_eq!(
        eval_str(r#"Tail([j \in 1..2 |-> j])"#).unwrap(),
        Value::seq([Value::int(2)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_append() {
    assert_eq!(
        eval_str("Append(<<1, 2>>, 3)").unwrap(),
        Value::seq([Value::int(1), Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_subseq() {
    assert_eq!(
        eval_str("SubSeq(<<1, 2, 3, 4>>, 2, 3)").unwrap(),
        Value::seq([Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_subseq_string() {
    assert_eq!(
        eval_str(r#"SubSeq("/ctrl/c", 1, Len("/ctrl"))"#).unwrap(),
        Value::string("/ctrl")
    );
    // TLC-compatible string SubSeq indices are in UTF-16 code units.
    assert_eq!(
        eval_str(r#"SubSeq("a🙂b", 2, 3)"#).unwrap(),
        Value::string("🙂")
    );
    // A non-BMP code point occupies two UTF-16 code units, so SubSeq can split a surrogate pair.
    // TLC can represent unpaired surrogates as Java `char`s, but Rust strings must be valid UTF-8.
    // We fall back to lossy UTF-16 decoding, yielding U+FFFD for an unpaired surrogate half.
    assert_eq!(
        eval_str(r#"SubSeq("🙂a", 1, 1)"#).unwrap(),
        Value::string("\u{FFFD}")
    );
    assert_eq!(
        eval_str(r#"SubSeq("🙂a", 2, 2)"#).unwrap(),
        Value::string("\u{FFFD}")
    );
    assert_eq!(
        eval_str(r#"SubSeq("🙂a", 1, 2)"#).unwrap(),
        Value::string("🙂")
    );
    assert_eq!(
        eval_str(r#"SubSeq("a🙂b", 2, 4)"#).unwrap(),
        Value::string("🙂b")
    );
    assert_eq!(
        eval_str(r#"SubSeq("a🙂b", 4, 4)"#).unwrap(),
        Value::string("b")
    );
    assert_eq!(
        eval_str(r#"SubSeq("abc", 2, 1)"#).unwrap(),
        Value::string("")
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_subseq_bounds_errors() {
    let err = eval_str("SubSeq(<<1, 2>>, 1, 3)").unwrap_err();
    assert!(matches!(
        err,
        EvalError::IndexOutOfBounds {
            index: 3,
            len: 2,
            ..
        }
    ));

    let err = eval_str("SubSeq(<<1, 2>>, 0, 1)").unwrap_err();
    assert!(matches!(
        err,
        EvalError::IndexOutOfBounds {
            index: 0,
            len: 2,
            ..
        }
    ));

    let err = eval_str(r#"SubSeq("ab", 1, 3)"#).unwrap_err();
    assert!(matches!(
        err,
        EvalError::IndexOutOfBounds {
            index: 3,
            len: 2,
            ..
        }
    ));

    // TLC string Len is UTF-16 code units, so "🙂" has length 2.
    let err = eval_str(r#"SubSeq("🙂", 1, 3)"#).unwrap_err();
    assert!(matches!(
        err,
        EvalError::IndexOutOfBounds {
            index: 3,
            len: 2,
            ..
        }
    ));

    // Even if m > n, TLC still requires that the first argument is a sequence/string.
    let err = eval_str("SubSeq(1, 2, 1)").unwrap_err();
    assert!(matches!(err, EvalError::ArgumentError { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_subseq_accepts_seq_like_functions() {
    // SubSeq must accept any function value with domain 1..n, not just <<...>> literals.
    assert_eq!(
        eval_str(r#"SubSeq([i \in 1..4 |-> i], 2, 3)"#).unwrap(),
        Value::seq([Value::int(2), Value::int(3)])
    );
    assert_eq!(
        eval_str(r#"SubSeq([i \in {1, 2, 3, 4} |-> i], 2, 3)"#).unwrap(),
        Value::seq([Value::int(2), Value::int(3)])
    );
}
