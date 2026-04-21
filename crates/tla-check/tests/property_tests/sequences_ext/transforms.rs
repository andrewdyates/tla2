// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Transform operators: ReplaceAll, Interleave, SubSeqs, SetToSeqs, AllSubSeqs

use super::eval_seqext_str;
use super::{int_set_of_seqs, Value};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_replace_all_basic() {
    // ReplaceAll(s, old, new) replaces all occurrences
    let result = eval_seqext_str("ReplaceAll(<<1, 2, 1, 3, 1>>, 1, 9)").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![
            Value::int(9),
            Value::int(2),
            Value::int(9),
            Value::int(3),
            Value::int(9)
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_replace_all_no_match() {
    // ReplaceAll with no matching elements leaves sequence unchanged
    let result = eval_seqext_str("ReplaceAll(<<1, 2, 3>>, 5, 9)").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![Value::int(1), Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_replace_all_empty_seq() {
    // ReplaceAll on empty sequence returns empty sequence
    let result = eval_seqext_str("ReplaceAll(<<>>, 1, 2)").unwrap();
    assert_eq!(result, Value::seq(vec![]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interleave_equal_length() {
    // Interleave(s, t) interleaves two sequences of equal length
    let result = eval_seqext_str("Interleave(<<1, 2, 3>>, <<4, 5, 6>>)").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![
            Value::int(1),
            Value::int(4),
            Value::int(2),
            Value::int(5),
            Value::int(3),
            Value::int(6)
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interleave_first_longer() {
    // Interleave with first sequence longer - remaining elements appended
    let result = eval_seqext_str("Interleave(<<1, 2, 3, 4>>, <<5, 6>>)").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![
            Value::int(1),
            Value::int(5),
            Value::int(2),
            Value::int(6),
            Value::int(3),
            Value::int(4)
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interleave_second_longer() {
    // Interleave with second sequence longer - remaining elements appended
    let result = eval_seqext_str("Interleave(<<1, 2>>, <<5, 6, 7, 8>>)").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![
            Value::int(1),
            Value::int(5),
            Value::int(2),
            Value::int(6),
            Value::int(7),
            Value::int(8)
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interleave_empty() {
    // Interleave with both empty sequences
    let result = eval_seqext_str("Interleave(<<>>, <<>>)").unwrap();
    assert_eq!(result, Value::seq(vec![]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interleave_one_empty() {
    // Interleave with one empty sequence
    let result = eval_seqext_str("Interleave(<<1, 2>>, <<>>)").unwrap();
    assert_eq!(result, Value::seq(vec![Value::int(1), Value::int(2)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseqs_basic() {
    // SubSeqs(s) returns all contiguous subsequences including empty
    let result = eval_seqext_str("SubSeqs(<<1, 2>>)").unwrap();
    let expected = int_set_of_seqs(&[vec![], vec![1], vec![2], vec![1, 2]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseqs_singleton() {
    // SubSeqs of singleton
    let result = eval_seqext_str("SubSeqs(<<1>>)").unwrap();
    let expected = int_set_of_seqs(&[vec![], vec![1]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseqs_empty() {
    // SubSeqs of empty sequence is just the empty sequence
    let result = eval_seqext_str("SubSeqs(<<>>)").unwrap();
    let expected = int_set_of_seqs(&[vec![]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseqs_three() {
    // SubSeqs of length 3 sequence
    let result = eval_seqext_str("SubSeqs(<<1, 2, 3>>)").unwrap();
    // Count: empty + 3 singletons + 2 pairs + 1 triple = 7
    let expected = int_set_of_seqs(&[
        vec![],
        vec![1],
        vec![2],
        vec![3],
        vec![1, 2],
        vec![2, 3],
        vec![1, 2, 3],
    ]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_to_seqs_basic() {
    // SetToSeqs({1, 2}) returns both permutations
    let result = eval_seqext_str("SetToSeqs({1, 2})").unwrap();
    let expected = int_set_of_seqs(&[vec![1, 2], vec![2, 1]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_to_seqs_three_elements() {
    // SetToSeqs({1, 2, 3}) returns all 6 permutations (3! = 6)
    let result = eval_seqext_str("SetToSeqs({1, 2, 3})").unwrap();
    let expected = int_set_of_seqs(&[
        vec![1, 2, 3],
        vec![1, 3, 2],
        vec![2, 1, 3],
        vec![2, 3, 1],
        vec![3, 1, 2],
        vec![3, 2, 1],
    ]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_to_seqs_singleton() {
    // SetToSeqs({1}) returns single permutation
    let result = eval_seqext_str("SetToSeqs({1})").unwrap();
    let expected = int_set_of_seqs(&[vec![1]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_to_seqs_empty() {
    // SetToSeqs({}) returns set with empty sequence
    let result = eval_seqext_str("SetToSeqs({})").unwrap();
    let expected = int_set_of_seqs(&[vec![]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_subseqs_basic() {
    // AllSubSeqs(<<1, 2>>) returns all 2^2 = 4 subsequences
    let result = eval_seqext_str("AllSubSeqs(<<1, 2>>)").unwrap();
    let expected = int_set_of_seqs(&[vec![], vec![1], vec![2], vec![1, 2]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_subseqs_three() {
    // AllSubSeqs(<<1, 2, 3>>) returns all 2^3 = 8 subsequences
    let result = eval_seqext_str("AllSubSeqs(<<1, 2, 3>>)").unwrap();
    let expected = int_set_of_seqs(&[
        vec![],
        vec![1],
        vec![2],
        vec![3],
        vec![1, 2],
        vec![1, 3],
        vec![2, 3],
        vec![1, 2, 3],
    ]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_subseqs_empty() {
    // AllSubSeqs(<<>>) returns just empty sequence
    let result = eval_seqext_str("AllSubSeqs(<<>>)").unwrap();
    let expected = int_set_of_seqs(&[vec![]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_all_subseqs_singleton() {
    // AllSubSeqs(<<1>>) returns empty and singleton
    let result = eval_seqext_str("AllSubSeqs(<<1>>)").unwrap();
    let expected = int_set_of_seqs(&[vec![], vec![1]]);
    assert_eq!(result, expected);
}
