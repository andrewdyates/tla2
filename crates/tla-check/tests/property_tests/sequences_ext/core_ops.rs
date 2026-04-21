// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core SequencesExt operators: ToSet, Cons, Contains, IsPrefix, IsSuffix,
//! Indices, InsertAt, RemoveAt, ReplaceAt, Remove, FlattenSeq, Zip,
//! FoldLeft, FoldRight

use tla_core::{lower, parse_to_syntax_tree, FileId};

use super::eval_seqext_str;
use super::{int_set, Value};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_set() {
    // ToSet converts sequence to set
    let result = eval_seqext_str("ToSet(<<1, 2, 3, 2, 1>>)").unwrap();
    assert_eq!(result, int_set(&[1, 2, 3]));

    // Empty sequence -> empty set
    let result = eval_seqext_str("ToSet(<<>>)").unwrap();
    assert_eq!(result, int_set(&[]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cons() {
    // Cons prepends element to sequence
    let result = eval_seqext_str("Cons(0, <<1, 2, 3>>)").unwrap();
    assert_eq!(
        result,
        Value::seq([Value::int(0), Value::int(1), Value::int(2), Value::int(3)])
    );

    // Cons to empty sequence
    let result = eval_seqext_str("Cons(42, <<>>)").unwrap();
    assert_eq!(result, Value::seq([Value::int(42)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_contains() {
    // Contains checks if element is in sequence
    let result = eval_seqext_str("Contains(<<1, 2, 3>>, 2)").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_seqext_str("Contains(<<1, 2, 3>>, 5)").unwrap();
    assert_eq!(result, Value::Bool(false));

    let result = eval_seqext_str("Contains(<<>>, 1)").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_prefix() {
    // IsPrefix checks prefix relationship
    let result = eval_seqext_str("IsPrefix(<<1, 2>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_seqext_str("IsPrefix(<<1, 3>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(false));

    // Empty sequence is prefix of any sequence
    let result = eval_seqext_str("IsPrefix(<<>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(true));

    // Sequence is prefix of itself
    let result = eval_seqext_str("IsPrefix(<<1, 2>>, <<1, 2>>)").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_suffix() {
    // IsSuffix checks suffix relationship
    let result = eval_seqext_str("IsSuffix(<<2, 3>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_seqext_str("IsSuffix(<<1, 3>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(false));

    // Empty sequence is suffix of any sequence
    let result = eval_seqext_str("IsSuffix(<<>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_indices() {
    // Indices returns the set {1..Len(s)}
    let result = eval_seqext_str("Indices(<<1, 2, 3>>)").unwrap();
    // Interval 1..3
    assert_eq!(result, int_set(&[1, 2, 3]));

    let result = eval_seqext_str("Indices(<<>>)").unwrap();
    // Empty interval 1..0
    assert_eq!(result, int_set(&[]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_insert_at() {
    // InsertAt inserts element at position
    let result = eval_seqext_str("InsertAt(<<1, 2, 3>>, 2, 99)").unwrap();
    assert_eq!(
        result,
        Value::seq([Value::int(1), Value::int(99), Value::int(2), Value::int(3)])
    );

    // Insert at beginning
    let result = eval_seqext_str("InsertAt(<<1, 2, 3>>, 1, 99)").unwrap();
    assert_eq!(
        result,
        Value::seq([Value::int(99), Value::int(1), Value::int(2), Value::int(3)])
    );

    // Insert at end
    let result = eval_seqext_str("InsertAt(<<1, 2, 3>>, 4, 99)").unwrap();
    assert_eq!(
        result,
        Value::seq([Value::int(1), Value::int(2), Value::int(3), Value::int(99)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_remove_at() {
    // RemoveAt removes element at position
    let result = eval_seqext_str("RemoveAt(<<1, 2, 3>>, 2)").unwrap();
    assert_eq!(result, Value::seq([Value::int(1), Value::int(3)]));

    let result = eval_seqext_str("RemoveAt(<<1, 2, 3>>, 1)").unwrap();
    assert_eq!(result, Value::seq([Value::int(2), Value::int(3)]));

    let result = eval_seqext_str("RemoveAt(<<1, 2, 3>>, 3)").unwrap();
    assert_eq!(result, Value::seq([Value::int(1), Value::int(2)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_replace_at() {
    // ReplaceAt replaces element at position
    let result = eval_seqext_str("ReplaceAt(<<1, 2, 3>>, 2, 99)").unwrap();
    assert_eq!(
        result,
        Value::seq([Value::int(1), Value::int(99), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_remove() {
    // Remove removes first occurrence of element
    let result = eval_seqext_str("Remove(<<1, 2, 3, 2>>, 2)").unwrap();
    assert_eq!(
        result,
        Value::seq([Value::int(1), Value::int(3), Value::int(2)])
    );

    // Remove non-existent element - sequence unchanged
    let result = eval_seqext_str("Remove(<<1, 2, 3>>, 99)").unwrap();
    assert_eq!(
        result,
        Value::seq([Value::int(1), Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_flatten_seq() {
    // FlattenSeq flattens nested sequences
    let result = eval_seqext_str("FlattenSeq(<< <<1, 2>>, <<3>>, <<4, 5>> >>)").unwrap();
    assert_eq!(
        result,
        Value::seq([
            Value::int(1),
            Value::int(2),
            Value::int(3),
            Value::int(4),
            Value::int(5)
        ])
    );

    // Empty sequences
    let result = eval_seqext_str("FlattenSeq(<< <<>>, <<1>>, <<>> >>)").unwrap();
    assert_eq!(result, Value::seq([Value::int(1)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_zip() {
    // Zip combines two sequences into sequence of pairs
    let result = eval_seqext_str("Zip(<<1, 2>>, <<3, 4>>)").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![
            Value::Tuple(vec![Value::int(1), Value::int(3)].into()),
            Value::Tuple(vec![Value::int(2), Value::int(4)].into()),
        ])
    );

    // Different lengths - takes minimum
    let result = eval_seqext_str("Zip(<<1, 2, 3>>, <<4>>)").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![Value::Tuple(
            vec![Value::int(1), Value::int(4)].into()
        )])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fold_left() {
    // FoldLeft folds from left to right
    let module_src = r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

Add(a, b) == a + b
Op == FoldLeft(Add, 0, <<1, 2, 3, 4>>)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    assert_eq!(result, Value::int(10)); // 0+1+2+3+4 = 10
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fold_right() {
    // FoldRight folds from right to left
    // Using subtraction to verify order matters
    let module_src = r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

Sub(a, b) == a - b
Op == FoldRight(Sub, <<1, 2, 3>>, 0)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    // FoldRight(Sub, <<1, 2, 3>>, 0) = 1 - (2 - (3 - 0)) = 1 - (2 - 3) = 1 - (-1) = 2
    assert_eq!(result, Value::int(2));
}
