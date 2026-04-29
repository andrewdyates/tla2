// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SetToSortSeq, Snoc, IsStrictPrefix, IsStrictSuffix, Prefixes, Suffixes,
//! TupleOf, BoundedSeq, SeqOf

use tla_core::{lower, parse_to_syntax_tree, FileId};

use super::{eval_str, Value};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_to_sort_seq() {
    // SetToSortSeq converts set to sorted sequence
    let module_src = r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

LessThan(a, b) == a < b
Op == SetToSortSeq({3, 1, 4, 1, 5}, LessThan)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    // Set deduplicates, so {3, 1, 4, 1, 5} = {1, 3, 4, 5}, sorted ascending
    assert_eq!(
        result,
        Value::seq([Value::int(1), Value::int(3), Value::int(4), Value::int(5)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_snoc() {
    // Snoc(<<1, 2>>, 3) = <<1, 2, 3>>
    let result = eval_str("Snoc(<<1, 2>>, 3)").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![Value::int(1), Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_snoc_empty() {
    // Snoc(<<>>, 1) = <<1>>
    let result = eval_str("Snoc(<<>>, 1)").unwrap();
    assert_eq!(result, Value::seq(vec![Value::int(1)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_strict_prefix_true() {
    // <<1, 2>> is strict prefix of <<1, 2, 3>>
    let result = eval_str("IsStrictPrefix(<<1, 2>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_strict_prefix_false_equal() {
    // <<1, 2>> is NOT strict prefix of <<1, 2>> (equal sequences)
    let result = eval_str("IsStrictPrefix(<<1, 2>>, <<1, 2>>)").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_strict_prefix_false_not_prefix() {
    // <<2, 1>> is NOT strict prefix of <<1, 2, 3>>
    let result = eval_str("IsStrictPrefix(<<2, 1>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_strict_suffix_true() {
    // <<2, 3>> is strict suffix of <<1, 2, 3>>
    let result = eval_str("IsStrictSuffix(<<2, 3>>, <<1, 2, 3>>)").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_strict_suffix_false_equal() {
    // <<1, 2>> is NOT strict suffix of <<1, 2>>
    let result = eval_str("IsStrictSuffix(<<1, 2>>, <<1, 2>>)").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prefixes() {
    // Prefixes(<<1, 2>>) = { <<>>, <<1>>, <<1, 2>> }
    let result = eval_str("Prefixes(<<1, 2>>)").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 3);
        assert!(set.contains(&Value::seq(vec![])));
        assert!(set.contains(&Value::seq(vec![Value::int(1)])));
        assert!(set.contains(&Value::seq(vec![Value::int(1), Value::int(2)])));
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prefixes_empty() {
    // Prefixes(<<>>) = { <<>> }
    let result = eval_str("Prefixes(<<>>)").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 1);
        assert!(set.contains(&Value::seq(vec![])));
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_suffixes() {
    // Suffixes(<<1, 2>>) = { <<>>, <<2>>, <<1, 2>> }
    let result = eval_str("Suffixes(<<1, 2>>)").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 3);
        assert!(set.contains(&Value::seq(vec![])));
        assert!(set.contains(&Value::seq(vec![Value::int(2)])));
        assert!(set.contains(&Value::seq(vec![Value::int(1), Value::int(2)])));
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_suffixes_empty() {
    // Suffixes(<<>>) = { <<>> }
    let result = eval_str("Suffixes(<<>>)").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 1);
        assert!(set.contains(&Value::seq(vec![])));
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_of() {
    // TupleOf({1, 2}, 2) = { <<1,1>>, <<1,2>>, <<2,1>>, <<2,2>> }
    let result = eval_str("TupleOf({1, 2}, 2)").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 4);
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_of_zero() {
    // TupleOf({1, 2}, 0) = { <<>> }
    let result = eval_str("TupleOf({1, 2}, 0)").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 1);
        assert!(set.contains(&Value::seq(vec![])));
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_seq() {
    // BoundedSeq({1}, 2) = { <<>>, <<1>>, <<1, 1>> }
    let result = eval_str("BoundedSeq({1}, 2)").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 3);
        assert!(set.contains(&Value::seq(vec![])));
        assert!(set.contains(&Value::seq(vec![Value::int(1)])));
        assert!(set.contains(&Value::seq(vec![Value::int(1), Value::int(1)])));
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_of_alias() {
    // SeqOf is an alias for BoundedSeq
    let result = eval_str("SeqOf({1}, 2)").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 3);
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}
