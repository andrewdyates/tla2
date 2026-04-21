// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LongestCommonPrefix, CommonPrefixes, FoldLeftDomain, FoldRightDomain

use tla_core::{lower, parse_to_syntax_tree, FileId};

use super::eval_seqext_str;
use super::{int_set_of_seqs, sorted_set_from_values, Value};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_longest_common_prefix_basic() {
    // LongestCommonPrefix of two sequences with common prefix
    let result = eval_seqext_str("LongestCommonPrefix({<<1, 2, 3>>, <<1, 2, 4>>})").unwrap();
    assert_eq!(result, Value::seq(vec![Value::int(1), Value::int(2)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_longest_common_prefix_no_common() {
    // LongestCommonPrefix with no common prefix
    let result = eval_seqext_str("LongestCommonPrefix({<<1, 2>>, <<3, 4>>})").unwrap();
    assert_eq!(result, Value::seq(vec![]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_longest_common_prefix_identical() {
    // LongestCommonPrefix of identical sequences
    let result = eval_seqext_str("LongestCommonPrefix({<<1, 2, 3>>, <<1, 2, 3>>})").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![Value::int(1), Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_longest_common_prefix_one_prefix_of_other() {
    // LongestCommonPrefix where one is prefix of other
    let result = eval_seqext_str("LongestCommonPrefix({<<1, 2>>, <<1, 2, 3>>})").unwrap();
    assert_eq!(result, Value::seq(vec![Value::int(1), Value::int(2)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_longest_common_prefix_single() {
    // LongestCommonPrefix of single sequence
    let result = eval_seqext_str("LongestCommonPrefix({<<1, 2, 3>>})").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![Value::int(1), Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_longest_common_prefix_empty_set() {
    // LongestCommonPrefix of empty set
    let result = eval_seqext_str("LongestCommonPrefix({})").unwrap();
    assert_eq!(result, Value::seq(vec![]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_common_prefixes_basic() {
    // CommonPrefixes of two sequences with common prefix
    let result = eval_seqext_str("CommonPrefixes({<<1, 2, 3>>, <<1, 2, 4>>})").unwrap();
    let expected = int_set_of_seqs(&[vec![], vec![1], vec![1, 2]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_common_prefixes_no_common() {
    // CommonPrefixes with no common prefix (only empty)
    let result = eval_seqext_str("CommonPrefixes({<<1, 2>>, <<3, 4>>})").unwrap();
    let expected = int_set_of_seqs(&[vec![]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_common_prefixes_identical() {
    // CommonPrefixes of identical sequences
    let result = eval_seqext_str("CommonPrefixes({<<1, 2>>, <<1, 2>>})").unwrap();
    let expected = int_set_of_seqs(&[vec![], vec![1], vec![1, 2]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_common_prefixes_empty_set() {
    // CommonPrefixes of empty set
    let result = eval_seqext_str("CommonPrefixes({})").unwrap();
    let expected = int_set_of_seqs(&[vec![]]);
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fold_left_domain_sum_indices() {
    // Use FoldLeftDomain to sum elements weighted by their indices
    // Sum(i * s[i]) over sequence <<10, 20, 30>>
    // = 1*10 + 2*20 + 3*30 = 10 + 40 + 90 = 140
    let module_src = r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

WeightedAdd(acc, elem, idx) == acc + (idx * elem)
Result == FoldLeftDomain(WeightedAdd, 0, <<10, 20, 30>>)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Result").unwrap();
    assert_eq!(result, Value::int(140));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fold_left_domain_build_pairs() {
    // Use FoldLeftDomain to collect (index, element) pairs into a set
    let module_src = r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

AddPair(acc, elem, idx) == acc \union { <<idx, elem>> }
Result == FoldLeftDomain(AddPair, {}, <<10, 20>>)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Result").unwrap();

    // Expected: { <<1, 10>>, <<2, 20>> }
    let expected = sorted_set_from_values(vec![
        Value::Tuple(vec![Value::int(1), Value::int(10)].into()),
        Value::Tuple(vec![Value::int(2), Value::int(20)].into()),
    ]);
    assert_eq!(result, Value::Set(expected.into()));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fold_left_domain_empty() {
    // FoldLeftDomain on empty sequence returns base
    let module_src = r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

Op(acc, elem, idx) == acc + elem
Result == FoldLeftDomain(Op, 42, <<>>)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Result").unwrap();
    assert_eq!(result, Value::int(42));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fold_right_domain_build_list() {
    // Use FoldRightDomain to prepend (idx, elem) pairs
    // Processing <<10, 20>> from right:
    // idx=2: Op(20, <<>>, 2) = <<2, 20>> \o <<>> = <<2, 20>>
    // idx=1: Op(10, <<2, 20>>, 1) = <<1, 10>> \o <<2, 20>> = <<1, 10, 2, 20>>
    let module_src = r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

Prepend(elem, acc, idx) == <<idx, elem>> \o acc
Result == FoldRightDomain(Prepend, <<10, 20>>, <<>>)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Result").unwrap();
    assert_eq!(
        result,
        Value::seq(vec![
            Value::int(1),
            Value::int(10),
            Value::int(2),
            Value::int(20)
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fold_right_domain_empty() {
    // FoldRightDomain on empty sequence returns base
    let module_src = r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

Op(elem, acc, idx) == acc + elem
Result == FoldRightDomain(Op, <<>>, 99)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Result").unwrap();
    assert_eq!(result, Value::int(99));
}
