// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests that operators accepting boolean predicates reject non-boolean results.
//!
//! Each test verifies that passing a predicate returning an integer (instead of
//! a boolean) produces a TypeError mentioning BOOLEAN.

use tla_check::Value;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn eval_module_op(module_src: &str) -> Result<Value, String> {
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return Err(format!("Parse error: {:?}", lower_result.errors)),
    };
    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    ctx.eval_op("Op").map_err(|e| format!("{e:?}"))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_select_in_seq_non_boolean_predicate_errors() {
    let err = eval_module_op(
        r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

BadTest(x) == 1
Op == SelectInSeq(<<1, 2, 3>>, BadTest)

===="#,
    )
    .unwrap_err();
    assert!(
        err.contains("TypeError") && err.contains("BOOLEAN"),
        "SelectInSeq should reject non-boolean predicate: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_select_last_in_seq_non_boolean_predicate_errors() {
    let err = eval_module_op(
        r#"---- MODULE Test ----
EXTENDS Sequences, SequencesExt

BadTest(x) == 1
Op == SelectLastInSeq(<<1, 2, 3>>, BadTest)

===="#,
    )
    .unwrap_err();
    assert!(
        err.contains("TypeError") && err.contains("BOOLEAN"),
        "SelectLastInSeq should reject non-boolean predicate: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_restrict_domain_non_boolean_predicate_errors() {
    let err = eval_module_op(
        r#"---- MODULE Test ----
EXTENDS Functions

f == [x \in {1, 2, 3} |-> x]
BadPred(x) == 1
Op == RestrictDomain(f, LAMBDA x: BadPred(x))

===="#,
    )
    .unwrap_err();
    assert!(
        err.contains("TypeError") && err.contains("BOOLEAN"),
        "RestrictDomain should reject non-boolean predicate: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_restrict_values_non_boolean_predicate_errors() {
    let err = eval_module_op(
        r#"---- MODULE Test ----
EXTENDS Functions

f == [x \in {1, 2, 3} |-> x]
BadPred(y) == 1
Op == RestrictValues(f, LAMBDA y: BadPred(y))

===="#,
    )
    .unwrap_err();
    assert!(
        err.contains("TypeError") && err.contains("BOOLEAN"),
        "RestrictValues should reject non-boolean predicate: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_unique_non_boolean_predicate_errors() {
    let err = eval_module_op(
        r#"---- MODULE Test ----
EXTENDS FiniteSetsExt

Op == ChooseUnique({1, 2, 3}, LAMBDA x: 1)

===="#,
    )
    .unwrap_err();
    assert!(
        err.contains("TypeError") && err.contains("BOOLEAN"),
        "ChooseUnique should reject non-boolean predicate: {err}"
    );
}
