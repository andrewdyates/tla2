// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_core::{lower, parse_to_syntax_tree, FileId};
use tla_eval::{clear_for_test_reset, eval, EvalCtx};
use tla_value::{error::EvalResult, Value};

fn eval_str(src: &str) -> EvalResult<Value> {
    clear_for_test_reset();

    let module_src = format!("---- MODULE Test ----\n\nOp == {}\n\n====", src);
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("module should parse");

    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = EvalCtx::new();
                return eval(&ctx, &def.body);
            }
        }
    }

    panic!("Op not found");
}

fn eval_with_ops(defs: &str, expr: &str) -> EvalResult<Value> {
    clear_for_test_reset();

    let module_src = format!(
        "---- MODULE Test ----\n\n{}\n\nOp == {}\n\n====",
        defs, expr
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("module should parse");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.eval_op("Op")
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_selectseq() {
    assert_eq!(
        eval_with_ops(
            "IsEven(x) == x % 2 = 0",
            "SelectSeq(<<1, 2, 3, 4, 5, 6>>, IsEven)"
        )
        .unwrap(),
        Value::seq([Value::int(2), Value::int(4), Value::int(6)])
    );

    assert_eq!(
        eval_with_ops(
            "IsNegative(x) == x < 0",
            "SelectSeq(<<1, 2, 3>>, IsNegative)"
        )
        .unwrap(),
        Value::seq([])
    );

    assert_eq!(
        eval_with_ops(
            "IsPositive(x) == x > 0",
            "SelectSeq(<<1, 2, 3>>, IsPositive)"
        )
        .unwrap(),
        Value::seq([Value::int(1), Value::int(2), Value::int(3)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_selectseq_named_operator_reuses_binding_across_inner_let() {
    assert_eq!(
        eval_with_ops(
            "KeepEven(x) == LET y == x IN y % 2 = 0",
            "SelectSeq(<<1, 2, 3, 4>>, KeepEven)"
        )
        .unwrap(),
        Value::seq([Value::int(2), Value::int(4)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_select_in_seq_named_operator_reuses_binding_across_inner_let() {
    assert_eq!(
        eval_with_ops(
            "KeepEven(x) == LET y == x IN y % 2 = 0",
            "SelectInSeq(<<1, 2, 3, 4>>, KeepEven)"
        )
        .unwrap(),
        Value::int(2)
    );

    assert_eq!(
        eval_with_ops(
            "KeepEven(x) == LET y == x IN y % 2 = 0",
            "SelectInSeq(<<1, 3, 5>>, KeepEven)"
        )
        .unwrap(),
        Value::int(0)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_select_last_in_seq_named_operator_reuses_binding_across_inner_let() {
    assert_eq!(
        eval_with_ops(
            "KeepEven(x) == LET y == x IN y % 2 = 0",
            "SelectLastInSeq(<<1, 2, 3, 4>>, KeepEven)"
        )
        .unwrap(),
        Value::int(4)
    );

    assert_eq!(
        eval_with_ops(
            "KeepEven(x) == LET y == x IN y % 2 = 0",
            "SelectLastInSeq(<<1, 3, 5>>, KeepEven)"
        )
        .unwrap(),
        Value::int(0)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_selectseq_lambda_reuses_binding_across_inner_let() {
    assert_eq!(
        eval_str("SelectSeq(<<1, 2, 3, 4>>, LAMBDA x: LET y == x IN y % 2 = 0)").unwrap(),
        Value::seq([Value::int(2), Value::int(4)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_toset_with_selectseq() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE waiting
ToSet(s) == { s[i] : i \in DOMAIN s }
is_read(p) == p[1] = "read"
WaitingToRead == { p[2] : p \in ToSet(SelectSeq(waiting, is_read)) }
TestWaiting == WaitingToRead
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("module should parse");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("waiting".to_string());

    ctx.bind_mut("waiting".to_string(), Value::seq([]));
    let result = ctx.eval_op("TestWaiting").expect("empty queue should eval");
    assert_eq!(result, Value::empty_set());

    ctx.bind_mut(
        "waiting".to_string(),
        Value::seq([Value::tuple([Value::string("read"), Value::int(1)])]),
    );
    let waiting_set = ctx
        .eval_op("TestWaiting")
        .expect("one read should eval")
        .as_set()
        .unwrap()
        .clone();
    assert!(
        waiting_set.contains(&Value::int(1)),
        "Actor 1 should be in WaitingToRead"
    );

    ctx.bind_mut(
        "waiting".to_string(),
        Value::seq([
            Value::tuple([Value::string("read"), Value::int(1)]),
            Value::tuple([Value::string("write"), Value::int(2)]),
            Value::tuple([Value::string("read"), Value::int(3)]),
        ]),
    );
    let waiting_set = ctx
        .eval_op("TestWaiting")
        .expect("mixed requests should eval")
        .as_set()
        .unwrap()
        .clone();
    assert_eq!(waiting_set.len(), 2, "Should have 2 read requests");
    assert!(waiting_set.contains(&Value::int(1)));
    assert!(waiting_set.contains(&Value::int(3)));
    assert!(!waiting_set.contains(&Value::int(2)));
}
