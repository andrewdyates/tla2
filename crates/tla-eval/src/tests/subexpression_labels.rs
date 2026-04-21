// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;
use tla_core::ast::{Expr, Substitution};
use tla_core::{lower, parse_to_syntax_tree, FileId, Spanned};

/// Verify that label selection returns the body's actual value, not a hardcoded
/// true. The labeled expression `P0:: counter = 99` evaluates to FALSE because
/// counter == 0.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_returns_false_when_body_is_false() {
    let defs = r#"
counter == 0
Inv ==
  /\ P0:: counter = 99
  /\ counter <= 1
"#;

    let value = eval_with_ops(defs, "Inv!P0").expect("Inv!P0 should evaluate");
    assert_eq!(value, Value::Bool(false));
}

/// Verify label selection returns non-boolean values. The labeled expression
/// `P0:: counter + 10` evaluates to the integer 10, not a boolean.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_returns_integer_value() {
    let defs = r#"
counter == 0
Inv ==
  /\ P0:: counter + 10
  /\ TRUE
"#;

    let value = eval_with_ops(defs, "Inv!P0").expect("Inv!P0 should evaluate");
    assert_eq!(value, Value::Int(Arc::new(10.into())));
}

/// Verify that selecting a nonexistent label returns an error rather than
/// silently succeeding.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_nonexistent_label_errors() {
    let defs = r#"
counter == 0
Inv ==
  /\ P0:: counter = 0
  /\ counter <= 1
"#;

    let result = eval_with_ops(defs, "Inv!P99");
    assert!(
        result.is_err(),
        "selecting nonexistent label P99 should error, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_evaluates_named_label() {
    let defs = r#"
counter == 0
Inv ==
  /\ P0:: counter = 0
  /\ counter <= 1
"#;

    let value = eval_with_ops(defs, "Inv!P0").expect("Inv!P0 should evaluate");
    assert_eq!(value, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_preserves_let_scope() {
    let defs = r#"
Outer ==
  LET hidden == 42
  IN /\ P0:: hidden = 42
     /\ TRUE
"#;

    let value = eval_with_ops(defs, "Outer!P0").expect("Outer!P0 should evaluate");
    assert_eq!(value, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_preserves_substin_wrapper() {
    clear_for_test_reset();

    let module_src = r#"
---- MODULE Test ----
Inv == P0:: x = 42
Op == Inv!P0
====
"#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut inv = (**ctx.get_op("Inv").expect("Inv operator")).clone();
    inv.body = Spanned::dummy(Expr::SubstIn(
        vec![Substitution {
            from: Spanned::dummy("x".to_string()),
            to: Spanned::dummy(Expr::Int(42.into())),
        }],
        Box::new(inv.body.clone()),
    ));
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("Inv".to_string(), Arc::new(inv));

    let value = ctx
        .eval_op("Op")
        .expect("Op should evaluate through SubstIn label selection");
    assert_eq!(value, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_preserves_named_instance_chain() {
    clear_for_test_reset();

    let mod_inner = r#"
---- MODULE Inner ----
VARIABLE x
Inv ==
  /\ P0:: x = 42
  /\ TRUE
===="#;
    let mod_main = r#"
---- MODULE Main ----
Node == 42
Inst == INSTANCE Inner WITH x <- Node
Op == Inst!Inv!P0
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "Inner: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("Inner module");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "Main: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("Main module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let value = ctx
        .eval_op("Op")
        .expect("Inst!Inv!P0 should evaluate through the instance chain");
    assert_eq!(value, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_preserves_parameterized_instance_chain() {
    clear_for_test_reset();

    let mod_inner = r#"
---- MODULE Inner ----
VARIABLE x
Inv ==
  /\ P0:: x = 42
  /\ TRUE
===="#;
    let mod_main = r#"
---- MODULE Main ----
P(value) == INSTANCE Inner WITH x <- value
Node == 42
Op == P(Node)!Inv!P0
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "Inner: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("Inner module");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "Main: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("Main module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let value = ctx
        .eval_op("Op")
        .expect("P(Node)!Inv!P0 should evaluate through the parameterized instance chain");
    assert_eq!(value, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_supports_nested_direct_labels() {
    let defs = r#"
Outer ==
  /\ P0:: /\ P1:: TRUE
           /\ TRUE
  /\ TRUE
"#;

    let value = eval_with_ops(defs, "Outer!P0!P1").expect("Outer!P0!P1 should evaluate");
    assert_eq!(value, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_supports_nested_named_instance_labels() {
    clear_for_test_reset();

    let mod_inner = r#"
---- MODULE Inner ----
VARIABLE x
Inv ==
  /\ P0:: /\ P1:: x = 42
           /\ TRUE
  /\ TRUE
===="#;
    let mod_main = r#"
---- MODULE Main ----
Node == 42
Inst == INSTANCE Inner WITH x <- Node
Op == Inst!Inv!P0!P1
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "Inner: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("Inner module");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "Main: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("Main module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let value = ctx
        .eval_op("Op")
        .expect("Inst!Inv!P0!P1 should evaluate through nested label selection");
    assert_eq!(value, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subexpression_label_selector_supports_nested_parameterized_instance_labels() {
    clear_for_test_reset();

    let mod_inner = r#"
---- MODULE Inner ----
VARIABLE x
Inv ==
  /\ P0:: /\ P1:: x = 42
           /\ TRUE
  /\ TRUE
===="#;
    let mod_main = r#"
---- MODULE Main ----
P(value) == INSTANCE Inner WITH x <- value
Node == 42
Op == P(Node)!Inv!P0!P1
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "Inner: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("Inner module");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "Main: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("Main module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let value = ctx
        .eval_op("Op")
        .expect("P(Node)!Inv!P0!P1 should evaluate through nested label selection");
    assert_eq!(value, Value::Bool(true));
}
