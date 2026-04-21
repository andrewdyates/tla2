// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eq_non_enumerable_funcset_errors() {
    let err = eval_str(r#"[Nat -> Nat] = {}"#).unwrap_err();
    assert!(matches!(err, EvalError::SetTooLarge { .. }), "{err:?}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eq_non_enumerable_subset_errors() {
    let err = eval_str(r#"SUBSET Nat = {}"#).unwrap_err();
    assert!(matches!(err, EvalError::SetTooLarge { .. }), "{err:?}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_sets() {
    assert_eq!(
        eval_str("{1, 2, 3}").unwrap(),
        Value::set([Value::int(1), Value::int(2), Value::int(3)])
    );
    assert_eq!(eval_str(r#"1 \in {1, 2}"#).unwrap(), Value::Bool(true));
    assert_eq!(eval_str(r#"3 \notin {1, 2}"#).unwrap(), Value::Bool(true));
    assert_eq!(
        eval_str(r#"{1} \cup {2}"#).unwrap(),
        Value::set([Value::int(1), Value::int(2)])
    );
    assert_eq!(
        eval_str(r#"{1, 2} \cap {2, 3}"#).unwrap(),
        Value::set([Value::int(2)])
    );
    assert_eq!(
        eval_str(r#"{1, 2} \ {2}"#).unwrap(),
        Value::set([Value::int(1)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_union_singleton_fast_path_rhs() {
    assert_eq!(
        eval_str(r#"{1, 3} \cup {2}"#).unwrap(),
        Value::set([Value::int(1), Value::int(2), Value::int(3)])
    );
    assert_eq!(
        eval_str(r#"{1, 2} \cup {2}"#).unwrap(),
        Value::set([Value::int(1), Value::int(2)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_union_singleton_fast_path_lhs() {
    assert_eq!(
        eval_str(r#"{2} \cup {1, 3}"#).unwrap(),
        Value::set([Value::int(1), Value::int(2), Value::int(3)])
    );
    assert_eq!(
        eval_str(r#"{2} \cup {1, 2}"#).unwrap(),
        Value::set([Value::int(1), Value::int(2)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_set_builder() {
    assert_eq!(
        eval_str(r#"{x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::set([Value::int(2), Value::int(4), Value::int(6)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_set_builder_over_filtered_subset_domain() {
    // Regression test for #1814: set-builder domains backed by lazy SetPred
    // (from filtering SUBSET) must still enumerate correctly.
    assert_eq!(
        eval_str(r#"{s : s \in {t \in SUBSET {1, 2, 3} : 2 \in t}}"#).unwrap(),
        Value::set([
            Value::set([Value::int(2)]),
            Value::set([Value::int(1), Value::int(2)]),
            Value::set([Value::int(2), Value::int(3)]),
            Value::set([Value::int(1), Value::int(2), Value::int(3)]),
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_set_builder_over_nested_filtered_subset_domain() {
    assert_eq!(
        eval_str(r#"{s : s \in {u \in {t \in SUBSET {1, 2, 3} : 2 \in t} : 3 \in u}}"#).unwrap(),
        Value::set([
            Value::set([Value::int(2), Value::int(3)]),
            Value::set([Value::int(1), Value::int(2), Value::int(3)]),
        ])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_set_builder_multi_var() {
    // Test {<<x, y>> : x, y \in {1, 2}}
    // First, let's check the CST/AST
    let src = r#"
---- MODULE Test ----
S == {<<x, y>> : x, y \in {1, 2}}
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    eprintln!("=== CST for multi-var set builder ===");
    eprintln!("{:#?}", tree);

    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    eprintln!("Lower errors: {:?}", lower_result.errors);
    let module = lower_result.module.unwrap();
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            eprintln!("Op '{}' body: {:?}", def.name.node, def.body.node);
        }
    }

    // Setup eval context
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let result = ctx.eval_op("S");
    eprintln!("Multi-var set builder result: {:?}", result);
    let val = result.unwrap();
    let expected = Value::set([
        Value::tuple([Value::int(1), Value::int(1)]),
        Value::tuple([Value::int(1), Value::int(2)]),
        Value::tuple([Value::int(2), Value::int(1)]),
        Value::tuple([Value::int(2), Value::int(2)]),
    ]);
    assert_eq!(val, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_set_builder_dependent_subexpr_not_cached_across_outer_quantifier() {
    // The builder body depends on the outer x. This remains a semantic guard
    // while hoisting is disabled, and if the lane returns it must not reuse
    // the first set across iterations.
    assert_eq!(
        eval_str(
            r#"\A x \in {1, 2} :
                 {y + x : y \in {1, 2}} =
                     IF x = 1 THEN {2, 3} ELSE {3, 4}"#,
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_set_filter() {
    assert_eq!(
        eval_str(r#"{x \in {1, 2, 3, 4} : x > 2}"#).unwrap(),
        Value::set([Value::int(3), Value::int(4)])
    );
}
