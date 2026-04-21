// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_module_skips_instance_definition_operators_and_keeps_executable_ones() {
    let lowered = lower_main_module_with_env(instance_source(), &["Inner", "Mid", "Leaf"]);
    let names = lowered
        .operators
        .iter()
        .map(|op| op.name.as_str())
        .collect::<Vec<_>>();
    assert_eq!(names, vec!["Named", "Param", "Chain"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_module_strictly_lowers_all_executable_operators() {
    let source = r"
---- MODULE Main ----
A == TRUE /\ FALSE
B == TRUE \/ FALSE
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");
    let lowered = lower_module(&module).expect("module lowering should succeed");
    assert_eq!(lowered.name, "Main");
    assert_eq!(lowered.operators.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_module_succeeds_with_lambda_operator() {
    let source = r"
---- MODULE Main ----
Good == TRUE /\ FALSE
WithLambda == LAMBDA x : x + 1
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");
    let tir = lower_module(&module).expect("module with lambda should now succeed");
    assert_eq!(tir.operators.len(), 2);
    assert_eq!(tir.operators[1].name, "WithLambda");
    assert!(matches!(tir.operators[1].body.node, TirExpr::Lambda { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_expr_returns_unsupported_for_instance_expr() {
    // InstanceExpr is the only remaining AST variant that is not lowered
    // (it represents INSTANCE definitions, not executable expressions).
    // Module-level lowering filters these out, but lower_expr should
    // return UnsupportedExpr if called directly on one.
    let source = r"
---- MODULE Main ----
Good == TRUE
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("lower produced no module");

    let expr = Spanned::new(
        Expr::InstanceExpr("Fake".to_string(), vec![]),
        tla_core::Span::new(FileId(0), 0, 10),
    );
    let err = lower_expr(&module, &expr).expect_err("InstanceExpr should be unsupported");
    match err {
        TirLowerError::UnsupportedExpr { kind, .. } => {
            assert_eq!(kind, "InstanceExpr");
        }
        other => panic!("expected UnsupportedExpr, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_apply_returns_unsupported_for_builtin_cardinality() {
    let source = r"
---- MODULE Main ----
EXTENDS FiniteSets
Result == Cardinality({1, 2})
====";

    let err = lower_named_operator_result(source, "Result")
        .expect_err("Cardinality builtin apply should fall back to AST");
    match err {
        TirLowerError::UnsupportedExpr { kind, .. } => {
            assert_eq!(kind, "Apply");
        }
        other => panic!("expected UnsupportedExpr, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_apply_keeps_user_defined_cardinality_shadow() {
    let source = r"
---- MODULE Main ----
Cardinality(x) == x + 1
Result == Cardinality(41)
====
";

    let lowered = lower_named_operator(source, "Result");
    let TirExpr::Apply { op, args } = &lowered.node else {
        panic!("expected Apply, got {:?}", lowered.node);
    };
    expect_ident(op, "Cardinality");
    assert_eq!(args.len(), 1);
    expect_int_const(&args[0], 41);
}
