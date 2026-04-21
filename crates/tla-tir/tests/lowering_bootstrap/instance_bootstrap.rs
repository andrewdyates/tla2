// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_named_instance_module_ref_inlines_substituted_body() {
    let lowered =
        lower_named_operator_with_env(instance_source(), &["Inner", "Mid", "Leaf"], "Named");
    expect_bool_const(&lowered, true);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_imported_named_instance_module_ref_inlines_substituted_body() {
    let source = r"
---- MODULE Main ----
EXTENDS Ext
Use == I!Safe
====
---- MODULE Ext ----
I == INSTANCE Inner WITH Flag <- TRUE
====
---- MODULE Inner ----
Flag == FALSE
Safe == Flag
====";

    let lowered = lower_named_operator_with_env(source, &["Ext", "Inner"], "Use");
    expect_bool_const(&lowered, true);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_parameterized_instance_module_ref_applies_callsite_arguments() {
    let lowered =
        lower_named_operator_with_env(instance_source(), &["Inner", "Mid", "Leaf"], "Param");
    expect_bool_const(&lowered, false);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_imported_parameterized_instance_module_ref_applies_callsite_arguments() {
    let source = r"
---- MODULE Main ----
EXTENDS Ext
Use == P(FALSE)!Safe
====
---- MODULE Ext ----
P(x) == INSTANCE Inner WITH Flag <- x
====
---- MODULE Inner ----
Flag == FALSE
Safe == Flag
====";

    let lowered = lower_named_operator_with_env(source, &["Ext", "Inner"], "Use");
    expect_bool_const(&lowered, false);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_chained_instance_module_ref_composes_nested_bindings() {
    let lowered =
        lower_named_operator_with_env(instance_source(), &["Inner", "Mid", "Leaf"], "Chain");
    expect_bool_const(&lowered, true);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_let_bound_instance_alias_module_ref_inlines_substituted_body() {
    let source = r"
---- MODULE Main ----
Use == LET I == INSTANCE Inner WITH Flag <- TRUE
       IN I!Safe
====
---- MODULE Inner ----
Flag == FALSE
Safe == Flag
====";

    let lowered = lower_named_operator_with_env(source, &["Inner"], "Use");
    let TirExpr::Let { defs, body } = &lowered.node else {
        panic!("expected Let, got {:?}", lowered.node);
    };
    assert!(
        defs.is_empty(),
        "instance alias defs should not be emitted into TIR"
    );
    expect_bool_const(body, true);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn substin_wrappers_lower_via_binding_scope_instead_of_tir_node() {
    let source = r"
---- MODULE Main ----
Flag == FALSE
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
    let expr = Spanned::dummy(Expr::SubstIn(
        vec![Substitution {
            from: Spanned::dummy("Flag".to_string()),
            to: Spanned::dummy(Expr::Bool(true)),
        }],
        Box::new(Spanned::dummy(Expr::Ident(
            "Flag".to_string(),
            intern_name("Flag"),
        ))),
    ));

    let lowered = lower_expr(&module, &expr).expect("SubstIn should lower");
    expect_bool_const(&lowered, true);
}
