// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #3264: TIR operator lookup must search dependency
/// modules, not just the root module. This is the INSTANCE wrapper pattern
/// where the root module has no operators — they all live in a dep.
#[test]
fn test_find_operator_in_dep_modules() {
    let inner = parse_module(
        "\
---- MODULE Inner3264 ----
VARIABLE x
Init == x = 0
TypeOK == x \\in {0, 1}
====",
    );
    // Wrapper has a variable but no operators — mirrors INSTANCE wrapper pattern.
    let wrapper = parse_module(
        "\
---- MODULE Wrapper3264 ----
VARIABLE x
====",
    );

    let program = TirProgram::from_modules(&wrapper, &[&inner]);

    // Root module should not have TypeOK.
    assert!(
        find_operator(&wrapper, "TypeOK").is_none(),
        "wrapper should not contain TypeOK directly"
    );

    // But the program should find it in the dep module.
    let found = program.find_operator_in_modules("TypeOK");
    assert!(
        found.is_some(),
        "TirProgram must find operators in dependency modules"
    );
    let (def, owner) = found.unwrap();
    assert_eq!(def.name.node, "TypeOK");
    assert_eq!(
        owner.name.node, "Inner3264",
        "operator should be found in the inner module"
    );
}

/// Verify that root module operators take priority over dep module operators.
#[test]
fn test_root_module_takes_priority_over_dep() {
    let inner = parse_module(
        "\
---- MODULE InnerPriority3264 ----
VARIABLE x
TypeOK == x \\in {0, 1, 2}
====",
    );
    let root = parse_module(
        "\
---- MODULE RootPriority3264 ----
VARIABLE x
TypeOK == x \\in {0, 1}
====",
    );

    let program = TirProgram::from_modules(&root, &[&inner]);
    let (_, owner) = program
        .find_operator_in_modules("TypeOK")
        .expect("should find TypeOK");
    assert_eq!(
        owner.name.node, "RootPriority3264",
        "root module operators should take priority over dep operators"
    );
}

/// Verify that eval_named_op works for operators in dep modules via
/// unnamed INSTANCE import with correct substitution context.
///
/// Updated for #3352: the old test found dep operators without INSTANCE
/// declarations, which was the unsafe pattern #3264 was guarding against.
/// Now operators must be imported via INSTANCE to be TIR-lowerable.
#[test]
fn test_eval_named_op_from_dep_module() {
    let inner = parse_module(
        "\
---- MODULE InnerEval3264 ----
MyConst == 42
====",
    );
    let wrapper = parse_module(
        "\
---- MODULE WrapperEval3264 ----
INSTANCE InnerEval3264
====",
    );

    let program = TirProgram::from_modules(&wrapper, &[&inner]);
    let ctx = EvalCtx::new();
    let result = program.eval_named_op(&ctx, "MyConst");
    assert_eq!(
        result.expect("eval_named_op should succeed for INSTANCE-imported dep module operators"),
        Value::SmallInt(42),
    );
}

/// Part of #3350: binding-form operators (FuncDef, SetFilter, SetBuilder)
/// now evaluate through TIR instead of being blanket-routed to AST.
#[test]
fn test_binding_form_operators_evaluate_through_tir() {
    let module = parse_module(
        "\
---- MODULE BindingFormTir3350 ----
FuncOp == [i \\in {1, 2} |-> i]
FilterOp == {x \\in {1, 2, 3}: x > 1}
BuilderOp == {x + 1 : x \\in {1, 2}}
Plain == <<1, 2>>
====",
    );

    let program = TirProgram::from_modules(&module, &[]);
    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&module]);

    // FuncDef-containing operator now succeeds via TIR
    let func_result = program.eval_named_op(&ctx, "FuncOp");
    assert!(
        func_result.is_ok(),
        "FuncDef operator should evaluate successfully via TIR, got: {func_result:?}"
    );

    // SetFilter-containing operator now succeeds via TIR
    let filter_result = program.eval_named_op(&ctx, "FilterOp");
    assert!(
        filter_result.is_ok(),
        "SetFilter operator should evaluate successfully via TIR, got: {filter_result:?}"
    );

    // SetBuilder-containing operator now succeeds via TIR
    let builder_result = program.eval_named_op(&ctx, "BuilderOp");
    assert!(
        builder_result.is_ok(),
        "SetBuilder operator should evaluate successfully via TIR, got: {builder_result:?}"
    );

    // Plain operator (no binding forms) still works
    let plain_result = program.eval_named_op(&ctx, "Plain");
    assert!(
        plain_result.is_ok(),
        "plain operator should still evaluate via TIR, got: {plain_result:?}"
    );
}

/// Part of #3352: INSTANCE-imported operators should be lowerable when
/// the root module has an unnamed INSTANCE declaration.
#[test]
fn test_instance_wrapper_can_lower() {
    let inner = parse_module(
        "\
---- MODULE Inner3352 ----
CONSTANT N
VARIABLE x
Init == x = N
====",
    );
    let wrapper = parse_module(
        "\
---- MODULE Wrapper3352 ----
CONSTANT Nodes
VARIABLE x
INSTANCE Inner3352 WITH N <- Nodes
====",
    );
    let program = TirProgram::from_modules(&wrapper, &[&inner]);
    assert!(
        program.can_lower_operator("Init"),
        "INSTANCE-imported operators should be lowerable"
    );
}

/// Part of #3352: root module operators take precedence over INSTANCE
/// imports (shadowing).
#[test]
fn test_instance_wrapper_root_shadows_instance() {
    let inner = parse_module(
        "\
---- MODULE InnerShadow3352 ----
Val == 0
====",
    );
    let root = parse_module(
        "\
---- MODULE RootShadow3352 ----
Val == 1
INSTANCE InnerShadow3352
====",
    );
    let program = TirProgram::from_modules(&root, &[&inner]);
    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&root, &inner]);

    assert_eq!(
        program
            .eval_named_op(&ctx, "Val")
            .expect("root operator should shadow INSTANCE import during evaluation"),
        Value::SmallInt(1),
        "root module operator should take precedence over the INSTANCE import",
    );
}

/// Part of #3352: INSTANCE wrapper with substitutions — verify the
/// substituted constant is correctly resolved.
#[test]
fn test_instance_wrapper_substitution_eval() {
    let inner = parse_module(
        "\
---- MODULE InnerSubst3352 ----
CONSTANT N
MyVal == N
====",
    );
    let wrapper = parse_module(
        "\
---- MODULE WrapperSubst3352 ----
CONSTANT Nodes
Nodes == 42
INSTANCE InnerSubst3352 WITH N <- Nodes
====",
    );
    let program = TirProgram::from_modules(&wrapper, &[&inner]);

    assert!(
        program.can_lower_operator("MyVal"),
        "INSTANCE-imported operator with substitution should be lowerable"
    );

    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&wrapper, &inner]);
    let result = program.eval_named_op(&ctx, "MyVal");
    assert_eq!(
        result.expect("MyVal should evaluate via TIR with INSTANCE substitution"),
        Value::SmallInt(42),
    );
}
