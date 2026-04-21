// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Part of #3460: Verify that expressions containing parameterized sequence
/// builtins (Append, Head, Tail, etc.) are rejected by TIR lowering and
/// fall back to AST evaluation. Without this gate, TIR produces UndefinedVar
/// errors for sequence builtins during successor generation.
#[test]
fn test_append_in_except_falls_back_to_ast() {
    let module = parse_module(
        "\
---- MODULE AppendFallback3460 ----
EXTENDS Sequences
VARIABLE consumed
Next == consumed' = Append(consumed, 1)
====",
    );

    let program = TirProgram::from_modules(&module, &[]);
    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&module]);
    ctx.bind_mut("consumed", Value::Seq(std::sync::Arc::new(vec![].into())));

    // The operator body contains Append — a sequence builtin that TIR
    // cannot evaluate. The lowerer must reject it so the leaf falls back
    // to AST. try_eval_expr returns None because lowering fails with
    // UnsupportedExpr for Expr::Apply(Ident("Append"), ...).
    let op_def = find_operator(&module, "Next").expect("Next should exist");
    let result = program.try_eval_expr(&ctx, &op_def.body);
    assert!(
        result.is_none(),
        "Next body with Append should NOT be TIR-evaluable (Part of #3460)"
    );
}

/// Part of #3460: Verify that try_eval_expr returns None (AST fallback) for
/// an expression containing a sequence builtin call.
#[test]
fn test_try_eval_expr_sequence_builtin_returns_none() {
    let module = parse_module(
        "\
---- MODULE SeqBuiltinLeaf3460 ----
EXTENDS Sequences
VARIABLE s
Op == Append(s, 42)
====",
    );

    let program = TirProgram::from_modules(&module, &[]);
    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&module]);
    ctx.bind_mut("s", Value::Seq(std::sync::Arc::new(vec![].into())));

    // Find the Op body expression
    let op_def = find_operator(&module, "Op").expect("Op should exist");
    let expr = &op_def.body;

    // try_eval_expr should return None because Append is unsupported in TIR
    let result = program.try_eval_expr(&ctx, expr);
    assert!(
        result.is_none(),
        "try_eval_expr should return None for Append call (unsupported sequence builtin)"
    );
}

/// Part of #263: Verify that `Cardinality(...)` is rejected during TIR
/// lowering so guards like `1 < Cardinality(V)` fall back to AST instead of
/// entering generic `Apply` and failing with `UndefinedVar("Cardinality")`.
#[test]
fn test_try_eval_expr_cardinality_guard_returns_none() {
    let module = parse_module(
        "\
---- MODULE CardinalityLeaf263 ----
EXTENDS FiniteSets
Op == 1 < Cardinality({1, 2})
====",
    );

    let program = TirProgram::from_modules(&module, &[]);
    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&module]);

    let op_def = find_operator(&module, "Op").expect("Op should exist");
    let result = program.try_eval_expr(&ctx, &op_def.body);
    assert!(
        result.is_none(),
        "try_eval_expr should return None for guards containing Cardinality(...)"
    );
}

/// Multi-variable SetBuilder must produce a flat set, not a set-of-sets.
/// Bytecode returns Unsupported for multi-var SetBuilder (#3618), so this
/// verifies the tree-walk fallback produces the correct flat semantics.
#[test]
fn test_multi_var_set_builder_produces_flat_set_not_set_of_sets() {
    let module = parse_module(
        "\
---- MODULE MultiVarSetBuilder3618 ----
Op == {x + y : x \\in {1, 2}, y \\in {10, 20}}
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Op")
        .expect("multi-variable SetBuilder should evaluate via tree-walk fallback");

    // TLA+ semantics: {x+y : x \in {1,2}, y \in {10,20}} = {11, 12, 21, 22}
    let expected = Value::set([
        Value::int(11),
        Value::int(12),
        Value::int(21),
        Value::int(22),
    ]);
    assert_eq!(
        value, expected,
        "should be flat set {{11,12,21,22}}, not set-of-sets"
    );

    // Multi-var SetBuilder now compiles to bytecode via BigUnion flattening.
    let (executed, _errors, _fallback) = bytecode_vm_stats();
    assert_eq!(
        executed, 1,
        "multi-var SetBuilder should execute via bytecode (BigUnion flattening)"
    );
}

/// Multi-variable FuncDef must produce a tuple-domain function, not a curried one.
/// Bytecode returns Unsupported for multi-var FuncDef (#3618), so this verifies
/// the tree-walk fallback produces the correct tuple-domain semantics.
#[test]
fn test_multi_var_func_def_produces_tuple_domain_not_curried() {
    let module = parse_module(
        "\
---- MODULE MultiVarFuncDef3618 ----
Op == [x \\in {0, 1}, y \\in {2, 3} |-> x * 10 + y]
====",
    );
    let _guard = enable_bytecode_vm_with_stats_for_test();
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&module, &[]);
    let value = program
        .eval_named_op(&ctx, "Op")
        .expect("multi-variable FuncDef should evaluate via tree-walk fallback");

    // TLA+ semantics: [x \in {0,1}, y \in {2,3} |-> x*10+y] has tuple-domain keys.
    let func = value
        .as_func()
        .expect("multi-variable FuncDef should be a Func with tuple-domain keys");

    // Tuple-domain: <<0,2>> |-> 2, <<0,3>> |-> 3, <<1,2>> |-> 12, <<1,3>> |-> 13
    assert_eq!(
        func.apply(&Value::tuple([Value::int(0), Value::int(2)])),
        Some(&Value::int(2)),
    );
    assert_eq!(
        func.apply(&Value::tuple([Value::int(1), Value::int(3)])),
        Some(&Value::int(13)),
    );
    // A curried function would accept a bare int key — this must NOT work.
    assert_eq!(
        func.apply(&Value::int(0)),
        None,
        "curried key lookup must fail — function should have tuple-domain keys"
    );

    // Multi-var FuncDef now compiles to bytecode via tuple-domain desugaring.
    let (executed, _errors, _fallback) = bytecode_vm_stats();
    assert_eq!(
        executed, 1,
        "multi-var FuncDef should execute via bytecode (tuple-domain desugaring)"
    );
}
