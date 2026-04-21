// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::tir::{
    enable_tir_eval_probe, tir_eval_probe_snapshot, TirEvalProbeCounts, TirExprEvalAttempt,
    TirProgram,
};
use tla_core::ast::{Expr, Module, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId, Spanned};

fn parse_module(src: &str) -> Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors for module:\n{src}\n{:?}",
        lower_result.errors
    );
    lower_result.module.expect("module should lower")
}

fn tir_value_for_named_op(module: &Module, name: &str) -> Value {
    clear_for_test_reset();
    let program = TirProgram::from_modules(module, &[]);
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);
    program
        .eval_named_op(&ctx, name)
        .unwrap_or_else(|err| panic!("TIR eval of '{name}' should succeed: {err:?}"))
}

fn ast_value_for_named_op(module: &Module, name: &str) -> Value {
    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);
    ctx.eval_op(name)
        .unwrap_or_else(|err| panic!("AST eval of '{name}' should succeed: {err:?}"))
}

fn probe_counts(
    snapshot: &std::collections::BTreeMap<String, TirEvalProbeCounts>,
    name: &str,
) -> TirEvalProbeCounts {
    snapshot.get(name).copied().unwrap_or_default()
}

fn find_operator_body<'a>(module: &'a Module, name: &str) -> &'a Spanned<Expr> {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == name => Some(&def.body),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operator '{name}' should exist"))
}

const STRUCTURED_MODULE: &str = r#"
---- MODULE TirStructuredContract ----
TupleValue == <<1, 2>>
RangeValue == 1..3
====
"#;

const PARAMETERIZED_LET_MODULE: &str = r#"
---- MODULE TirParameterizedLet ----
\* Parameterized LET: Op(x) == body lowered to LAMBDA + binding (Part of #3262)
LetApply == LET Double(x) == x + x IN Double(3)
LetMultiParam == LET Add(a, b) == a + b IN Add(2, 5)
LetMixed == LET c == 10
                 Scale(x) == x * c
             IN Scale(4)
====
"#;

const RECURSIVE_LET_LEAF_MODULE: &str = r#"
---- MODULE TirRecursiveLetLeaf ----
Maximum(S) ==
  LET Max[T \in SUBSET S] ==
        IF T = {} THEN -1
        ELSE LET n == CHOOSE n \in T : TRUE
                 rmax == Max[T \ {n}]
             IN IF n >= rmax THEN n ELSE rmax
  IN Max[S]

Leaf == LET mset == {
                      [bal |-> 1, val |-> 10],
                      [bal |-> 3, val |-> 30],
                      [bal |-> 2, val |-> 20]
                    }
            maxbal == Maximum({m.bal : m \in mset})
            val == IF maxbal = -1
                   THEN -1
                   ELSE (CHOOSE m \in mset : m.bal = maxbal).val
        IN <<maxbal, val>>
====
"#;

const RECURSIVE_OPERATOR_MODULE: &str = r#"
---- MODULE TirRecursiveOperator ----
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

Op == LET sc == [i \in {1, 2} |-> i]
      IN Sum(sc, {1, 2})
====
"#;

const PRIME_CONTRACT_MODULE: &str = r#"
---- MODULE TirPrimeContract ----
VARIABLE x
PrimeRead == x'
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_step2_tuple_matches_ast() {
    let module = parse_module(STRUCTURED_MODULE);

    let ast_value = ast_value_for_named_op(&module, "TupleValue");
    assert_eq!(
        ast_value,
        Value::tuple([Value::int(1), Value::int(2)]),
        "AST baseline should confirm the operator itself is valid"
    );

    let tir_value = tir_value_for_named_op(&module, "TupleValue");
    assert_eq!(
        tir_value, ast_value,
        "expected TupleValue parity, AST={ast_value:?}, TIR={tir_value:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_step2_range_matches_ast() {
    let module = parse_module(STRUCTURED_MODULE);

    let ast_value = ast_value_for_named_op(&module, "RangeValue");
    assert_eq!(
        ast_value.to_string(),
        "1..3",
        "AST baseline should confirm the operator itself is valid"
    );

    let tir_value = tir_value_for_named_op(&module, "RangeValue");
    assert_eq!(
        tir_value, ast_value,
        "expected RangeValue parity, AST={ast_value:?}, TIR={tir_value:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_try_eval_expr_unbound_prime_falls_back_to_ast() {
    // Part of #3264: TIR now falls back to AST (returns None) on any eval error,
    // including PrimedVariableNotBound. The old contract returned Some(Err(...))
    // which leaked TIR implementation details; the new contract signals "use AST"
    // so the caller gets correct behavior regardless of TIR expressiveness gaps.
    let module = parse_module(PRIME_CONTRACT_MODULE);
    let program = TirProgram::from_modules(&module, &[]);
    let expr = find_operator_body(&module, "PrimeRead");
    let ctx = EvalCtx::new();

    let result = program.try_eval_expr(&ctx, expr);
    assert!(
        result.is_none(),
        "prime leaf error should trigger AST fallback (None), got: {result:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_try_eval_expr_detailed_preserves_eval_error() {
    let module = parse_module(PRIME_CONTRACT_MODULE);
    let program = TirProgram::from_modules(&module, &[]);
    let expr = find_operator_body(&module, "PrimeRead");
    let ctx = EvalCtx::new();

    match program.try_eval_expr_detailed(&ctx, expr) {
        TirExprEvalAttempt::Evaluated(Err(_)) => {}
        other => panic!("detailed attempt should preserve TIR eval error, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_try_eval_expr_eval_error_caches_lowering_but_retries_eval() {
    // Part of #4113: with shared expr_cache, eval failures no longer mark
    // the expression as AST-only. The lowered TIR remains cached and is
    // re-evaluated on subsequent calls (eval might succeed for different
    // runtime state). We only skip re-lowering, not re-evaluation.
    let module = parse_module(PRIME_CONTRACT_MODULE);
    clear_for_test_reset();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();

    let program = TirProgram::from_modules(&module, &[]).with_probe_label("PrimeRead");
    let expr = find_operator_body(&module, "PrimeRead");
    let ctx = EvalCtx::new();

    let first = program.try_eval_expr(&ctx, expr);
    assert!(
        first.is_none(),
        "prime leaf error should trigger AST fallback (None), got: {first:?}"
    );

    let mid = tir_eval_probe_snapshot();
    let mid_counts = probe_counts(&mid, "PrimeRead");
    let before_counts = probe_counts(&before, "PrimeRead");
    assert_eq!(
        mid_counts
            .expr_evals
            .saturating_sub(before_counts.expr_evals),
        1,
        "the first failing TIR attempt should still be observed once"
    );

    let second = program.try_eval_expr(&ctx, expr);
    assert!(
        second.is_none(),
        "re-evaluated cached TIR should still fail (same context), got: {second:?}"
    );

    let after = tir_eval_probe_snapshot();
    let after_counts = probe_counts(&after, "PrimeRead");
    assert_eq!(
        after_counts
            .expr_evals
            .saturating_sub(mid_counts.expr_evals),
        1,
        "cached TIR should be re-evaluated (not skipped) on second call"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_named_op_probe_records_named_and_expr_hits() {
    let module = parse_module(
        "\
---- MODULE TirProbeNamedOp ----
Value == 1 + 1
====",
    );
    clear_for_test_reset();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let program = TirProgram::from_modules(&module, &[]).with_probe_label("Value");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let value = program
        .eval_named_op(&ctx, "Value")
        .expect("named-op TIR eval should succeed");
    assert_eq!(value, Value::int(2), "probe canary should evaluate Value");

    let after = tir_eval_probe_snapshot();
    let before_counts = probe_counts(&before, "Value");
    let after_counts = probe_counts(&after, "Value");
    assert_eq!(
        after_counts
            .expr_evals
            .saturating_sub(before_counts.expr_evals),
        1,
        "successful named-op replay should record one expr evaluation on the TIR path"
    );
    assert_eq!(
        after_counts
            .named_op_evals
            .saturating_sub(before_counts.named_op_evals),
        1,
        "named-op replay should remain observable separately from expr hits"
    );
}

// === Part of #3392: recursive user-operator TIR resolution tests ===
//
// These tests verify that nested user-defined operator references stay on the
// TIR path instead of bouncing back to AST through ctx.eval_op().

const NESTED_ZERO_ARG_MODULE: &str = r#"
---- MODULE TirNestedZeroArg ----
Inner == 1
Outer == Inner + 1
====
"#;

const NESTED_PARAMETERIZED_MODULE: &str = r#"
---- MODULE TirNestedParameterized ----
Double(x) == x + x
Outer == Double(3)
====
"#;

const NESTED_CHAIN_MODULE: &str = r#"
---- MODULE TirNestedChain ----
A == 10
B == A + 5
C == B * 2
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_nested_zero_arg_stays_on_tir_path() {
    // Part of #3392: when Outer references Inner, the TIR evaluator should
    // resolve Inner through the active TirProgram instead of bouncing to AST.
    let module = parse_module(NESTED_ZERO_ARG_MODULE);

    let ast_value = ast_value_for_named_op(&module, "Outer");
    assert_eq!(ast_value, Value::int(2), "AST: Outer == Inner + 1 == 2");

    let tir_value = tir_value_for_named_op(&module, "Outer");
    assert_eq!(
        tir_value, ast_value,
        "TIR/AST parity for nested zero-arg operator chain"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_nested_zero_arg_probe_records_ast_fallback_when_recursive_resolve_disabled() {
    // Part of #3392: recursive TIR resolution is disabled by default, so a
    // nested zero-arg operator reference should bounce back to AST. The probe
    // must record that fallback or the operator-level evidence lane is blind.
    let module = parse_module(NESTED_ZERO_ARG_MODULE);

    clear_for_test_reset();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();

    let program = TirProgram::from_modules(&module, &[]).with_probe_label("Outer");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let value = program
        .eval_named_op(&ctx, "Outer")
        .expect("should succeed");
    assert_eq!(value, Value::int(2));

    let after = tir_eval_probe_snapshot();
    let outer_before = probe_counts(&before, "Outer");
    let outer_after = probe_counts(&after, "Outer");

    // Outer should have at least 1 named_op_eval (from eval_named_op).
    // With bytecode VM enabled (#3697 StoredTirBody), the VM may also
    // resolve nested operators through the TIR path, producing additional
    // probe entries. The key invariant: at least 1, never 0.
    let outer_named_delta = outer_after
        .named_op_evals
        .saturating_sub(outer_before.named_op_evals);
    assert!(
        outer_named_delta >= 1,
        "Outer should have at least 1 named_op_eval, got {outer_named_delta}"
    );
    let outer_expr_delta = outer_after
        .expr_evals
        .saturating_sub(outer_before.expr_evals);
    assert!(
        outer_expr_delta >= 1,
        "Outer should have at least 1 expr_eval, got {outer_expr_delta}"
    );

    // Inner is evaluated through the zero-arg operator cache path
    // (eval_resolved_zero_arg_op → eval_zero_arg_cached → eval()) which does
    // NOT go through TirProgram::eval_named_op(), so no TIR probe events are
    // recorded for "Inner". This is correct: the zero-arg cache was added to
    // avoid re-evaluating CHOOSE expressions on every access (O(1) cached
    // lookup vs O(n) CHOOSE per access). The inner eval() dispatches through
    // TIR when available, but does not record named_op_eval probe entries.
    let inner_before = probe_counts(&before, "Inner");
    let inner_after = probe_counts(&after, "Inner");
    assert_eq!(
        inner_after
            .named_op_evals
            .saturating_sub(inner_before.named_op_evals),
        0,
        "Inner goes through zero-arg cache path, not TirProgram::eval_named_op — no probe recorded"
    );
    assert_eq!(
        inner_after
            .expr_evals
            .saturating_sub(inner_before.expr_evals),
        0,
        "Inner should not record a TIR expr eval through the zero-arg cache path"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_nested_parameterized_stays_on_tir_path() {
    // Part of #3392: when Outer calls Double(3), the closure created for Double
    // should have a TIR body attached, so application stays in TIR.
    let module = parse_module(NESTED_PARAMETERIZED_MODULE);

    let ast_value = ast_value_for_named_op(&module, "Outer");
    assert_eq!(ast_value, Value::int(6), "AST: Double(3) == 6");

    let tir_value = tir_value_for_named_op(&module, "Outer");
    assert_eq!(
        tir_value, ast_value,
        "TIR/AST parity for nested parameterized operator"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_nested_chain_three_levels() {
    // Part of #3392: three-level chain: C -> B -> A, all should stay in TIR.
    let module = parse_module(NESTED_CHAIN_MODULE);

    let ast_value = ast_value_for_named_op(&module, "C");
    assert_eq!(ast_value, Value::int(30), "AST: C == (10 + 5) * 2 == 30");

    let tir_value = tir_value_for_named_op(&module, "C");
    assert_eq!(
        tir_value, ast_value,
        "TIR/AST parity for three-level operator chain"
    );
}

// === Parameterized LET parity tests (Part of #3262) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_parameterized_let_single_param_matches_ast() {
    let module = parse_module(PARAMETERIZED_LET_MODULE);

    let ast_value = ast_value_for_named_op(&module, "LetApply");
    assert_eq!(ast_value, Value::int(6), "AST: Double(3) should be 6");

    let tir_value = tir_value_for_named_op(&module, "LetApply");
    assert_eq!(
        tir_value, ast_value,
        "TIR/AST parity for parameterized LET Double(x): TIR={tir_value:?}, AST={ast_value:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_parameterized_let_multi_param_matches_ast() {
    let module = parse_module(PARAMETERIZED_LET_MODULE);

    let ast_value = ast_value_for_named_op(&module, "LetMultiParam");
    assert_eq!(ast_value, Value::int(7), "AST: Add(2, 5) should be 7");

    let tir_value = tir_value_for_named_op(&module, "LetMultiParam");
    assert_eq!(
        tir_value, ast_value,
        "TIR/AST parity for parameterized LET Add(a, b): TIR={tir_value:?}, AST={ast_value:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_parameterized_let_mixed_with_zero_param_matches_ast() {
    let module = parse_module(PARAMETERIZED_LET_MODULE);

    let ast_value = ast_value_for_named_op(&module, "LetMixed");
    assert_eq!(
        ast_value,
        Value::int(40),
        "AST: Scale(4) with c==10 should be 40"
    );

    let tir_value = tir_value_for_named_op(&module, "LetMixed");
    assert_eq!(
        tir_value, ast_value,
        "TIR/AST parity for mixed LET (zero-param + parameterized): TIR={tir_value:?}, AST={ast_value:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_recursive_local_operator_via_zero_arg_let_matches_ast() {
    let module = parse_module(RECURSIVE_LET_LEAF_MODULE);

    let ast_value = ast_value_for_named_op(&module, "Leaf");
    assert_eq!(
        ast_value,
        Value::tuple([Value::int(3), Value::int(30)]),
        "AST baseline should confirm the recursive Maximum sketch"
    );

    let tir_value = tir_value_for_named_op(&module, "Leaf");
    assert_eq!(
        tir_value, ast_value,
        "TIR/AST parity for recursive local operator through zero-arg LET: TIR={tir_value:?}, AST={ast_value:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_try_eval_expr_recursive_local_operator_via_zero_arg_let_stays_on_tir() {
    let module = parse_module(RECURSIVE_LET_LEAF_MODULE);
    let expr = find_operator_body(&module, "Leaf");
    let ast_value = ast_value_for_named_op(&module, "Leaf");

    clear_for_test_reset();
    let program = TirProgram::from_modules(&module, &[]).with_probe_label("Leaf");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    match program.try_eval_expr_detailed(&ctx, expr) {
        TirExprEvalAttempt::Evaluated(Ok(tir_value)) => assert_eq!(
            tir_value, ast_value,
            "leaf-level TIR eval must match AST for recursive local operator through zero-arg LET"
        ),
        TirExprEvalAttempt::Evaluated(Err(err)) => {
            panic!("leaf-level TIR eval should not error for recursive LET sketch: {err:?}")
        }
        TirExprEvalAttempt::Unsupported => {
            panic!("leaf-level TIR eval should lower the recursive LET sketch")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_recursive_module_operator_matches_ast() {
    let module = parse_module(RECURSIVE_OPERATOR_MODULE);

    let ast_value = ast_value_for_named_op(&module, "Op");
    assert_eq!(
        ast_value,
        Value::int(3),
        "AST baseline should confirm the recursive operator sketch"
    );

    let tir_value = tir_value_for_named_op(&module, "Op");
    assert_eq!(
        tir_value, ast_value,
        "TIR/AST parity for recursive parameterized operator should hold: TIR={tir_value:?}, AST={ast_value:?}"
    );
}
