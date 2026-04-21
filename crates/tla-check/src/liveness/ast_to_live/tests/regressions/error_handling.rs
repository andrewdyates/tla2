// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error handling regression tests: #1744 div-by-zero edge cases,
//! #2806 eval_speculative Err path tests.

use super::*;
use num_bigint::BigInt;

/// Regression test for #1744: constant-level DivisionByZero must return
/// EvalFailed, not silently promote to state predicate.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1744_division_by_zero_not_silently_promoted() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // 1 \div 0 — constant-level expression that triggers DivisionByZero
    let expr = spanned(Expr::Div(
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    let result = conv.convert(&ctx, &expr);
    assert!(
        result.is_err(),
        "DivisionByZero should not be silently promoted to state predicate"
    );
    assert!(
        matches!(result.unwrap_err(), ConvertError::EvalFailed { .. }),
        "Expected ConvertError::EvalFailed for DivisionByZero"
    );
}

/// Regression test for #1744: UndefinedVar in constant-level context should
/// still fall back to state predicate (level was misclassified).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1744_unbound_var_still_falls_back_to_state_pred() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // Define an operator "C" whose body references undefined "missing_var".
    // get_level_with_ctx sees no state-level deps → Constant, but eval fails
    // with UndefinedVar.
    let mut ctx_with_op = ctx.clone();
    ctx_with_op.define_op(
        "C".to_string(),
        OperatorDef {
            name: spanned("C".to_string()),
            params: vec![],
            body: spanned(Expr::Ident(
                "missing_var".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        },
    );

    // Apply "C" — get_level_with_ctx should see it as Constant (op with no
    // state-level deps), eval will fail with UndefinedVar.
    let expr = spanned(Expr::Ident(
        "C".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));

    let result = conv.convert(&ctx_with_op, &expr);
    // Should succeed — UndefinedVar falls back to state predicate
    assert!(
        result.is_ok(),
        "UndefinedVar should fall back to state predicate, got: {:?}",
        result.unwrap_err()
    );
}

// ============= Part of #2806: eval_speculative Err(_) path tests =============
//
// These tests verify that unexpected eval errors (not in ConstantResolution
// class) at each call site produce warnings rather than being silently swallowed.

/// Call site A: config constant whose definition triggers DivisionByZero.
///
/// resolve_action_expr_node evaluates config constants via eval_speculative
/// with FallbackClass::ConstantResolution. DivisionByZero is NOT in that class,
/// so it reaches the Err(_) path. The expression should be kept as Ident.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_action_config_constant_div_by_zero_warns_and_keeps_ident() {
    use tla_core::ast::OperatorDef;

    let conv = AstToLive::new();
    let mut ctx = EvalCtx::new();

    // Register "BadConst" as a config constant
    Arc::make_mut(ctx.shared_arc_mut())
        .config_constants
        .insert("BadConst".to_string());

    // Define BadConst == 1 \div 0 (triggers DivisionByZero)
    let op_def = OperatorDef {
        name: spanned("BadConst".to_string()),
        params: Vec::new(),
        body: spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        )),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("BadConst".to_string(), Arc::new(op_def));

    let resolved = conv.resolve_action_expr(
        &ctx,
        &spanned(Expr::Ident(
            "BadConst".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );

    // The expression should be kept as Ident (not crash, not inline)
    assert!(
        matches!(&resolved.node, Expr::Ident(name, _) if name == "BadConst"),
        "config constant with DivisionByZero should be kept as Ident, got: {:?}",
        resolved.node
    );
}

/// Call site B: zero-arg constant-level operator whose body triggers DivisionByZero.
///
/// resolve_action_expr_node inlines zero-arg ops and tries to evaluate
/// constant-level bodies via eval_speculative. DivisionByZero reaches the
/// Err(_) path. The resolved (inlined) expression should be returned.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_action_zero_arg_op_div_by_zero_warns_and_keeps_resolved() {
    use tla_core::ast::OperatorDef;

    let conv = AstToLive::new();
    let mut ctx = EvalCtx::new();

    // Define BadOp == 1 \div 0 (constant-level, triggers DivisionByZero)
    let op_def = OperatorDef {
        name: spanned("BadOp".to_string()),
        params: Vec::new(),
        body: spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        )),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("BadOp".to_string(), Arc::new(op_def));

    let resolved = conv.resolve_action_expr(
        &ctx,
        &spanned(Expr::Ident(
            "BadOp".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );

    // The expression should be the inlined body (IntDiv), not crash
    assert!(
        matches!(&resolved.node, Expr::IntDiv(_, _)),
        "zero-arg op with DivisionByZero should return resolved body, got: {:?}",
        resolved.node
    );
}

/// Call site C: state-level expression with DivisionByZero under quantifier bindings.
///
/// convert_expr at ExprLevel::State with current_quantifier_bindings().is_some()
/// evaluates via eval_bool_speculative with FallbackClass::ConstantResolution.
/// DivisionByZero is NOT in ConstantResolution, so it reaches the Err(_) path.
/// The expression should fall through to StatePred (not crash, not error).
///
/// Part of #3066, #2806.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_quantifier_binding_div_by_zero_warns_and_keeps_state_pred() {
    use crate::eval::BindingChain;
    use num_bigint::BigInt;

    let conv = AstToLive::new();
    let ctx = EvalCtx::new();

    // Push quantifier bindings to make current_quantifier_bindings() return Some.
    // Use a dummy binding — the key is that the binding chain is non-None.
    let chain = BindingChain::empty().cons(
        tla_core::name_intern::NameId::INVALID,
        crate::eval::BindingValue::eager(Value::int(1)),
    );
    let _guard = conv.push_quantifier_bindings(Some(chain));

    // Create a state-level expression that triggers DivisionByZero:
    // `x + (1 \div 0)` — the Ident `x` makes it state-level,
    // and the IntDiv(1, 0) produces DivisionByZero during speculative eval.
    let expr = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));

    // The Err path logs a warning and falls through to StatePred
    let result = conv.convert(&ctx, &expr);
    assert!(
        result.is_ok(),
        "DivisionByZero under quantifier bindings should not propagate as error, got: {:?}",
        result.unwrap_err()
    );
    let live = result.unwrap();
    assert!(
        matches!(live, LiveExpr::StatePred { .. }),
        "expression should be kept as StatePred, got: {live:?}"
    );
}
