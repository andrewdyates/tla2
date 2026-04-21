// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the precomputed_constants pipeline (Part of #2663).
//!
//! Verifies that zero-arity constant-level operators stored in
//! SharedCtx.precomputed_constants are returned directly by eval_ident,
//! bypassing cache management, dep tracking, and context stripping overhead.
//! This is TLC `SpecProcessor.processConstantDefns()` parity.

use super::*;
use std::sync::Arc;
use tla_core::ast::{Expr, Substitution};
use tla_core::name_intern::intern_name;
use tla_core::{lower, parse_to_syntax_tree, FileId, Span, Spanned};

/// Verify that precomputed_constants short-circuit in eval_ident (fast path).
///
/// Uses sentinel value (999) different from body value (42) to prove
/// the precomputed lookup fires instead of re-evaluating the operator body.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_precomputed_constants_short_circuit_in_eval_ident() {
    // Define a zero-arity operator: MyConst == 42
    let src = r#"
---- MODULE Test ----
MyConst == 42
Op == MyConst
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("lower module");

    // Load operators into shared context
    let mut ctx = EvalCtx::new();
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            Arc::make_mut(ctx.shared_arc_mut())
                .ops
                .insert(def.name.node.clone(), Arc::new(def.clone()));
        }
    }

    // Pre-evaluate MyConst to sentinel 999 (body would produce 42).
    // If the short-circuit works, we get 999; if it re-evaluates, we get 42.
    let name_id = intern_name("MyConst");
    let precomputed_value = Value::int(999);
    Arc::make_mut(ctx.shared_arc_mut())
        .precomputed_constants_mut()
        .insert(name_id, precomputed_value.clone());

    // Evaluate Op (which references MyConst) — should use precomputed sentinel
    let op_def = ctx.shared().ops.get("Op").expect("missing Op");
    let result = eval(&ctx, &op_def.body).expect("eval should succeed");
    assert_eq!(
        result,
        Value::int(999),
        "Op should return precomputed sentinel 999, not body value 42"
    );

    // Verify directly: eval_ident for "MyConst" returns precomputed value
    let myconst_expr = Spanned::new(
        Expr::Ident(
            "MyConst".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ),
        Span::dummy(),
    );
    let direct_result = eval(&ctx, &myconst_expr).expect("direct eval should succeed");
    assert_eq!(direct_result, precomputed_value);
}

/// Verify that precomputed_constants are found via the SLOW path in eval_ident.
///
/// The slow path is taken when `call_by_name_subs` is Some (which makes
/// `can_take_fast_path` false in eval_ident). This exercises the precomputed
/// lookup at eval_ident.rs:417-428 (after call-by-name resolution).
///
/// Uses sentinel value (777) different from body value (5) to prove
/// the precomputed lookup fires in the slow path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_precomputed_constants_found_in_slow_path() {
    let mut ctx = EvalCtx::new();

    // Set up a precomputed constant with sentinel value
    let name_id = intern_name("N");
    Arc::make_mut(ctx.shared_arc_mut())
        .precomputed_constants_mut()
        .insert(name_id, Value::int(777));

    // Also define N as an operator with different value
    let n_def = tla_core::ast::OperatorDef {
        name: Spanned::new("N".to_string(), Span::dummy()),
        params: vec![],
        body: Spanned::new(Expr::Int(5.into()), Span::dummy()),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("N".to_string(), Arc::new(n_def));

    // Set call_by_name_subs to force the slow path in eval_ident.
    // The substitution is for an unrelated name so it won't match "N",
    // but its presence makes can_take_fast_path = false.
    let ctx_slow = ctx.with_call_by_name_subs(vec![Substitution {
        from: Spanned::new("unrelated_var".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Int(0.into()), Span::dummy()),
    }]);

    // Evaluate N — should find precomputed sentinel 777 via slow path,
    // not body value 5.
    let n_expr = Spanned::new(
        Expr::Ident("N".to_string(), tla_core::name_intern::NameId::INVALID),
        Span::dummy(),
    );
    let result = eval(&ctx_slow, &n_expr).expect("eval should succeed");
    assert_eq!(
        result,
        Value::int(777),
        "slow path should find precomputed sentinel 777, not body value 5"
    );
}

/// Verify that a precomputed constant takes priority over re-evaluating the
/// operator body. We pre-compute to a DIFFERENT value than the body would
/// produce, proving the short-circuit is active.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_precomputed_constants_bypass_operator_body_eval() {
    let src = r#"
---- MODULE Test ----
Expensive == 1 + 2 + 3
Op == Expensive
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("lower module");

    let mut ctx = EvalCtx::new();
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            Arc::make_mut(ctx.shared_arc_mut())
                .ops
                .insert(def.name.node.clone(), Arc::new(def.clone()));
        }
    }

    // Pre-compute "Expensive" to 999 (different from 1+2+3=6)
    // If the short-circuit works, we get 999; if it re-evaluates, we get 6.
    let name_id = intern_name("Expensive");
    Arc::make_mut(ctx.shared_arc_mut())
        .precomputed_constants_mut()
        .insert(name_id, Value::int(999));

    let expensive_expr = Spanned::new(
        Expr::Ident(
            "Expensive".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ),
        Span::dummy(),
    );
    let result = eval(&ctx, &expensive_expr).expect("eval should succeed");
    assert_eq!(
        result,
        Value::int(999),
        "precomputed value should bypass operator body evaluation"
    );
}
