// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::try_eval_const_level;
use crate::Env;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{lower, parse_to_syntax_tree, FileId, Span, Spanned};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_eval_const_level_allows_local_deps_but_rejects_state_deps() {
    let mut ctx = EvalCtx::new();

    // Local binding should be allowed (deps.local may be non-empty).
    let y_id = tla_core::name_intern::intern_name("y");
    ctx.push_binding(Arc::from("y"), Value::int(7));
    let y_expr = Spanned::new(Expr::StateVar("y".to_string(), 0, y_id), Span::dummy());
    assert_eq!(try_eval_const_level(&ctx, &y_expr), Some(Value::int(7)));

    // Also allow local deps for regular identifiers (witness vars are typically `Expr::Ident`).
    let y_ident = Spanned::new(
        Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
        Span::dummy(),
    );
    assert_eq!(try_eval_const_level(&ctx, &y_ident), Some(Value::int(7)));

    // A state var read that succeeds via env fallback must still be rejected via deps.state.
    let x_idx = ctx.register_var("x");
    let x_id = tla_core::name_intern::intern_name("x");
    Arc::make_mut(&mut ctx.stable_mut().env).insert(Arc::from("x"), Value::int(42));
    let x_expr = Spanned::new(
        Expr::StateVar("x".to_string(), x_idx.0, x_id),
        Span::dummy(),
    );
    assert_eq!(try_eval_const_level(&ctx, &x_expr), None);

    // Be conservative: if a state var hasn't been rewritten to Expr::StateVar yet,
    // a plain identifier must still be treated as state-dependent unless shadowed.
    let x_ident = Spanned::new(
        Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        Span::dummy(),
    );
    assert_eq!(try_eval_const_level(&ctx, &x_ident), None);

    // Shadowing should still allow const-level evaluation (local witness `x`).
    ctx.push_binding(Arc::from("x"), Value::int(7));
    assert_eq!(try_eval_const_level(&ctx, &x_ident), Some(Value::int(7)));
    assert_eq!(try_eval_const_level(&ctx, &x_expr), Some(Value::int(7)));

    // Primed vars require next-state context and must not be considered constant-level.
    let x_prime_expr = Spanned::new(Expr::Prime(Box::new(x_expr.clone())), Span::dummy());
    assert_eq!(try_eval_const_level(&ctx, &x_prime_expr), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_eval_const_level_uses_tlc_empty_state_ctx_even_if_next_state_is_set() {
    // Regression (Part of #858): try_eval_const_level must not accidentally succeed by
    // resolving primed identifiers via an ambient next_state HashMap.
    let next_state_name = Arc::from("NotAStateVar");
    let mut next = Env::new();
    next.insert(Arc::clone(&next_state_name), Value::int(123));
    let ctx = EvalCtx::new().with_next_state(next);

    let inner = Spanned::new(
        Expr::Ident(
            next_state_name.as_ref().to_string(),
            tla_core::name_intern::NameId::INVALID,
        ),
        Span::dummy(),
    );
    let primed = Spanned::new(Expr::Prime(Box::new(inner)), Span::dummy());
    assert_eq!(try_eval_const_level(&ctx, &primed), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_eval_const_level_returns_none_on_eval_error() {
    let src = r#"
---- MODULE Test ----
Op == 1 \div 0
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("lower module");
    let op_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Op" => Some(def),
            _ => None,
        })
        .expect("missing Op");

    let ctx = EvalCtx::new();
    assert_eq!(try_eval_const_level(&ctx, &op_def.body), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_eval_const_level_allows_bounded_exists_without_inconsistent_deps() {
    // Regression: bounded quantifiers repeatedly bind the same name to different values while
    // evaluating, but those internal iteration vars must not be recorded as deps (or it can
    // spuriously mark `deps.inconsistent`).
    let src = r#"
---- MODULE Test ----
Op == \E y \in {1, 2} : y = 1
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("lower module");
    let op_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Op" => Some(def),
            _ => None,
        })
        .expect("missing Op");

    let ctx = EvalCtx::new();
    assert_eq!(
        try_eval_const_level(&ctx, &op_def.body),
        Some(Value::Bool(true))
    );
}
