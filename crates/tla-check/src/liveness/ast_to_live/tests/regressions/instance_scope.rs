// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! INSTANCE substitution and scope resolution regression tests:
//! #2117 cache bleed, #2434 outer-module scope, #3220 nested INSTANCE,
//! #3166 SubstIn composition.

use super::*;
use num_bigint::BigInt;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_2117_repeated_conversion_different_instance_substitutions_no_cache_bleed() {
    // Regression for #2117:
    // SUBST_CACHE is keyed by (is_next_state, name) and does NOT encode the
    // substitution context. Without eval_entry() clearing the cache between
    // top-level evaluations, converting a constant-level expression that
    // references an INSTANCE-substituted identifier would return a stale
    // cached result from the previous conversion context.
    //
    // Setup: Define a zero-arg operator `my_const == inst_x` where `inst_x`
    // is mapped via INSTANCE substitution. The level checker applies
    // substitutions to operator bodies, so with `inst_x <- TRUE` the body
    // becomes `Bool(true)` → ExprLevel::Constant → constant eval path fires.
    // Evaluating `my_const` triggers eval_ident_explicit_instance_substitution
    // which populates SUBST_CACHE. Without eval_entry clearing the cache,
    // a second conversion with `inst_x <- FALSE` would hit the stale entry.
    let conv = AstToLive::new();

    // Define operator: my_const == inst_x (zero-arg, body references inst_x)
    let mut ops = OpEnv::new();
    ops.insert(
        "my_const".to_string(),
        zero_arg_operator("my_const", ident_expr("inst_x"), false),
    );

    // Expression: [](my_const) — Always wrapping our operator reference
    let expr = spanned(Expr::Always(Box::new(spanned(ident_expr("my_const")))));

    // Context 1: INSTANCE ... WITH inst_x <- TRUE
    let live1 = conv
        .convert(&ctx_with_instance_bool(ops.clone(), true), &expr)
        .unwrap();
    assert_always_bool(&live1, true);

    // Context 2: INSTANCE ... WITH inst_x <- FALSE
    // If SUBST_CACHE leaked from context 1, this would incorrectly return
    // Always(Bool(true)) instead of Always(Bool(false)).
    let live2 = conv
        .convert(&ctx_with_instance_bool(ops, false), &expr)
        .unwrap();
    assert_always_bool(&live2, false);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_2434_outer_module_operator_not_substituted_in_instance_context() {
    // Regression for #2434: outer-module operators (in shared.ops) must NOT
    // have INSTANCE substitutions applied. Only local_ops operators should be.
    // Simulates: pcBar == pc; R == INSTANCE Reachable WITH pc <- pcBar
    let conv = AstToLive::new();
    let mut ctx = EvalCtx::new();
    ctx.register_var("pc");

    // Outer-module op: pcBar == pc (in shared.ops, NOT local_ops)
    Arc::make_mut(ctx.shared_arc_mut()).ops.insert(
        "pcBar".into(),
        zero_arg_operator("pcBar", ident_expr("pc"), false),
    );

    // Instanced-module op: inst_action == pc' (in local_ops)
    let mut local_ops = OpEnv::new();
    local_ops.insert(
        "inst_action".into(),
        zero_arg_operator(
            "inst_action",
            Expr::Prime(Box::new(Spanned::dummy(ident_expr("pc")))),
            true,
        ),
    );

    let ctx = ctx
        .with_local_ops(local_ops)
        .with_instance_substitutions(vec![Substitution {
            from: Spanned::dummy("pc".into()),
            to: Spanned::dummy(Expr::Ident(
                "pcBar".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
        }]);

    assert_named_level(&conv, &ctx, "pcBar", ExprLevel::State);
    assert_named_level(&conv, &ctx, "inst_action", ExprLevel::Action);

    // Temporal conversion: [](pcBar) → Always(StatePred(...))
    let expr = spanned(Expr::Always(Box::new(spanned(ident_expr("pcBar")))));
    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::Always(inner) = &live else {
        panic!("Expected Always, got: {live:?}");
    };
    assert!(
        matches!(inner.as_ref(), LiveExpr::StatePred { .. }),
        "pcBar should be StatePred, got: {inner:?}"
    );
}

/// Regression test for #3220: resolving an outer-module action operator from
/// inside an INSTANCE scope must discard the instanced module's local_ops.
///
/// Without the fix, `resolve_action_expr` inlined `terminationDetected` using
/// `without_instance_substitutions()`, which left `local_ops` in scope. The
/// inner-module `Node == 0` then shadowed the outer-module `Node == 1`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3220_action_resolve_outer_operator_uses_outer_scope() {
    let conv = AstToLive::new();
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");

    Arc::make_mut(ctx.shared_arc_mut()).ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Int(BigInt::from(1)), false),
    );
    Arc::make_mut(ctx.shared_arc_mut()).ops.insert(
        "terminationDetected".into(),
        zero_arg_operator(
            "terminationDetected",
            Expr::Eq(
                Box::new(spanned(Expr::Prime(Box::new(spanned(ident_expr("x")))))),
                Box::new(spanned(ident_expr("Node"))),
            ),
            true,
        ),
    );

    let mut local_ops = OpEnv::new();
    local_ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Int(BigInt::from(0)), false),
    );

    let ctx = ctx
        .with_local_ops(local_ops)
        .with_instance_substitutions(vec![Substitution {
            from: Spanned::dummy("inst_x".to_string()),
            to: Spanned::dummy(ident_expr("x")),
        }]);

    let resolved = conv.resolve_action_expr(&ctx, &spanned(ident_expr("terminationDetected")));
    let Expr::Eq(_, rhs) = &resolved.node else {
        panic!(
            "expected terminationDetected to inline to an equality, got {:?}",
            resolved.node
        );
    };
    match &rhs.node {
        Expr::Int(value) => assert_eq!(
            value,
            &BigInt::from(1),
            "outer-module Node should resolve to 1, not the instanced module's 0"
        ),
        other => panic!("expected right-hand side to fold to Int(1), got {other:?}"),
    }
}

/// Regression test for #3220: temporal conversion of an outer-module operator
/// inside an INSTANCE scope must also discard the instanced module's local_ops.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3220_temporal_convert_outer_operator_uses_outer_scope() {
    let conv = AstToLive::new();
    let mut ctx = EvalCtx::new();

    Arc::make_mut(ctx.shared_arc_mut()).ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Bool(true), false),
    );
    Arc::make_mut(ctx.shared_arc_mut()).ops.insert(
        "terminationDetected".into(),
        zero_arg_operator("terminationDetected", ident_expr("Node"), false),
    );

    let mut local_ops = OpEnv::new();
    local_ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Bool(false), false),
    );

    let ctx = ctx
        .with_local_ops(local_ops)
        .with_instance_substitutions(vec![Substitution {
            from: Spanned::dummy("inst_node".to_string()),
            to: Spanned::dummy(ident_expr("Node")),
        }]);

    let live = conv
        .convert(
            &ctx,
            &spanned(Expr::Always(Box::new(spanned(ident_expr(
                "terminationDetected",
            ))))),
        )
        .unwrap();

    assert!(
        matches!(&live, LiveExpr::Always(inner) if matches!(inner.as_ref(), LiveExpr::Bool(true))),
        "outer-module Node should resolve to TRUE during temporal conversion, got {live:?}"
    );
}

/// Regression test for #3220: nested INSTANCE rewinds must restore the
/// enclosing instance's operator scope, not drop all local_ops.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3220_action_resolve_nested_instance_uses_enclosing_outer_scope() {
    let conv = AstToLive::new();
    let mut root_ctx = EvalCtx::new();
    root_ctx.register_var("x");

    Arc::make_mut(root_ctx.shared_arc_mut()).ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Int(BigInt::from(99)), false),
    );
    Arc::make_mut(root_ctx.shared_arc_mut()).ops.insert(
        "terminationDetected".into(),
        zero_arg_operator(
            "terminationDetected",
            Expr::Eq(
                Box::new(spanned(Expr::Prime(Box::new(spanned(ident_expr("x")))))),
                Box::new(spanned(ident_expr("Node"))),
            ),
            true,
        ),
    );

    let mut outer_ops = OpEnv::new();
    outer_ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Int(BigInt::from(1)), false),
    );
    let outer_ctx = root_ctx.with_instance_scope(outer_ops, vec![]);

    let mut inner_ops = OpEnv::new();
    inner_ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Int(BigInt::from(0)), false),
    );
    let inner_ctx = outer_ctx.with_instance_scope(inner_ops, vec![]);

    let resolved =
        conv.resolve_action_expr(&inner_ctx, &spanned(ident_expr("terminationDetected")));
    let Expr::Eq(_, rhs) = &resolved.node else {
        panic!(
            "expected terminationDetected to inline to an equality, got {:?}",
            resolved.node
        );
    };
    match &rhs.node {
        Expr::Int(value) => assert_eq!(
            value,
            &BigInt::from(1),
            "nested INSTANCE rewind should restore the enclosing outer Node == 1"
        ),
        other => panic!("expected right-hand side to fold to Int(1), got {other:?}"),
    }
}

/// Regression test for #3220: temporal conversion in nested INSTANCE scopes
/// must restore the enclosing instance's operator scope before inlining.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3220_temporal_convert_nested_instance_uses_enclosing_outer_scope() {
    let conv = AstToLive::new();
    let mut root_ctx = EvalCtx::new();

    Arc::make_mut(root_ctx.shared_arc_mut()).ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Bool(false), false),
    );
    Arc::make_mut(root_ctx.shared_arc_mut()).ops.insert(
        "terminationDetected".into(),
        zero_arg_operator("terminationDetected", ident_expr("Node"), false),
    );

    let mut outer_ops = OpEnv::new();
    outer_ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Bool(true), false),
    );
    let outer_ctx = root_ctx.with_instance_scope(outer_ops, vec![]);

    let mut inner_ops = OpEnv::new();
    inner_ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Bool(false), false),
    );
    let inner_ctx = outer_ctx.with_instance_scope(inner_ops, vec![]);

    let live = conv
        .convert(
            &inner_ctx,
            &spanned(Expr::Always(Box::new(spanned(ident_expr(
                "terminationDetected",
            ))))),
        )
        .unwrap();

    assert!(
        matches!(&live, LiveExpr::Always(inner) if matches!(inner.as_ref(), LiveExpr::Bool(true))),
        "nested INSTANCE rewind should restore the enclosing outer Node == TRUE, got {live:?}"
    );
}

/// Regression test for #3166: SubstIn in temporal conversion must compose
/// substitutions and descend into the body, not treat it as an opaque leaf.
///
/// Without the fix, `SubstIn(subs, body)` in `convert_temporal` fell through
/// to `predicate_by_level`, which either attempted constant eval (crash if
/// the substitution target was state-level) or wrapped the entire SubstIn
/// as an opaque StatePred without applying substitutions. This caused
/// EWD998Chan's PROPERTY `EWD998!Spec` to crash with "nonexistent field 'pos'"
/// because `token` resolved to the outer module's raw inbox message instead of
/// the INSTANCE-substituted record `[pos |-> tpos, ...]`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3166_subst_in_temporal_conversion_descends_into_body() {
    // Construct: SubstIn([v <- TRUE], [](v))
    // The temporal converter should compose the substitution, descend into
    // the body []v, and produce Always(Bool(true)) — not an opaque StatePred.
    let conv = AstToLive::new();
    let ctx = make_ctx();

    let subst_in_always = spanned(Expr::SubstIn(
        vec![Substitution {
            from: Spanned::dummy("v".to_string()),
            to: Spanned::dummy(Expr::Bool(true)),
        }],
        Box::new(spanned(Expr::Always(Box::new(spanned(Expr::Ident(
            "v".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
    ));

    let result = conv.convert(&ctx, &subst_in_always);
    assert!(
        result.is_ok(),
        "SubstIn wrapping temporal should not error: {:?}",
        result.unwrap_err()
    );
    let live = result.unwrap();
    // The converter should descend through SubstIn into the Always body,
    // resolve `v` via the composed substitution to TRUE, and produce Always(Bool(true)).
    assert!(
        matches!(&live, LiveExpr::Always(inner) if matches!(inner.as_ref(), LiveExpr::Bool(true))),
        "Expected Always(Bool(true)) after SubstIn substitution, got: {live:?}"
    );
}

/// Regression test for #3166: SubstIn in action expression resolution must
/// compose substitutions and descend into the body.
///
/// This tests the action_resolve.rs path which handles SubstIn during
/// the action expression resolution used by fairness expansion (WF_/SF_).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3166_subst_in_action_resolve_composes_substitutions() {
    use tla_core::ast::OperatorDef;

    let conv = AstToLive::new();
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");

    // Define operator Next == x' = x + 1 (action-level)
    let next_body = Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
    );
    Arc::make_mut(ctx.shared_arc_mut()).ops.insert(
        "Next".to_string(),
        Arc::new(OperatorDef {
            name: spanned("Next".to_string()),
            params: vec![],
            body: spanned(next_body.clone()),
            local: false,
            contains_prime: true,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }),
    );

    // Construct: SubstIn([], Next) — wrapping an action expression
    // The resolver should descend through SubstIn and resolve Next's body.
    let subst_in_action = spanned(Expr::SubstIn(
        vec![], // empty substitutions — just tests the descent
        Box::new(spanned(Expr::Ident(
            "Next".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let resolved = conv.resolve_action_expr(&ctx, &subst_in_action);
    // The resolved expression should be the inlined body of Next (x' = x + 1),
    // not an opaque SubstIn wrapper.
    assert!(
        !matches!(&resolved.node, Expr::SubstIn(_, _)),
        "SubstIn should be unwrapped by action resolver, got: {:?}",
        resolved.node
    );
}
