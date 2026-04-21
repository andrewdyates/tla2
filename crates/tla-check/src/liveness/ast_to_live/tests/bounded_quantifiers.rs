// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded quantifier liveness tests (#838/#915/#916/#917): non-temporal quantifier handling
//!
//! Split from liveness/ast_to_live/tests.rs — Part of #2779

use super::helpers::make_ctx;
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_non_temporal_becomes_predicate_by_level() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // \E x \in {1, 2}: x = y
    //
    // This is state-level (because of the free identifier `y`), so it must become a
    // predicate node rather than being evaluated as a constant boolean.
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ])))),
        pattern: None,
    }];
    let body = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::StatePred { expr, .. } = live else {
        panic!("Expected StatePred");
    };
    assert!(matches!(&expr.node, Expr::Exists(_, _)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_constant_level_constant_folds_to_bool() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // \E x \in {1}: TRUE
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
            BigInt::from(1),
        ))])))),
        pattern: None,
    }];
    let body = spanned(Expr::Bool(true));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    assert!(matches!(live, LiveExpr::Bool(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_domain_eval_error_preserves_state_level_predicate() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // \E x \in S: y \in x  (S/y are unknown in ctx; domain eval would fail in TLC)
    //
    // This must still be classified as state-level (no primed identifiers).
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::Ident(
            "S".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        pattern: None,
    }];
    let body = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::StatePred { expr, .. } = live else {
        panic!("Expected StatePred");
    };
    assert!(matches!(&expr.node, Expr::Exists(_, _)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_domain_eval_error_preserves_action_level_predicate() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // \E x \in S: y' \in x  (S/y are unknown in ctx; domain eval would fail in TLC)
    //
    // This must still be classified as action-level (because of the prime).
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::Ident(
            "S".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        pattern: None,
    }];
    let body = spanned(Expr::In(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::ActionPred { expr, .. } = live else {
        panic!("Expected ActionPred");
    };
    assert!(matches!(&expr.node, Expr::Exists(_, _)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_non_enumerable_domain_becomes_predicate_by_level() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // \E x \in Seq({1}): x = y
    //
    // `Seq({1})` is non-enumerable for context enumeration, but for non-temporal bounded
    // quantifiers TLC treats the original expression as a leaf predicate by level (no
    // expansion / enumeration attempts).
    let seq_domain = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Seq".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::SetEnum(vec![spanned(Expr::Int(
            BigInt::from(1),
        ))]))],
    ));
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(seq_domain)),
        pattern: None,
    }];
    let body = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::StatePred { expr, .. } = live else {
        panic!("Expected StatePred");
    };
    assert!(matches!(&expr.node, Expr::Exists(_, _)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_constant_level_non_enumerable_domain_does_not_error() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // \E x \in Seq({1}): TRUE
    //
    // Even though `Seq({1})` is not enumerable, converting a constant-level bounded
    // quantifier must not fail liveness conversion with a temporal-level expansion error.
    let seq_domain = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Seq".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::SetEnum(vec![spanned(Expr::Int(
            BigInt::from(1),
        ))]))],
    ));
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(seq_domain)),
        pattern: None,
    }];
    let body = spanned(Expr::Bool(true));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    match live {
        LiveExpr::Bool(true) => {}
        LiveExpr::StatePred { .. } => {}
        other => panic!("Expected Bool(true) or StatePred, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_action_level_non_enumerable_domain_becomes_predicate_by_level() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // \E x \in Seq({1}): y' \in x
    //
    // This is action-level because of the prime, so it must become an ActionPred leaf
    // without attempting to enumerate the (non-enumerable) domain.
    let seq_domain = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Seq".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::SetEnum(vec![spanned(Expr::Int(
            BigInt::from(1),
        ))]))],
    ));
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(seq_domain)),
        pattern: None,
    }];
    let body = spanned(Expr::In(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::ActionPred { expr, .. } = live else {
        panic!("Expected ActionPred");
    };
    assert!(matches!(&expr.node, Expr::Exists(_, _)));
}

/// Regression test for #1707: bounded-quantifier fallback through predicate_by_level
/// must apply resolve_action_expr on action-level predicates, inlining operator bodies.
/// Without the fix, the operator reference remains as Expr::Ident("Act", NameId::INVALID) and later
/// evaluation fails with "Undefined variable" when the original context is gone.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1707_bounded_quantifier_action_fallback_resolves_operator() {
    use tla_core::ast::OperatorDef;

    let conv = AstToLive::new();
    let mut ctx = EvalCtx::new();
    ctx.register_var("y");

    // Define Act == y' = 1 (action-level zero-arg operator)
    let op_body = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let op_def = OperatorDef {
        name: spanned("Act".to_string()),
        params: Vec::new(),
        body: op_body,
        local: false,
        contains_prime: true,
        guards_depend_on_prime: true,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("Act".to_string(), Arc::new(op_def));

    // \E x \in Seq({1}): Act
    // Non-enumerable domain forces fallback to predicate_by_level.
    // Body is action-level (Act contains y'), so predicate_by_level
    // should route to the Action arm and call resolve_action_expr.
    let seq_domain = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Seq".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::SetEnum(vec![spanned(Expr::Int(
            BigInt::from(1),
        ))]))],
    ));
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(seq_domain)),
        pattern: None,
    }];
    let body = spanned(Expr::Ident(
        "Act".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::ActionPred { expr: result, .. } = live else {
        panic!("Expected ActionPred, got {:?}", live);
    };

    // The operator should have been inlined by resolve_action_expr.
    // Without the #1707 fix, this would be Expr::Exists(_, Ident("Act")).
    // With the fix, the body should contain the resolved Eq(Prime(y), 1).
    match &result.node {
        Expr::Exists(_, body) => {
            assert!(
                matches!(&body.node, Expr::Eq(_, _)),
                "Expected resolved Eq body (y' = 1), got {:?}",
                body.node
            );
        }
        other => panic!("Expected Exists with resolved body, got {:?}", other),
    }
}
