// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for current-target leaf reification (#3166).

use super::*;
use crate::eval::OpEnv;
use tla_core::ast::{ModuleTarget, OperatorDef, Substitution};

fn ident(name: &str) -> Spanned<Expr> {
    spanned(Expr::Ident(
        name.to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))
}

fn zero_arg_operator(name: &str, body: Expr, contains_prime: bool) -> Arc<OperatorDef> {
    Arc::new(OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body: Spanned::dummy(body),
        local: false,
        contains_prime,
        guards_depend_on_prime: contains_prime,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    })
}

fn current_target() -> Arc<ModuleTarget> {
    Arc::new(ModuleTarget::Named("Inner".to_string()))
}

fn token_pos_expr() -> Spanned<Expr> {
    spanned(Expr::RecordAccess(
        Box::new(ident("inst_token")),
        Spanned::dummy("pos".to_string()).into(),
    ))
}

fn current_target_ctx() -> EvalCtx {
    let mut ctx = EvalCtx::new();
    Arc::make_mut(ctx.shared_arc_mut()).ops.insert(
        "outer_token".to_string(),
        zero_arg_operator(
            "outer_token",
            Expr::Record(vec![
                (
                    Spanned::dummy("pos".to_string()),
                    spanned(Expr::Int(BigInt::from(1))),
                ),
                (
                    Spanned::dummy("q".to_string()),
                    spanned(Expr::Int(BigInt::from(0))),
                ),
                (
                    Spanned::dummy("color".to_string()),
                    spanned(Expr::String("black".to_string())),
                ),
            ]),
            false,
        ),
    );

    let mut local_ops = OpEnv::new();
    local_ops.insert(
        "vars".to_string(),
        zero_arg_operator(
            "vars",
            Expr::Tuple(vec![spanned(Expr::RecordAccess(
                Box::new(ident("inst_token")),
                Spanned::dummy("pos".to_string()).into(),
            ))]),
            false,
        ),
    );

    ctx.with_local_ops(local_ops)
        .with_instance_substitutions(vec![Substitution {
            from: Spanned::dummy("inst_token".to_string()),
            to: ident("outer_token"),
        }])
}

fn current_target_ctx_without_local_ops() -> EvalCtx {
    let mut ctx = EvalCtx::new();
    Arc::make_mut(ctx.shared_arc_mut()).ops.insert(
        "outer_token".to_string(),
        zero_arg_operator(
            "outer_token",
            Expr::Record(vec![
                (
                    Spanned::dummy("pos".to_string()),
                    spanned(Expr::Int(BigInt::from(1))),
                ),
                (
                    Spanned::dummy("q".to_string()),
                    spanned(Expr::Int(BigInt::from(0))),
                ),
                (
                    Spanned::dummy("color".to_string()),
                    spanned(Expr::String("black".to_string())),
                ),
            ]),
            false,
        ),
    );

    ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("inst_token".to_string()),
        to: ident("outer_token"),
    }])
}

fn current_target_substituted_local_op_ctx() -> EvalCtx {
    let mut local_ops = OpEnv::new();
    local_ops.insert(
        "inner_alias".to_string(),
        zero_arg_operator("inner_alias", Expr::Bool(true), false),
    );

    EvalCtx::new()
        .with_local_ops(local_ops)
        .with_instance_substitutions(vec![Substitution {
            from: Spanned::dummy("inst_alias".to_string()),
            to: ident("inner_alias"),
        }])
}

fn assert_no_unresolved_inst_token(expr: &Spanned<Expr>, label: &str) {
    assert!(
        !AstToLive::expr_references_name(&expr.node, "inst_token"),
        "{label} should not retain raw Ident(\"inst_token\") after current-target reification: {:?}",
        expr.node
    );
}

fn collect_subscripts(expr: &LiveExpr, subscripts: &mut Vec<Arc<Spanned<Expr>>>) {
    match expr {
        LiveExpr::Enabled { subscript, .. } | LiveExpr::StateChanged { subscript, .. } => {
            if let Some(subscript) = subscript {
                subscripts.push(Arc::clone(subscript));
            }
        }
        LiveExpr::Not(inner)
        | LiveExpr::Always(inner)
        | LiveExpr::Eventually(inner)
        | LiveExpr::Next(inner) => collect_subscripts(inner, subscripts),
        LiveExpr::And(exprs) | LiveExpr::Or(exprs) => {
            for expr in exprs {
                collect_subscripts(expr, subscripts);
            }
        }
        LiveExpr::Bool(_) | LiveExpr::StatePred { .. } | LiveExpr::ActionPred { .. } => {}
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_current_target_action_pred_reifies_instance_substitution() {
    let conv = AstToLive::new();
    let ctx = current_target_ctx();
    let _guard = conv.push_target(current_target());

    let expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(token_pos_expr())))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));

    let live = conv
        .convert(&ctx, &expr)
        .expect("action-level current-target expression should convert");
    let LiveExpr::ActionPred { expr, .. } = live else {
        panic!("expected ActionPred, got {live:?}");
    };

    assert_no_unresolved_inst_token(&expr, "ActionPred leaf");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_current_target_state_pred_reifies_instance_substitution() {
    let conv = AstToLive::new();
    let ctx = current_target_ctx();
    let _guard = conv.push_target(current_target());

    let expr = spanned(Expr::Eq(
        Box::new(token_pos_expr()),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));

    let live = conv
        .convert(&ctx, &expr)
        .expect("state-level current-target expression should convert");
    let LiveExpr::StatePred { expr, .. } = live else {
        panic!("expected StatePred, got {live:?}");
    };

    assert_no_unresolved_inst_token(&expr, "StatePred leaf");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_current_target_state_pred_reifies_instance_substitution_without_local_ops() {
    let conv = AstToLive::new();
    let ctx = current_target_ctx_without_local_ops();
    let _guard = conv.push_target(current_target());

    let expr = spanned(Expr::Eq(
        Box::new(token_pos_expr()),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));

    let live = conv
        .convert(&ctx, &expr)
        .expect("state-level current-target expression should convert without local ops");
    let LiveExpr::StatePred { expr, .. } = live else {
        panic!("expected StatePred, got {live:?}");
    };

    assert_no_unresolved_inst_token(&expr, "StatePred leaf without local ops");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_current_target_state_pred_qualifies_substitution_rhs_local_op() {
    let conv = AstToLive::new();
    let ctx = current_target_substituted_local_op_ctx();
    let _guard = conv.push_target(current_target());

    let expr = spanned(Expr::Eq(
        Box::new(ident("inst_alias")),
        Box::new(spanned(Expr::Bool(true))),
    ));

    let live = conv
        .convert(&ctx, &expr)
        .expect("state-level current-target expression should convert");
    let LiveExpr::StatePred { expr, .. } = live else {
        panic!("expected StatePred, got {live:?}");
    };

    let Expr::Eq(lhs, _) = &expr.node else {
        panic!(
            "expected Eq after substitution qualification, got {:?}",
            expr.node
        );
    };
    match &lhs.node {
        Expr::ModuleRef(ModuleTarget::Named(target), name, args) => {
            assert_eq!(target, "Inner");
            assert_eq!(name, "inner_alias");
            assert!(
                args.is_empty(),
                "zero-arg substitution RHS should stay a zero-arg ModuleRef: {:?}",
                lhs.node
            );
        }
        other => {
            panic!("expected substitution RHS local op to qualify to ModuleRef, got {other:?}")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_current_target_wf_simple_ident_subscript_preserves_boundary() {
    let conv = AstToLive::new();
    let ctx = current_target_ctx();
    let _guard = conv.push_target(current_target());

    let wf_expr = spanned(Expr::WeakFair(
        Box::new(ident("vars")),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Prime(Box::new(token_pos_expr())))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
    ));

    let live = conv
        .convert(&ctx, &wf_expr)
        .expect("WF current-target expression should convert");

    let mut subscripts = Vec::new();
    collect_subscripts(&live, &mut subscripts);
    assert!(
        !subscripts.is_empty(),
        "WF conversion should produce subscript-bearing leaves"
    );

    for subscript in subscripts {
        assert_no_unresolved_inst_token(&subscript, "WF subscript leaf");
        match &subscript.node {
            Expr::ModuleRef(ModuleTarget::Named(target), name, args) => {
                assert_eq!(target, "Inner");
                assert_eq!(name, "vars");
                assert!(
                    args.is_empty(),
                    "simple fairness subscript should not gain arguments: {:?}",
                    subscript.node
                );
            }
            other => panic!("expected WF subscript to stay a ModuleRef boundary, got {other:?}"),
        }
    }
}
