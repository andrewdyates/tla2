// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_weak_fairness() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // WF_x(A) where A is x' = x + 1
    let action = spanned(Expr::Eq(
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
    ));
    let wf = spanned(Expr::WeakFair(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(action),
    ));

    // Should successfully convert to LiveExpr
    let result = conv.convert(&ctx, &wf);
    assert!(result.is_ok(), "WeakFair conversion failed: {:?}", result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_strong_fairness() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // SF_x(A) where A is x' = x + 1
    let action = spanned(Expr::Eq(
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
    ));
    let sf = spanned(Expr::StrongFair(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(action),
    ));

    // Should successfully convert to LiveExpr
    let result = conv.convert(&ctx, &sf);
    assert!(result.is_ok(), "StrongFair conversion failed: {:?}", result);
}

fn assert_parsed_tuple_fairness_converts(op_name: &str) {
    let conv = AstToLive::new();
    let ctx = make_ctx();
    let expr = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            op_name.to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::Bool(true))],
    ));

    let live = conv
        .convert(&ctx, &expr)
        .expect("parsed fused fairness with tuple subscript should convert");

    match live {
        LiveExpr::Always(_) | LiveExpr::Or(_) => {}
        other => panic!("expected fairness expansion shape, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_parsed_weak_fairness_tuple_subscript() {
    assert_parsed_tuple_fairness_converts("WF_<<x, y>>");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_parsed_strong_fairness_tuple_subscript() {
    assert_parsed_tuple_fairness_converts("SF_<<x, y>>");
}
