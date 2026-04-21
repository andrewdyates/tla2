// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared test helpers for liveness checker tests.

use crate::liveness::test_helpers::spanned;
use crate::liveness::LiveExpr;
use std::sync::Arc;
use tla_core::ast::Expr;

pub(super) fn state_pred_x_eq(n: i64, tag: u32) -> LiveExpr {
    LiveExpr::state_pred(
        Arc::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(n.into()))),
        ))),
        tag,
    )
}

pub(super) fn action_pred_xprime_eq_x(tag: u32) -> LiveExpr {
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    LiveExpr::action_pred(
        Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x)))),
        tag,
    )
}

pub(super) fn action_pred_xprime_eq_x_plus_1(tag: u32) -> LiveExpr {
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = spanned(Expr::Add(
        Box::new(x),
        Box::new(spanned(Expr::Int(1.into()))),
    ));
    LiveExpr::action_pred(
        Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x_plus_1)))),
        tag,
    )
}
