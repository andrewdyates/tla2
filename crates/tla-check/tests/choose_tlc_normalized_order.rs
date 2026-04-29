// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use num_bigint::BigInt;
use tla_check::{eval, EvalCtx, Value};
use tla_core::ast::{BoundVar, Expr};
use tla_core::Spanned;

fn int_expr(n: i64) -> Spanned<Expr> {
    Spanned::dummy(Expr::Int(BigInt::from(n)))
}

fn bool_expr(b: bool) -> Spanned<Expr> {
    Spanned::dummy(Expr::Bool(b))
}

fn tuple_expr(elems: Vec<Spanned<Expr>>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Tuple(elems))
}

fn set_expr(elems: Vec<Spanned<Expr>>) -> Spanned<Expr> {
    Spanned::dummy(Expr::SetEnum(elems))
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn choose_over_set_prefers_shorter_tuple_in_tlc_normalized_order() {
    // TLC tuple ordering is length-first, then element-wise. This is parity-critical for CHOOSE
    // (first satisfying witness) when the CHOOSE domain is an extensional set.
    //
    // Part of #980.
    let ctx = EvalCtx::new();

    let domain = set_expr(vec![
        tuple_expr(vec![int_expr(1)]),
        tuple_expr(vec![int_expr(0), int_expr(5)]),
    ]);

    let bv = BoundVar {
        name: Spanned::dummy("t".to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    };

    let choose_expr = Spanned::dummy(Expr::Choose(bv, Box::new(bool_expr(true))));
    let v = eval(&ctx, &choose_expr).expect("eval CHOOSE");
    assert_eq!(v, Value::tuple([Value::SmallInt(1)]));
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn choose_over_set_prefers_smaller_cardinality_set_in_tlc_normalized_order() {
    // TLC set ordering is cardinality-first, then element-wise in normalized order.
    //
    // Part of #980.
    let ctx = EvalCtx::new();

    let domain = set_expr(vec![
        set_expr(vec![int_expr(1), int_expr(2)]),
        set_expr(vec![int_expr(3)]),
    ]);

    let bv = BoundVar {
        name: Spanned::dummy("s".to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    };

    let choose_expr = Spanned::dummy(Expr::Choose(bv, Box::new(bool_expr(true))));
    let v = eval(&ctx, &choose_expr).expect("eval CHOOSE");
    assert_eq!(v, Value::set([Value::SmallInt(3)]));
}
