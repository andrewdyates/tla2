// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared test helpers for ast_to_live tests.

use crate::eval::EvalCtx;
use num_bigint::BigInt;
use tla_core::ast::Expr;

pub(super) fn make_ctx() -> EvalCtx {
    EvalCtx::new()
}

pub(super) fn assert_expr_range_int_bounds(expr: Expr, low: BigInt, high: BigInt) {
    match expr {
        Expr::Range(a, b) => {
            let Expr::Int(a_int) = a.node else {
                panic!("Expected Range low bound Int");
            };
            let Expr::Int(b_int) = b.node else {
                panic!("Expected Range high bound Int");
            };
            assert_eq!(a_int, low);
            assert_eq!(b_int, high);
        }
        _ => panic!("Expected Range"),
    }
}
