// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::span::Span;
use num_bigint::BigInt;
use std::collections::HashMap;

mod capture_avoidance_tests;
mod identity_fold_tests;
mod regression_tests;
mod substitute_expr_tests;
mod substitution_fold_tests;

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned {
        node,
        span: Span::dummy(),
    }
}

fn boxed_expr(e: Expr) -> Box<Spanned<Expr>> {
    Box::new(spanned(e))
}

fn assert_expr_eq(a: &Expr, b: &Expr) -> bool {
    a == b
}
