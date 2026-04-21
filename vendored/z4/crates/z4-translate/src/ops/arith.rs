// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic operations.

use std::hash::Hash;

use z4_dpll::api::Term;

use super::expect_result;
use crate::TranslationHost;

/// Arithmetic binary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IntDiv,
    Mod,
}

/// Arithmetic unary operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Abs,
}

/// Binary arithmetic operation.
pub fn binop<V>(ctx: &mut impl TranslationHost<V>, op: BinOp, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    match op {
        BinOp::Add => expect_result(ctx.solver().try_add(a, b), "arith.add"),
        BinOp::Sub => expect_result(ctx.solver().try_sub(a, b), "arith.sub"),
        BinOp::Mul => expect_result(ctx.solver().try_mul(a, b), "arith.mul"),
        BinOp::Div => expect_result(ctx.solver().try_div(a, b), "arith.div"),
        BinOp::IntDiv => expect_result(ctx.solver().try_int_div(a, b), "arith.int_div"),
        BinOp::Mod => expect_result(ctx.solver().try_modulo(a, b), "arith.modulo"),
    }
}

/// Unary arithmetic operation.
pub fn unary<V>(ctx: &mut impl TranslationHost<V>, op: UnaryOp, a: Term) -> Term
where
    V: Eq + Hash,
{
    match op {
        UnaryOp::Neg => expect_result(ctx.solver().try_neg(a), "arith.neg"),
        UnaryOp::Abs => expect_result(ctx.solver().try_abs(a), "arith.abs"),
    }
}

/// Addition.
pub fn add<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Add, a, b)
}

/// Subtraction.
pub fn sub<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Sub, a, b)
}

/// Multiplication.
pub fn mul<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Mul, a, b)
}

/// Division (real).
pub fn div<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Div, a, b)
}

/// Integer division.
pub fn int_div<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::IntDiv, a, b)
}

/// Modulo.
pub fn modulo<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    binop(ctx, BinOp::Mod, a, b)
}

/// Negation.
pub fn neg<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    unary(ctx, UnaryOp::Neg, a)
}

/// Absolute value.
pub fn abs<V>(ctx: &mut impl TranslationHost<V>, a: Term) -> Term
where
    V: Eq + Hash,
{
    unary(ctx, UnaryOp::Abs, a)
}

/// Minimum of two terms.
pub fn min<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_min(a, b), "arith.min")
}

/// Maximum of two terms.
pub fn max<V>(ctx: &mut impl TranslationHost<V>, a: Term, b: Term) -> Term
where
    V: Eq + Hash,
{
    expect_result(ctx.solver().try_max(a, b), "arith.max")
}
